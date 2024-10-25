module Checker.Terms where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Reader.Class

import Checker.Types
import Checker.Unify
import Checker.Monad
import Syntax

expectT :: Term -> Ty -> Ty -> CheckM TyEqu
expectT m actual expected =
  do b <- unify actual expected
     case b of
       Nothing -> typeMismatch m actual expected
       Just q  -> return q


typeMismatch :: Term -> Ty -> Ty -> CheckM a
typeMismatch m actual expected =
  do actual' <- flattenT actual
     expected' <- flattenT expected
     throwError (ErrTypeMismatch m actual' expected')

wrap :: TyEqu -> Term -> Term
wrap q t = case flattenQ q of
             QRefl -> t
             q'    -> ETyEqu t q'

checkTerm' :: Term -> Ty -> CheckM Term
checkTerm' e t = checkTerm e =<< flattenT t

lookupVar :: Int -> CheckM Ty
lookupVar i = asks ((!! i) . tctxt)

inst :: Term -> Ty -> Ty -> CheckM Term
inst e (TForall x k t) expected =
  do u <- typeGoal' "t" k
     t' <- subst 0 u t
     inst (ETyApp e u) t' expected
inst e (TThen p t) expected =
  do vr <- newRef Nothing
     require p vr
     inst (EPrApp e (VGoal (Goal ("v", vr)))) t expected
inst e t expected = flip wrap e <$> expectT e t expected

checkTerm :: Term -> Ty -> CheckM Term
checkTerm e0@(ETyLam v k e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TForall v k tcod) expected
     wrap q . ETyLam v k <$> bindTy k (checkTerm' e tcod)
checkTerm e (TForall v k t) =
  ETyLam v k <$> bindTy k (checkTerm e t)
checkTerm e0@(EPrLam p e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TThen p tcod) expected
     wrap q . EPrLam p <$> assume p (checkTerm' e tcod)
checkTerm e (TThen p t) =
  EPrLam p <$> assume p (checkTerm e t)
checkTerm (EVar (-1) x) expected =   
  throwError (ErrOther $ "scoping error: variable " ++ x ++ " not resolved")
checkTerm e@(EVar i v) expected = flip (inst (EVar i v)) expected =<< flattenT =<< lookupVar i
checkTerm e0@(ELam v t e) expected =
  do tcod <- typeGoal "cod"
     t' <- checkTy' e0 t KType
     q <- expectT e0 (funTy t' tcod) expected
     wrap q . ELam v t' <$> bind t' (checkTerm' e tcod)
checkTerm e0@(EApp f e) expected =
  do tdom <- typeGoal "dom"
     EApp <$>
       checkTerm f (funTy tdom expected) <*>
       checkTerm' e tdom
checkTerm e0@(ETyApp e t) expected
  | Just ((i, x), ts) <- insts e0 =
    do u <- flattenT =<< lookupVar i
       let (ks, actual) = quants u
       when (length ks < length ts) $
         fail $ "too many type arguments to " ++ x ++ " : " ++ show u
       ts' <- zipWithM (checkTy' e0) ts (snd <$> ks)
       actual' <- foldM (\u' (x, t) -> subst x t u') actual (zip (takeWhile (0 <=) (iterate (subtract 1) (length ts' - 1))) ts')
       inst (foldl ETyApp (EVar i x) ts')
            (foldr (uncurry TForall) actual' (drop (length ts) ks))
            expected
  | otherwise =
    -- Saddest of faces...
    do et <- typeGoal "t"
       e' <- checkTerm e et
       et' <- flattenT et
       case et' of
         TForall x k u ->
           do u' <- subst 0 t u
              q <- expectT e0 u' expected
              return (wrap q (ETyApp e' t))
         _ -> fail $ "in " ++ show e0 ++ ": expected " ++ show et' ++ " to be a quantified type"
checkTerm e0@(EPrApp e p) expected =
  fail "unimplemented"
checkTerm e0@(ESing t) expected =
  do q <- expectT e0 (TSing t) expected
     wrap q . ESing <$> checkTy' e0 t KLabel
checkTerm e0@(ELabel el e) expected =
  do tl <- typeGoal' "l" KLabel
     t <- typeGoal "t"
     q <- expectT e0 (TLabeled tl t) expected
     wrap q <$>
       (ELabel <$> checkTerm' el (TSing tl) <*> checkTerm' e t)
checkTerm e0@(EUnlabel e el) expected =
  do tl <- typeGoal' "l" KLabel
     el' <- checkTerm el (TSing tl)
     e' <- checkTerm' e (TLabeled tl expected)
     return (EUnlabel e' el')
checkTerm e0@(EPrj y z v@(VGoal (Goal (_, r))) e) expected =
  do y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TPi y') expected
     e' <- checkTerm e (TPi z')
     require (PLeq y' z') r
     return (wrap q (EPrj y' z' v e'))  -- but let's go ahead and flatten this term...
checkTerm (EPrj {}) _ =
  fail "unimplemented: prj with non-goal evidence"
checkTerm e0@(EConcat x y z v@(VGoal (Goal (_, r))) m n) expected =
  do x' <- checkTy x (KRow (kindOf expected))
     y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TPi z') expected
     m' <- checkTerm m (TPi x')
     n' <- checkTerm n (TPi y')
     require (PPlus x' y' z') r
     return (wrap q (EConcat x' y' z' v m' n'))
checkTerm (EConcat {}) _ =
  fail "unimplemented: ++ with non-goal evidence"
checkTerm e0@(EInj y z v@(VGoal (Goal (_, r))) e) expected =
  do y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TSigma z') expected
     e' <- checkTerm e (TSigma y')
     require (PLeq y' z') r
     return (wrap q (EPrj y' z' v e'))  -- but let's go ahead and flatten this term...
checkTerm (EInj {}) _ =
  fail "unimplemented: inj with non-goal evidence"
checkTerm e0@(EBranch x y z v@(VGoal (Goal (_, r))) m n) expected =
  do x' <- checkTy x (KRow (kindOf expected))
     y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     t <- typeGoal "t"
     q <- expectT e0 (funTy (TSigma z') t) expected
     t' <- flattenT t
     m' <- checkTerm m (funTy (TSigma x') t')
     n' <- checkTerm n (funTy (TSigma y') t')
     require (PPlus x' y' z') r
     return (wrap q (EBranch x' y' z' v m' n'))
checkTerm (EBranch {}) _ =
  fail "unimplemented: ++ with non-goal evidence"
checkTerm e0@(EAna phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     t <- typeGoal "t"
     q <- expectT e0 (TSigma (TApp (TMapFun phi') r) `funTy` t) expected
     EAna phi' <$> checkTerm e (TForall "l" KLabel $ TForall "u" k $ TForall "y1" (KRow k) $ TForall "z" (KRow k) $ TForall "y2" (KRow k) $
                                PPlus (TVar 2 "y1" (Just (KRow k))) (TRow [TLabeled (TVar 4 "l" (Just KLabel)) (TVar 3 "u" (Just k))]) (TVar 1 "z" (Just (KRow k))) `TThen`
                                PPlus (TVar 1 "z" (Just (KRow k))) (TVar 0 "y2" (Just (KRow k))) r `TThen`
                                TSing (TVar 4 "l" (Just KLabel)) `funTy` TApp phi' (TVar 3 "u" (Just k)) `funTy` t)
checkTerm e0@(ESyn phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     q <- expectT e0 (TPi (TApp (TMapFun phi') r)) expected
     ESyn phi' <$> checkTerm e (TForall "l" KLabel $ TForall "u" k $ TForall "y1" (KRow k) $ TForall "z" (KRow k) $ TForall "y2" (KRow k) $
                                PPlus (TVar 2 "y1" (Just (KRow k))) (TRow [TLabeled (TVar 4 "l" (Just KLabel)) (TVar 3 "u" (Just k))]) (TVar 1 "z" (Just (KRow k))) `TThen`
                                PPlus (TVar 1 "z" (Just (KRow k))) (TVar 0 "y2" (Just (KRow k))) r `TThen`
                                TSing (TVar 4 "l" (Just KLabel)) `funTy` TApp phi' (TVar 3 "u" (Just k)))
