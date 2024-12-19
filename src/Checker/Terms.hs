module Checker.Terms where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Error.Class
import Control.Monad.Reader.Class

import Checker.Types
import Checker.Unify
import Checker.Monad
import Syntax

expectT :: Term -> Ty -> Ty -> CheckM TyEqu
expectT m actual expected =
  do trace ("expect (" ++ show actual ++ ") (" ++ show expected ++ ")")
     b <- unify actual expected
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

checkTerm' :: Bool -> Term -> Ty -> CheckM Term
checkTerm' implicitTyLams e t = checkTerm implicitTyLams e =<< flattenT t

lookupVar :: Int -> CheckM Ty
lookupVar i = asks (lookupV i . tctxt)

inst :: Term -> Ty -> Ty -> CheckM Term
inst e actual@(TForall {}) expected@(TForall {}) = -- Could have a little finer resolution here: suppose the actual type has *more* quantifiers than the expected type?
    flip wrap e <$> expectT e actual expected
inst e (TForall x k t) expected =
  do u <- typeGoal' "t" k
     t' <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 1 u) t
     inst (ETyApp e u) t' expected
inst e (TThen p t) expected =
  do vr <- newRef Nothing
     p' <- flattenP p 
     trace ("instantiating " ++ show e ++ " requiring " ++ show p')
     require p vr
     inst (EPrApp e (VGoal (Goal ("v", vr)))) t expected
inst e t expected = flip wrap e <$> expectT e t expected

checkTerm :: Bool -> Term -> Ty -> CheckM Term
checkTerm implicitTyLams m t = 
  do g <- asks tctxt
     trace $ "checkTerm (" ++ show m ++ ") (" ++ show t ++ ") in (" ++ show g ++ ")"
     checkTerm0 implicitTyLams m t

checkTerm0 :: Bool -> Term -> Ty -> CheckM Term
checkTerm0 implicitTyLams e0@(ETyLam v k e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TForall v k tcod) expected
     wrap q . ETyLam v k <$> bindTy k (checkTerm' implicitTyLams e tcod) -- is this the right call for implicits? maybe once you've gone explicit, you should have to stay explicit....?
checkTerm0 True e (TForall v k t) =
  ETyLam v k <$> bindTy k (checkTerm True e t)
checkTerm0 implicitTyLams e0@(EPrLam p e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TThen p tcod) expected
     wrap q . EPrLam p <$> assume p (checkTerm' implicitTyLams e tcod)
checkTerm0 implicitTyLams e (TThen p t) =
  EPrLam p <$> assume p (checkTerm implicitTyLams e t)
checkTerm0 implicitTyLams (EVar (-1) x) expected =   
  throwError (ErrOther $ "scoping error: variable " ++ x ++ " not resolved")
checkTerm0 implicitTyLams e@(EVar i v) expected = flip (inst (EVar i v)) expected =<< flattenT =<< lookupVar i -- . unshift =<< lookupVar i
checkTerm0 implicitTyLams e0@(ELam v t e) expected =
  do tcod <- typeGoal "cod"
     t' <- fst <$> (normalize' =<< checkTy' e0 t KType)
     q <- expectT e0 (funTy t' tcod) expected
     wrap q . ELam v t' <$> bind t' (checkTerm' implicitTyLams  e tcod)
checkTerm0 implicitTyLams e0@(EApp f e) expected =
  do tdom <- typeGoal "dom"
     EApp <$>
       checkTerm implicitTyLams f (funTy tdom expected) <*>
       checkTerm' implicitTyLams  e tdom
checkTerm0 implicitTyLams e0@(ETyApp e t) expected
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
       e' <- checkTerm implicitTyLams e et
       et' <- flattenT et
       case et' of
         TForall x k u ->
           do u' <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 1 t) u
              q <- expectT e0 u' expected
              return (wrap q (ETyApp e' t))
         _ -> fail $ "in " ++ show e0 ++ ": expected " ++ show et' ++ " to be a quantified type"
checkTerm0 implicitTyLams e0@(EPrApp e p) expected =
  fail "unimplemented"
checkTerm0 implicitTyLams e0@(ESing t) expected =
  do q <- expectT e0 (TSing t) expected
     wrap q . ESing <$> checkTy' e0 t KLabel
checkTerm0 implicitTyLams e0@(ELabel el e) expected =
  do tl <- typeGoal' "l" KLabel
     t <- typeGoal "t"
     q <- expectT e0 (TLabeled tl t) expected
     wrap q <$>
       (ELabel <$> checkTerm' implicitTyLams  el (TSing tl) <*> checkTerm' implicitTyLams  e t)
checkTerm0 implicitTyLams e0@(EUnlabel e el) expected =
  do tl <- typeGoal' "l" KLabel
     el' <- checkTerm implicitTyLams el (TSing tl)
     e' <- checkTerm' implicitTyLams  e (TLabeled tl expected)
     return (EUnlabel e' el')
checkTerm0 implicitTyLams e0@(EPrj y z v@(VGoal (Goal (_, r))) e) expected =
  do y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TPi y') expected
     e' <- checkTerm implicitTyLams e (TPi z')
     require (PLeq y' z') r
     return (wrap q (EPrj y' z' v e'))  -- but let's go ahead and flatten this term...
checkTerm0 implicitTyLams (EPrj {}) _ =
  fail "unimplemented: prj with non-goal evidence"
checkTerm0 implicitTyLams e0@(EConcat x y z v@(VGoal (Goal (_, r))) m n) expected =
  do x' <- checkTy x (KRow (kindOf expected))
     y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TPi z') expected
     m' <- checkTerm implicitTyLams m (TPi x')
     n' <- checkTerm implicitTyLams n (TPi y')
     require (PPlus x' y' z') r
     return (wrap q (EConcat x' y' z' v m' n'))
checkTerm0 implicitTyLams (EConcat {}) _ =
  fail "unimplemented: ++ with non-goal evidence"
checkTerm0 implicitTyLams e0@(EInj y z v@(VGoal (Goal (_, r))) e) expected =
  do y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TSigma z') expected
     e' <- checkTerm implicitTyLams e (TSigma y')
     require (PLeq y' z') r
     return (wrap q (EPrj y' z' v e'))  -- but let's go ahead and flatten this term...
checkTerm0 implicitTyLams (EInj {}) _ =
  fail "unimplemented: inj with non-goal evidence"
checkTerm0 implicitTyLams e0@(EBranch x y z v@(VGoal (Goal (_, r))) m n) expected =
  do x' <- checkTy x (KRow (kindOf expected))
     y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     t <- typeGoal "t"
     q <- expectT e0 (funTy (TSigma z') t) expected
     t' <- flattenT t
     m' <- checkTerm implicitTyLams m (funTy (TSigma x') t')
     n' <- checkTerm implicitTyLams n (funTy (TSigma y') t')
     require (PPlus x' y' z') r
     return (wrap q (EBranch x' y' z' v m' n'))
checkTerm0 implicitTyLams (EBranch {}) _ =
  fail "unimplemented: ++ with non-goal evidence"
checkTerm0 implicitTyLams e0@(EAna phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     t <- typeGoal "t"
     q <- expectT e0 (TSigma (TApp (TMapFun phi') r) `funTy` t) expected
     EAna phi' <$> checkTerm implicitTyLams e (TForall "l" KLabel $ TForall "u" k $ TForall "y1" (KRow k) $ TForall "z" (KRow k) $ TForall "y2" (KRow k) $
                                PPlus (TVar 2 "y1" (Just (KRow k))) (TRow [TLabeled (TVar 4 "l" (Just KLabel)) (TVar 3 "u" (Just k))]) (TVar 1 "z" (Just (KRow k))) `TThen`
                                PPlus (TVar 1 "z" (Just (KRow k))) (TVar 0 "y2" (Just (KRow k))) (shiftTN 0 5 r) `TThen`
                                TSing (TVar 4 "l" (Just KLabel)) `funTy` TApp (shiftTN 0 5 phi') (TVar 3 "u" (Just k)) `funTy` shiftTN 0 5 t)
checkTerm0 implicitTyLams e0@(ESyn phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     q <- expectT e0 (TPi (TApp (TMapFun phi') r)) expected
     ESyn phi' <$> checkTerm implicitTyLams e (TForall "l" KLabel $ TForall "u" k $ TForall "y1" (KRow k) $ TForall "z" (KRow k) $ TForall "y2" (KRow k) $
                                PPlus (TVar 2 "y1" (Just (KRow k))) (TRow [TLabeled (TVar 4 "l" (Just KLabel)) (TVar 3 "u" (Just k))]) (TVar 1 "z" (Just (KRow k))) `TThen`
                                PPlus (TVar 1 "z" (Just (KRow k))) (TVar 0 "y2" (Just (KRow k))) r `TThen`
                                TSing (TVar 4 "l" (Just KLabel)) `funTy` TApp (shiftTN 0 4 phi') (TVar 3 "u" (Just k)))
checkTerm0 implicitTyLams e0@(ETyped e t) expected =
  do (t', _) <- normalize =<< checkTy' e0 t KType
     e' <- checkTerm False e t'  -- any reason to preserve the type ascription?
     inst e0 t' expected
     


checkTop :: Term -> Ty -> CheckM Term
checkTop m t = 
  do (t', q) <- normalize' t
     m' <- checkTerm True m t'
     return (case q of
               QRefl -> m'
               _ -> ETyEqu m' q)
       