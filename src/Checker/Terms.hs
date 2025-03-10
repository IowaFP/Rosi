module Checker.Terms where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Error.Class
import Control.Monad.Reader.Class

import Checker.Types
import Checker.Unify
import Checker.Monad
import Syntax

expectT :: Term -> Ty -> Ty -> CheckM Evid
expectT m actual expected =
  do trace ("expect (" ++ show actual ++ ") (" ++ show expected ++ ")")
     b <- unify actual expected
     case b of
       Nothing -> typeMismatch m actual expected
       Just q  -> flattenV q


typeMismatch :: Term -> Ty -> Ty -> CheckM a
typeMismatch m actual expected =
  do actual' <- flattenT actual
     expected' <- flattenT expected
     throwError (ErrTypeMismatch m actual' expected')

wrap :: Evid -> Term -> Term
wrap VRefl t = t
wrap q t     = ECast t q

checkTerm' :: Bool -> Term -> Ty -> CheckM Term
checkTerm' implicitTyLams e t = checkTerm implicitTyLams e =<< flattenT t

lookupVar :: Int -> CheckM Ty
lookupVar i = asks (lookupV i . tctxt)

checkTerm :: Bool -> Term -> Ty -> CheckM Term
checkTerm implicitTyLams m t =
  do g <- asks tctxt
     trace $ "checkTerm (" ++ show m ++ ") (" ++ show t ++ ") in (" ++ show g ++ ")"
     checkTerm0 implicitTyLams m t

elimForm :: Ty -> (Ty -> CheckM Term) -> CheckM Term
elimForm expected@(TInst {}) k =
  k expected
elimForm expected k =
  do iv <- newRef Nothing
     name <- fresh "i"
     flip EInst (Unknown (Goal (name, iv))) <$> k (TInst (Unknown (Goal (name, iv))) expected)

checkTerm0 :: Bool -> Term -> Ty -> CheckM Term
checkTerm0 implicitTyLams (ETyLam v Nothing e) expected =
  do k <- kindGoal "d"
     checkTerm0 implicitTyLams (ETyLam v (Just k) e) expected
checkTerm0 implicitTyLams e0@(ETyLam v (Just k) e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TForall v (Just k) tcod) expected
     wrap q . ETyLam v (Just k) <$> bindTy k (checkTerm' implicitTyLams e tcod) -- is this the right call for implicits? maybe once you've gone explicit, you should have to stay explicit....?
checkTerm0 _ _ (TForall v Nothing t) =
  error "checkTerm: forall without kind"
checkTerm0 True e (TForall v (Just k) t) =
  ETyLam v (Just k) <$> bindTy k (checkTerm True (shiftEN 0 1 e) t)
checkTerm0 implicitTyLams e0@(EPrLam p e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TThen p tcod) expected
     wrap q . EPrLam p <$> assume p (checkTerm' implicitTyLams e tcod)
checkTerm0 implicitTyLams e (TThen p t) =
  EPrLam p <$> assume p (checkTerm implicitTyLams e t)
checkTerm0 implicitTyLams (EVar (-1) x) expected =
  throwError (ErrOther $ "scoping error: variable " ++ x ++ " not resolved")
checkTerm0 implicitTyLams e@(EVar i v) expected =
  do ir <- newRef Nothing
     t <- lookupVar i
     expectT e t (TInst (Unknown (Goal ("i", ir))) expected)
     return (EInst (EVar i v) (Unknown (Goal ("i", ir))))
checkTerm0 implicitTyLams (ELam v Nothing e) expected =
  do tdom <- typeGoal "dom"
     checkTerm0 implicitTyLams (ELam v (Just tdom) e) expected
checkTerm0 implicitTyLams e0@(ELam v (Just t) e) expected =
  do tcod <- typeGoal "cod"
     t' <- fst <$> (normalize' =<< checkTy' e0 t KType)
     q <- expectT e0 (funTy t' tcod) expected
     wrap q . ELam v (Just t') <$> bind t' (checkTerm' implicitTyLams  e tcod)
checkTerm0 implicitTyLams e0@(EApp f e) expected =
  do tdom <- typeGoal "dom"
     elimForm expected $ \expected ->
       EApp <$>
         checkTerm implicitTyLams f (funTy tdom expected) <*>
         checkTerm' implicitTyLams e tdom
-- Unknown instantiations should be *introduced* during type checking, so how are we trying to type check one...?
checkTerm0 implicitTyLams e0@(EInst e (Unknown ig)) expected =
  fail $ "in " ++ show e0 ++ ": unexpected instantiation hole in type checking"
checkTerm0 implicitTyLams e0@(EInst e is) expected =
  do is' <- checkInsts is
     elimForm expected $ \expected ->
       EInst <$> checkTerm implicitTyLams e (TInst is' expected) <*> pure is'
  where checkInsts :: Insts -> CheckM Insts
        checkInsts (Unknown _) = error "internal: why am I type checking an unknown instantiation?"
        checkInsts (Known is) = Known <$> mapM checkInst is
        checkInst :: Inst -> CheckM Inst
        checkInst (TyArg t) =
          do k <- kindGoal "k"
             t' <- checkTy' e0 t k
             return (TyArg t')
        checkInst (PrArg _) =
          error "internal: why am I type checking a predicate instantiation?"
checkTerm0 implicitTyLams e0@(ESing t) expected =
  do t' <- checkTy' e0 t =<< kindGoal "k"
     q <- expectT e0 (TSing t') expected
     return (wrap q (ESing t'))
checkTerm0 implicitTyLams e0@(ELabel el e) expected =
  do tl <- typeGoal' "l" KLabel
     t <- typeGoal "t"
     q <- expectT e0 (TLabeled tl t) expected
     wrap q <$>
       (ELabel <$> checkTerm' implicitTyLams  el (TSing tl) <*> checkTerm' implicitTyLams  e t)
checkTerm0 implicitTyLams e0@(EUnlabel e el) expected =
  do tl <- typeGoal' "l" KLabel
     el' <-checkTerm implicitTyLams el (TSing tl)
     elimForm expected $ \expected ->
       do e' <- checkTerm' implicitTyLams e (TLabeled tl expected)
          return (EUnlabel e' el')
checkTerm0 _ e@(EConst c) expected =
  do ir <- newRef Nothing
     t <- constType c
     expectT e t (TInst (Unknown (Goal ("i", ir))) expected)
     return (EInst e (Unknown (Goal ("i", ir))))
  where -- This is necessary because I don't yet support kind polymorphism, so I can't express the
        -- types of the constants directly
        constType CPrj =
          do k <- kindGoal "r"
             return (TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $
                       PLeq (TVar 1 "y" (Just (KRow k))) (TVar 0 "z" (Just (KRow k))) `TThen`
                         TPi (TVar 0 "z" (Just (KRow k))) `funTy` TPi (TVar 1 "y" (Just (KRow k))))
        constType CInj =
          do k <- kindGoal "r"
             return (TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $
                       PLeq (TVar 1 "y" (Just (KRow k))) (TVar 0 "z" (Just (KRow k))) `TThen`
                         TSigma (TVar 1 "y" (Just (KRow k))) `funTy` TSigma (TVar 0 "z" (Just (KRow k))))
        constType CConcat =
          do k <- kindGoal "r"
             let tvar 2 = TVar 2 "x" (Just (KRow k))
                 tvar 1 = TVar 1 "y" (Just (KRow k))
                 tvar 0 = TVar 0 "z" (Just (KRow k))
             return (TForall "x" (Just (KRow k)) $ TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $
                       PPlus (tvar 2) (tvar 1) (tvar 0) `TThen`
                         TPi (tvar 2) `funTy` TPi (tvar 1) `funTy` TPi (tvar 0))
        constType CBranch =
          do k <- kindGoal "r"
             let tvar 3 = TVar 3 "x" (Just (KRow k))
                 tvar 2 = TVar 2 "y" (Just (KRow k))
                 tvar 1 = TVar 1 "z" (Just (KRow k))
                 tvar 0 = TVar 0 "t" (Just KType)
             return (TForall "x" (Just (KRow k)) $ TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $ TForall "t" (Just KType) $
                       PPlus (tvar 3) (tvar 2) (tvar 1) `TThen`
                         (TSigma (tvar 3) `funTy` tvar 0) `funTy`
                         (TSigma (tvar 2) `funTy` tvar 0) `funTy`
                         (TSigma (tvar 1) `funTy` tvar 0))
        constType CIn =
          return (TForall "f" (Just (KType `KFun` KType)) $
                    f `TApp` TMu f `funTy` TMu f) where
          f = TVar 0 "f" (Just (KType `KFun` KType))
        constType COut =
          return (TForall "f" (Just (KType `KFun` KType)) $
                    TMu f `funTy` f `TApp` TMu f) where
          f = TVar 0 "f" (Just (KType `KFun` KType))
        constType CFix =
          return (TForall "a" (Just KType) $
                   (a `funTy` a) `funTy` a) where
          a = TVar 0 "a" (Just KType)
checkTerm0 implicitTyLams e0@(EAna phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     t <- typeGoal "t"
     elimForm expected $ \expected ->
       do q <- expectT e0 (TSigma (TApp (TMapFun phi') r) `funTy` t) expected
          EAna phi' <$> checkTerm implicitTyLams e (TForall "l" (Just KLabel) $ TForall "u" (Just k) $
                                                      PLeq (TRow [TLabeled (TVar 1 "l" (Just KLabel)) (TVar 0 "u" (Just k))]) (shiftTN 0 2 r) `TThen`
                                                      TSing (TVar 1 "l" (Just KLabel)) `funTy` TApp (shiftTN 0 2 phi') (TVar 0 "u" (Just k)) `funTy` shiftTN 0 2 t)
--           EAna phi' <$> checkTerm implicitTyLams e (TForall "l" (Just KLabel) $ TForall "u" (Just k) $ TForall "y1" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $ TForall "y2" (Just (KRow k)) $
--                                      PPlus (TVar 2 "y1" (Just (KRow k))) (TRow [TLabeled (TVar 4 "l" (Just KLabel)) (TVar 3 "u" (Just k))]) (TVar 1 "z" (Just (KRow k))) `TThen`
--                                      PPlus (TVar 1 "z" (Just (KRow k))) (TVar 0 "y2" (Just (KRow k))) (shiftTN 0 5 r) `TThen`
--                                      TSing (TVar 4 "l" (Just KLabel)) `funTy` TApp (shiftTN 0 5 phi') (TVar 3 "u" (Just k)) `funTy` shiftTN 0 5 t)
checkTerm0 implicitTyLams e0@(ESyn phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     q <- expectT e0 (TPi (TApp (TMapFun phi') r)) expected
     ESyn phi' <$> checkTerm implicitTyLams e (TForall "l" (Just KLabel) $ TForall "u" (Just k) $
                                                 PLeq (TRow [TLabeled (TVar 1 "l" (Just KLabel)) (TVar 0 "u" (Just k))]) (shiftTN 0 2 r) `TThen`
                                                 TSing (TVar 1 "l" (Just KLabel)) `funTy` TApp (shiftTN 0 2 phi') (TVar 0 "u" (Just k)))
--     ESyn phi' <$> checkTerm implicitTyLams e (TForall "l" (Just KLabel) $ TForall "u" (Just k) $ TForall "y1" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $ TForall "y2" (Just (KRow k)) $
--                                PPlus (TVar 2 "y1" (Just (KRow k))) (TRow [TLabeled (TVar 4 "l" (Just KLabel)) (TVar 3 "u" (Just k))]) (TVar 1 "z" (Just (KRow k))) `TThen`
--                                PPlus (TVar 1 "z" (Just (KRow k))) (TVar 0 "y2" (Just (KRow k))) (shiftTN 0 5 r) `TThen`
--                                TSing (TVar 4 "l" (Just KLabel)) `funTy` TApp (shiftTN 0 5 phi') (TVar 3 "u" (Just k)))
checkTerm0 implicitTyLams e0@(ETyped e t) expected =
  do (t', _) <- normalize =<< checkTy' e0 t KType
     e' <- checkTerm False e t'  -- any reason to preserve the type ascription?
     elimForm expected $ \expected ->
       do q <- expectT e0 t expected
          return (ECast e' q)

checkTop :: Term -> Ty -> CheckM Term
checkTop m t =
  do (t', q) <- normalize' t
     m' <- checkTerm True m t'
     return (case q of
               VRefl -> m'
               _ -> ECast m' q)
