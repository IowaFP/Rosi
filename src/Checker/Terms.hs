module Checker.Terms where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Data.Generics (everywhereM, mkM)
import Data.IORef
import Data.List (intercalate)

import Checker.Types hiding (trace)
import Checker.Unify
import Checker.Normalize
import Checker.Monad
import Checker.Preds
import Printer
import Syntax


expectT :: Term -> Ty -> Ty -> CheckM Evid
expectT m actual expected =
  do trace ("expect (" ++ renderString False (ppr actual) ++ ") (" ++ renderString False (ppr expected) ++ ")")
     b <- typeErrorContext (ErrContextTerm m . ErrContextTyEq actual expected) $ unify [] actual expected
     case b of
       Left (actual', expected') -> typeMismatch m actual expected actual' expected'
       Right q  -> flattenV q

typeMismatch :: Term -> Ty -> Ty -> Ty -> Ty -> CheckM a
typeMismatch m actual expected actual' expected' =
  do [actual0, expected0, actual'0, expected'0] <- mapM flattenT [actual, expected, actual', expected']
     typeError (ErrContextTerm m $ ErrTypeMismatch actual0 expected0 actual'0 expected'0)

wrap :: Evid -> Term -> Term
wrap VEqRefl t = t
wrap q t       = ECast t q

checkTerm' :: Term -> Ty -> CheckM Term
checkTerm' e t = checkTerm e =<< flattenT t

lookupVar :: Int -> CheckM Ty
lookupVar i = asks (lookupV i . tctxt)

checkTerm :: Term -> Ty -> CheckM Term
checkTerm m t =
  do g <- asks tctxt
     l <- theLevel
     trace $ "checkTerm@" ++ show l ++ " (" ++ renderString False (ppr m) ++ ") (" ++ renderString False (ppr t) ++ ") in (" ++ intercalate "," (map (renderString False . ppr) g) ++ ")"
     typeErrorContext (ErrContextTerm m) $ checkTerm0 m t

elimForm :: Ty -> (Ty -> CheckM Term) -> CheckM Term
elimForm expected k =
  do iv <- newRef Nothing
     name <- fresh "i"
     flip EInst (Unknown 0 (Goal (name, iv))) <$> k (TInst (Unknown 0 (Goal (name, iv))) expected)

checkTerm0 :: Term -> Ty -> CheckM Term
checkTerm0 (ETyLam v Nothing e) expected =
  do k <- kindGoal "d"
     checkTerm (ETyLam v (Just k) e) expected
checkTerm0 e0@(ETyLam v (Just k) e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TForall v (Just k) tcod) expected
     wrap q . ETyLam v (Just k) <$>
       (upLevel $
        bindTy k $
          checkTerm' e tcod)
checkTerm0 _ (TForall v Nothing t) =
  error "checkTerm: forall without kind"
checkTerm0 e (TForall v (Just k) t) =
  ETyLam v (Just k) <$>
    (upLevel $
     bindTy k $
       checkTerm (shiftEN 0 1 e) t)
checkTerm0 e0@(EPrLam p e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TThen p tcod) expected
     wrap q . EPrLam p <$> assume p (checkTerm' e tcod)
checkTerm0 e (TThen p t) =
  EPrLam p <$> assume p (checkTerm e t)
checkTerm0 (EVar (-1) x) expected =
  typeError (ErrOther $ "scoping error: variable " ++ x ++ " not resolved")
checkTerm0 e@(EVar i v) expected =
  do t <- lookupVar i
     elimForm expected $ \ expected ->
       do q <- expectT e t expected
          return (wrap q (EVar i v))
checkTerm0 (ELam v Nothing e) expected =
  do tdom <- typeGoal "dom"
     checkTerm0 (ELam v (Just tdom) e) expected
checkTerm0 e0@(ELam v (Just t) e) expected =
  do tcod <- typeGoal "cod"
     t' <- fst <$> (normalize' [] =<< checkTy' e0 t KType)
     q <- expectT e0 (funTy t' tcod) expected
     wrap q . ELam v (Just t') <$> bind t' (checkTerm'  e tcod)
checkTerm0 e0@(EApp f e) expected =
  do tdom <- typeGoal "dom"
     elimForm expected $ \expected ->
       EApp <$>
         checkTerm f (funTy tdom expected) <*>
         checkTerm' e tdom
-- Unknown instantiations should be *introduced* during type checking, so how are we trying to type check one...?
checkTerm0 e0@(EInst e (Unknown _ ig)) expected =
  fail $ "in " ++ show e0 ++ ": unexpected instantiation hole in type checking"
checkTerm0 e0@(EInst e is) expected =
  do is' <- checkInsts is
     elimForm expected $ \expected ->
       EInst <$> checkTerm e (TInst is' expected) <*> pure is'
  where checkInsts :: Insts -> CheckM Insts
        checkInsts (Unknown _ _) = error "internal: why am I type checking an unknown instantiation?"
        checkInsts (Known is) = Known <$> mapM checkInst is
        checkInst :: Inst -> CheckM Inst
        checkInst (TyArg t) =
          do k <- kindGoal "k"
             (t', q) <- normalize [] =<< checkTy' e0 t k
             return (TyArg t')
        checkInst (PrArg _) =
          error "internal: why am I type checking a predicate instantiation?"
checkTerm0 e0@(ESing t) expected =
  do t' <- checkTy' e0 t =<< kindGoal "k"
     q <- expectT e0 (TSing t') expected
     return (wrap q (ESing t'))
checkTerm0 e0@(ELabel Nothing el e) expected =
  do k <- ctorGoal "k"
     tl <- typeGoal' "l" KLabel
     t <- typeGoal "t"
     q <- expectT e0 (TConApp k (TRow [TLabeled tl t])) expected
     wrap q <$>
       (ELabel (Just k) <$> checkTerm'  el (TSing tl) <*> checkTerm'  e t)
checkTerm0 e0@(EUnlabel Nothing e el) expected =
  do k <- ctorGoal "k"
     tl <- typeGoal' "l" KLabel
     el' <- checkTerm el (TSing tl)
     elimForm expected $ \expected ->
       do e' <- checkTerm' e (TConApp k (TRow [TLabeled tl expected]))
          return (EUnlabel (Just k) e' el')
checkTerm0 e@(EConst c) expected =
  do ir <- newRef Nothing
     t <- constType c
     name <- fresh "i"
     q <- expectT e t (TInst (Unknown 0 (Goal (name, ir))) expected)
     return (wrap q $ EInst e (Unknown 0 (Goal (name, ir))))
  where -- This is necessary because I don't yet support kind polymorphism, so I can't express the
        -- types of the constants directly
        constType CPrj =
          do k <- kindGoal "r"
             let tvar 1 = TVar 1 "y"
                 tvar 0 = TVar 0 "z"
             return (TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $
                       PLeq (tvar 1) (tvar 0) `TThen`
                         TConApp Pi (tvar 0) `funTy` TConApp Pi (tvar 1))
        constType CInj =
          do k <- kindGoal "r"
             let tvar 1 = TVar 1 "y"
                 tvar 0 = TVar 0 "z"
             return (TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $
                       PLeq (tvar 1) (tvar 0) `TThen`
                         TConApp Sigma (tvar 1) `funTy` TConApp Sigma (tvar 0))
        constType CConcat =
          do k <- kindGoal "r"
             let tvar 2 = TVar 2 "x"
                 tvar 1 = TVar 1 "y"
                 tvar 0 = TVar 0 "z"
             return (TForall "x" (Just (KRow k)) $ TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $
                       PPlus (tvar 2) (tvar 1) (tvar 0) `TThen`
                         TConApp Pi (tvar 2) `funTy` TConApp Pi (tvar 1) `funTy` TConApp Pi (tvar 0))
        constType CBranch =
          do k <- kindGoal "r"
             let tvar 3 = TVar 3 "x"
                 tvar 2 = TVar 2 "y"
                 tvar 1 = TVar 1 "z"
                 tvar 0 = TVar 0 "t"
             return (TForall "x" (Just (KRow k)) $ TForall "y" (Just (KRow k)) $ TForall "z" (Just (KRow k)) $ TForall "t" (Just KType) $
                       PPlus (tvar 3) (tvar 2) (tvar 1) `TThen`
                         (TConApp Sigma (tvar 3) `funTy` tvar 0) `funTy`
                         (TConApp Sigma (tvar 2) `funTy` tvar 0) `funTy`
                         (TConApp Sigma (tvar 1) `funTy` tvar 0))
        constType CIn =
          do let f = TVar 0 "f"
             return (TForall "f" (Just (KType `KFun` KType)) $
                       f `TApp` TConApp Mu f `funTy` TConApp Mu f) where

        constType COut =
          do let f = TVar 0 "f"
             return (TForall "f" (Just (KType `KFun` KType)) $
                       TConApp Mu f `funTy` f `TApp` TConApp Mu f) where

        constType CFix =
          do let a = TVar 0 "a"
             return (TForall "a" (Just KType) $
                      (a `funTy` a) `funTy` a) where

        constType CStringCat =
          return (TString `funTy` TString `funTy` TString)

        constType CFold =
          return $
            TForall "r" (Just (KRow KType)) $
            TForall "t" (Just KType) $
              PFold (TVar 1 "r") `TThen`
              (TForall "l" (Just KLabel) $
               TForall "u" (Just KType) $
                  PLeq (TRow [TLabeled (TVar 1 "l") (TVar 0 "u")]) (TVar 3 "r") `TThen`
                  TSing (TVar 1 "l") `funTy` TVar 0 "u" `funTy` TVar 2 "t") `funTy`
              (TVar 0 "t" `funTy` TVar 0 "t" `funTy` TVar 0 "t") `funTy`
              TVar 0 "t" `funTy`
              TConApp Pi (TVar 1 "r") `funTy`
              TVar 0 "t"

checkTerm0 e0@(EAna phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     t <- typeGoal "t"
     elimForm expected $ \expected ->
       do q <- expectT e0 (TConApp Sigma (TApp (TMapFun phi') r) `funTy` t) expected
          let tvar 0 = TVar 0 "u"
              tvar 1 = TVar 1 "l"
          EAna phi' <$> checkTerm e (TForall "l" (Just KLabel) $ TForall "u" (Just k) $
                                                      PLeq (TRow [TLabeled (tvar 1) (tvar 0)]) (shiftTN 0 2 r) `TThen`
                                                      TSing (tvar 1) `funTy` TApp (shiftTN 0 2 phi') (tvar 0) `funTy` shiftTN 0 2 t)
checkTerm0 e0@(ESyn phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     q <- expectT e0 (TConApp Pi (TApp (TMapFun phi') r)) expected
     let tvar 0 = TVar 0 "u"
         tvar 1 = TVar 1 "l"
     ESyn phi' <$> checkTerm e (TForall "l" (Just KLabel) $ TForall "u" (Just k) $
                                                 PLeq (TRow [TLabeled (tvar 1) (tvar 0)]) (shiftTN 0 2 r) `TThen`
                                                 TSing (tvar 1) `funTy` TApp (shiftTN 0 2 phi') (tvar 0))

checkTerm0 e0@(ETyped e t) expected =
  do (t', _) <- normalize [] =<< checkTy' e0 t KType
     e' <- checkTerm e t'  -- any reason to preserve the type ascription?
     elimForm expected $ \expected ->
       do q <- expectT e0 t' expected
          return (ECast e' q)
checkTerm0 e0@(ELet x e f) expected =
  do (e', t) <- generalize e
     f' <- bind t (elimForm expected (checkTerm0 f))
     return (ELet x e' f')
checkTerm0 e0@(EStringLit _) expected =
  do expectT e0 TString expected
     return e0

generalize :: Term -> CheckM (Term, Ty)
generalize e =
  do tcin <- ask
     (level, t, e', remaining, psThere) <-
       upLevel $
       local (\cin -> cin { pctxt = [] }) $
       do t <- typeGoal "t"
          level <- theLevel
          (e', tcout) <- collect $ checkTerm e t
          (psHere, psThere) <- splitProblems level (goals tcout)
          remaining <- solverLoop psHere
          return (level, t, e', remaining, psThere)
     let (generalizable, ungeneralizable) = splitGeneralizable (kctxt tcin) remaining
     when (not (null ungeneralizable)) $ notEntailed ungeneralizable
     tell (TCOut (map (\(cin, p, evar) -> (cin { pctxt = pctxt cin ++ pctxt tcin }, p, evar)) psThere))
     genVars <- foldl cat [] <$> ((:) <$> uvars level t <*> mapM (puvars level . fst) generalizable)
     fixInsts t
     t' <- shiftTNV genVars 0 (length genVars) <$> flattenT t
     e'' <- shiftENV genVars 0 (length genVars) <$> flattenE e'
     trace $ "Generalizing " ++ intercalate ", " (map (renderString False . ppr) genVars) ++ " in " ++ renderString False (ppr t')
     as <- generalizeVars genVars
     generalizePreds generalizable
     let (e''', t'') = buildFinal as genVars generalizable e'' t'
     trace $ "Generalized: " ++ renderString False (ppr t')
     return (e''', t'')

  where uvars :: Int -> Ty -> CheckM [UVar]
        uvars _ (TVar {}) = return []
        uvars level (TUnif v@(UV { uvLevel = uvl, uvGoal = Goal (_, r) })) =
          do mt <- readRef r
             case mt of
               Just t -> uvars level t
               Nothing
                 | uvl >= level -> return [v]
                 | otherwise    -> return []
        uvars _ TFun = return []
        uvars level (TThen p t) = cat <$> puvars level p <*> uvars level t
        uvars level (TForall _ _ t) = uvars level t
        uvars level (TLam _ _ t) = uvars level t
        uvars level (TApp t u) = cat <$> uvars level t <*> uvars level u
        uvars _ (TLab {}) = return []
        uvars level (TSing t) = uvars level t
        uvars level (TLabeled l t) = cat <$> uvars level t <*> uvars level t
        uvars level (TRow ts) = foldl cat [] <$> mapM (uvars level) ts
        uvars level (TConApp k t) = uvars level t
        uvars level (TMapFun t) = uvars level t
        uvars level (TInst is t) = cat <$> isuvars is <*> uvars level t where
          isuvars (Unknown {}) = return []
          isuvars (Known is) = foldl cat [] <$> mapM iuvars is
          iuvars (TyArg t) = uvars level t
          iuvars (PrArg {}) = return []
        uvars level (TMapArg t) = uvars level t
        uvars _ TString = return []

        puvars :: Int -> Pred -> CheckM [UVar]
        puvars level (PEq t u) = cat <$> uvars level t <*> uvars level u
        puvars level (PLeq y z) = cat <$> uvars level y <*> uvars level z
        puvars level (PPlus x y z) = cat <$> (cat <$> uvars level x <*> uvars level y) <*> uvars level z
        puvars level (PFold z) = uvars level z

        cat :: [UVar] -> [UVar] -> [UVar]
        cat ts us = ts ++ filter (\u -> all (different u) ts) us

        ref = goalRef . uvGoal
        different t u = ref t /= ref u
        same t u = ref t == ref u

        splitProblems :: Int -> [Problem] -> CheckM ([Problem], [Problem])
        splitProblems level [] = return ([], [])
        splitProblems level (pr@(tcin, p, _) : prs) =
          do (here, there) <- splitProblems level prs
             prUvars <- (++) <$> (foldr (++) [] <$> mapM (puvars level) (pctxt tcin)) <*> puvars level p
             if null prUvars
             then return (here, pr : there)
             else return (pr : here, there)

        splitGeneralizable :: KCtxt -> [Problem] -> ([(Pred, IORef (Maybe Evid))], [Problem])
        splitGeneralizable _ [] = ([], [])
        splitGeneralizable now (pr@(cin, p, evar) : ps)
          | null (pctxt cin) && length now == length (kctxt cin) = ((p, evar) : gen, notGen)
          | otherwise                                            = (gen, pr : notGen)
          where (gen, notGen) = splitGeneralizable now ps

        generalizeVars :: [UVar] -> CheckM [String]
        generalizeVars ts =
          do names <- replicateM (n + 1) (fresh "a")
             sequence_ [generalize t b i | (t, b, i) <- zip3 ts names [0..]]
             return names
          where n = length ts - 1
                generalize (UV { uvGoal = Goal (_, r), uvKind = k }) b i =
                   writeRef r (Just (TVar (n - i) b))

        generalizePreds :: [(Pred, IORef (Maybe Evid))] -> CheckM ()
        generalizePreds ps =
          sequence_ [generalize v i | ((_, v), i) <- zip ps [0..]]
          where n = length ps - 1
                generalize v i = writeRef v (Just (VVar (n - i)))

        fixInsts :: Ty -> CheckM ()
        fixInsts t = everywhereM (mkM fixInst) t >> return () where
          fixInst :: Ty -> CheckM Ty
          fixInst t@(TUnif v) =
            do mu <- readRef (ref v)
               case mu of
                 Just u -> fixInsts u >> return t
                 Nothing -> return t
          fixInst t@(TInst (Unknown _ (Goal (_, iref))) _) =
            do mi <- readRef iref
               case mi of
                 Nothing -> do writeRef iref (Just (Known []))
                               return t
                 _       -> return t
          fixInst t = return t

        buildFinal :: [String] -> [UVar] -> [(Pred, IORef (Maybe Evid))] -> Term -> Ty -> (Term, Ty)
        buildFinal names ts ps e t =
          (tyLams ts names (prLams ps e), quantifiers ts names (qualifiers ps t))
          where quantifiers [] _ t = t
                quantifiers (u : us) (b : bs) t = TForall b (Just (uvKind u)) (quantifiers us bs t)
                qualifiers [] t = t
                qualifiers ((p, _) : ps) t = TThen p (qualifiers ps t)
                tyLams [] _ e = e
                tyLams (u : us) (b : bs) e = ETyLam b (Just (uvKind u)) (tyLams us bs e)
                prLams [] e = e
                prLams ((p, _) : ps) e = EPrLam p (prLams ps e)

checkTop :: Term -> Maybe Ty -> CheckM (Term, Ty)
checkTop m (Just t) =
  do trace $ "Begin type checking: " ++ renderString False (ppr m)
     m' <- checkTerm m t
     return (m', t)
checkTop m Nothing =
  do trace $ "Begin type checking: " ++ renderString False (ppr m)
     generalize m
