module Plusses where

import Data.Generics
import Data.List
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer

import Syntax

newtype M a = M {runM :: WriterT [(Name, Pred)] (StateT Int (Except Error)) a}
  deriving (Functor, Applicative, Monad, MonadWriter [(Name, Pred)], MonadState Int, MonadError Error)

collect :: M a -> M (a, [(Name, Pred)])
collect = censor (const []) . listen

fresh :: M Name
fresh = do x <- get
           put (x + 1)
           return $ "$z#" ++ show x

class Sugared t where
  desugar :: t -> M t

catu :: Eq a => [a] -> [a] -> [a]
catu xs ys = filter (`notElem` ys) xs ++ ys
infixr 5 `catu`

tyvars :: Ty -> [QName]
tyvars (TVar i x) = [x]
tyvars (TUnif {}) = []
tyvars TFun = []
tyvars (TThen p t) = tyvarsP p `catu` tyvars t
tyvars (TForall x _ t) = filter ([x] /=) (tyvars t)
tyvars (TLam x _ t) = filter ([x] /=) (tyvars t)
tyvars (TLab {}) = []
tyvars (TSing t) = tyvars t
tyvars (TLabeled l t) = tyvars l `catu` tyvars t
tyvars (TConApp _ t) = tyvars t
tyvars (TMap t) = tyvars t
tyvars (TCompl z y) = tyvars z `catu` tyvars y
tyvars TString = []
tyvars (TInst {}) = error "Plusses.tyvars: TInst"
tyvars (TMapApp t) = tyvars t
tyvars (TPlus y z) = tyvars y `catu` tyvars z

tyvarsP :: Pred -> [QName]
tyvarsP = everything catu (mkQ [] tyvars)

implicitConstraints :: Ty -> M Ty
implicitConstraints t =
  do (t'', ps) <- collect (desugar t')
     let (here, there) = partition (any (`elem` map (sing . fst) bs) . tyvarsP . snd) ps
     let (bs', ps) = unzip here
     tell there
     return (rebind (bs ++ map (,Nothing) bs') (foldr TThen t'' ps))
  where (bs, t') = tybinders t
        sing x = [x]

quantifyAll :: Ty -> M Ty
quantifyAll t =
  do (t'', qs) <- collect (desugar t')
     let (bs', ps) = unzip qs
     return (rebind (bs ++ map (,Nothing) bs') (foldr TThen t'' ps))
  where (bs, t') = tybinders t

instance Sugared Ty where
  desugar t@(TVar {}) = return t
  desugar t@(TUnif {}) = return t
  desugar t@TFun = return t
  desugar (TThen p t) = TThen <$> desugar p <*> desugar t
  desugar t@(TForall {}) = implicitConstraints t
  desugar t@(TLam {}) = return t -- Not sure what to do here, actually... where does the constraint go in \a. a + {'l := Unit}?
  desugar (TApp t u) = TApp <$> desugar t <*> desugar u
  desugar t@(TLab {}) = return t
  desugar (TSing t) = TSing <$> desugar t
  desugar (TLabeled l t) = TLabeled <$> desugar l <*> desugar t
  desugar (TRow ts) = TRow <$> mapM desugar ts
  desugar (TConApp k t) = TConApp k <$> desugar t
  desugar (TMap t) = TMap <$> desugar t
  desugar (TCompl z y) = TCompl <$> desugar z <*> desugar y
  desugar t@TString = return t
  desugar (TInst {}) = error "Plusses.desugar: TInst"
  desugar (TMapApp t) = TMapApp <$> desugar t
  desugar (TPlus x y)
    | TRow xr <- x, TRow yr <- y, Just xs <- mapM splitConcrete xr, Just ys <- mapM splitConcrete yr =
      if any (`elem` map fst ys) (map fst xs)
      then throwError (ErrTypeDesugaring (TPlus x y))
      else return (TRow (map (uncurry TLabeled) (xs ++ ys)))
    | otherwise =
      do x' <- desugar x
         y' <- desugar y
         zv  <- fresh
         tell [(zv, PPlus x' y' (TVar (-1) [zv]))]
         return (TVar (-1) [zv])
    where splitConcrete (TLabeled (TLab s) x) = Just (TLab s, x)
          splitConcrete _ = Nothing
  desugar (TConOrd k ord t) =
    do t' <- desugar t
       zv <- fresh
       tell [(zv, case ord of
                    Leq -> PLeq (TVar (-1) [zv]) t'
                    Geq -> PLeq t' (TVar (-1) [zv]))]
       return (TConApp k (TVar (-1) [zv]))
  desugar t = error $ "<whoopsie: " ++ show t ++ ">"

desugarTy :: Ty -> M Ty
desugarTy t =
  do (t', ps) <- collect $ desugar t
     if null ps
     then return t'
     else throwError (ErrTypeDesugaring t)

instance Sugared Term where
  desugar = everywhereM (mkM desugarTy)

instance Sugared Pred where
  desugar = everywhereM (mkM (desugar :: Ty -> M Ty))

instance Sugared Decl where
  desugar (TyDecl x k t) =
    TyDecl x k <$> quantifyAll t
  desugar (TmDecl x Nothing m) =
    TmDecl x Nothing <$> desugar m
  desugar (TmDecl x (Just t) m) =
    do t' <- quantifyAll t
       TmDecl x (Just t') <$> desugar m

runDesugaring :: M a -> Either Error a
runDesugaring m = fst <$> runExcept (evalStateT (runWriterT (runM m)) 0)

desugarPluses :: [Decl] -> Either Error [Decl]
desugarPluses ds = runDesugaring (mapM desugar ds)


-- testing code
t1 = TForall "A" Nothing $ TForall "B" Nothing $ TPlus (TVar (-1) ["A"]) (TVar (-1) ["B"])

m1 = ETyLam "A" Nothing $ ETyLam "B" Nothing $ EInst (EVar (-1) ["id"]) (Known [TyArg (TPlus (TVar (-1) ["A"]) (TVar (-1) ["B"]))])


t2 = TApp (TApp TFun (TVar (-1) ["A"])) (TConOrd Sigma Geq (TRow [TLabeled (TLab "l") (TVar (-1) ["A"])]))
