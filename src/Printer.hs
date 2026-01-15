{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
module Printer where

import Control.Monad.Reader
import Data.IORef (readIORef)
import Data.List (intercalate)
import Data.String
import qualified Prettyprinter as P
import qualified Prettyprinter.Render.String as P
import qualified Prettyprinter.Util as P
import System.IO.Unsafe

import Syntax

data PrinterOptions = PO { level :: Int, printKinds :: Bool, printMaps :: Bool, printInstantiations :: Bool }
type RDoc ann = ReaderT PrinterOptions IO (P.Doc ann)

instance Semigroup (RDoc ann) where
  (<>) = liftA2 (<>)

instance Monoid (RDoc ann) where
  mempty = return mempty

instance IsString (RDoc ann) where
  fromString = pure . fromString

class Printable t where
  ppr :: t -> RDoc ann

ppre :: P.Pretty a => a -> RDoc ann
ppre = pure . P.pretty

ifM :: Monad m => m Bool -> m a -> m a -> m a -- this seems to be defined in a bunch of random places
ifM mb m0 m1 = do b <- mb; if b then m0 else m1

with :: Int -> RDoc ann -> RDoc ann
with n d =
  ifM (asks ((n >=) . level)) d (P.parens <$> at 0 d)

at :: Int -> RDoc ann -> RDoc ann
at n d = local (\po -> po {level = n}) d

sep :: [RDoc ann] -> RDoc ann
sep = fmap P.sep . sequence

vsep, vcat :: [RDoc ann] -> RDoc ann
vsep = fmap P.vsep . sequence
vcat = fmap P.vcat . sequence

fillSep :: [RDoc ann] -> RDoc ann
fillSep = fmap P.fillSep . sequence

hang, nest, indent :: Int -> RDoc ann -> RDoc ann
hang = fmap . P.hang
nest = fmap . P.nest
indent = fmap . P.indent

-- copied from Prettyprinter library... fun puzzle: how to properly lift this through the reader monad...
punctuate :: RDoc ann -> [RDoc ann] -> [RDoc ann]
punctuate p = go where
    go []     = []
    go [d]    = [d]
    go (d:ds) = (d <> p) : go ds

(<+>) :: RDoc ann -> RDoc ann -> RDoc ann
(<+>) = liftA2 (P.<+>)

(<:>) :: RDoc ann -> RDoc ann -> RDoc ann
x <:> y = fillSep [x <+> pure P.colon, y]

braces, brackets, parens :: RDoc ann -> RDoc ann
braces = fmap P.braces
brackets = fmap P.brackets
parens = fmap P.parens

stringFromQName :: QName -> String
stringFromQName [x] = x
stringFromQName [x, ""] = x
stringFromQName xs = intercalate "." (reverse xs)

instance Printable QName where
  ppr = ppre . stringFromQName


instance Printable Kind where
  ppr KType = "*"
  ppr KLabel = "L"
  ppr (KRow k) = "R[" <> ppr k <> "]"
  ppr (KFun k1 k2) = with 0 $ fillSep [at 1 (ppr k1) <+> "->", ppr k2]
  ppr (KUnif (Goal (s, mkr))) =
    do mk <- liftIO (readIORef mkr)
       case mk of
         Nothing -> "%" <> ppre s
         Just k  -> ppr k

-- Precedence table:
--   forall, lambda   0
--   :=               1
--   =>, ->           2
--   application      3

-- TODO: fix precedence in printing
-- TODO: I think the precedence above is not what the parser implements

instance Printable Level where
  ppr (Lv i) = ppre i
  ppr Top    = pure "T"

instance Printable UVar where
  ppr (UV n l (Goal (s, rmt)) k) =
    do mt <- liftIO (readIORef rmt)
       case mt of
         Just t -> ppr t
         Nothing ->
           do pk <- asks printKinds
              let name = ppre s <> "@" <> ppr l <>
                         if n > 0 then "^" <> ppre n else mempty
              if pk
              then name <:> (P.align <$> ppr k)
              else name

instance Printable TyCon where
  ppr Pi = "Pi"
  ppr Sigma = "Sigma"
  ppr (Mu Nothing) = "Mu"
  ppr (Mu (Just n)) = "Mu [" <> ppre n <> "]"
  ppr (TCUnif g) =
    do mk <- liftIO (readIORef (goalRef g))
       case mk of
         Just k -> ppr k
         Nothing -> ppre (goalName g)

instance Printable Ty where
  ppr (TVar _ x) = ppr x
  ppr (TUnif v) = ppr v
  ppr TFun = "(->)"
  ppr (TThen p t) = fillSep [ppr p <+> "=>", ppr t]
  ppr (TForall x (Just k) t) = with 0 $ nest 2 $ fillSep ["forall" <+> ppre x <:> ppr k <> ".", ppr t]
  ppr (TForall x Nothing t) = with 0 $ nest 2 $ fillSep ["forall" <+> ppre x <> ".", ppr t]
  ppr (TLam x (Just k) t) = with 0 $ nest 2 $ fillSep ["\\" <> ppre x <:> ppr k <> ".", ppr t]
  ppr (TLam x Nothing t) = with 0 $ nest 2 $ fillSep ["\\" <> ppre x <> ".", ppr t]
  ppr (TApp (TApp TFun t) u) = with 2 $ fillSep [at 3 (ppr t) <+> "->", ppr u]
  ppr (TApp t u) = with 3 $ fillSep [at 3 (ppr t), at 4 (ppr u)]
  ppr (TLab s) = "'" <> ppre s
  ppr (TSing t) = "#" <> at 5 (ppr t)
  ppr (TLabeled l t) = fillSep [ppr l <+> ":=", ppr t]
  ppr (TRow ts) = braces (fillSep (punctuate "," (map ppr ts)))
  ppr (TConApp k t) = ppr k <+> at 4 (ppr t)
  ppr (TMapFun t) =
    do b <- asks printMaps
       if b then "map" <+> ppr t else ppr t
  ppr (TMapArg t) =
    do b <- asks printMaps
       if b then "map_arg" <+> ppr t else ppr t
  ppr TString = "String"
  ppr (TInst (Unknown n (Goal (s, r))) t) =
    do b <- asks printInstantiations
       if b
       then do minst <- liftIO $ readIORef r
               case minst of
                 Nothing -> brackets ("^" <> ppre n <> "%" <> ppre s) <+> parens (ppr t)
                 Just is  -> ppr (TInst is t)
       else ppr t
  ppr (TInst (Known is) t) =
    do b <- asks printInstantiations
       if b
       then do with 3 $ fillSep (map pprI is ++ [ppr t])
       else ppr t
    where pprI (TyArg t) = brackets (ppr t)
          pprI (PrArg v) = brackets (ppre (show v)) -- dunno what to put here, honestly...

  ppr (TCompl r0 r1) = fillSep [ppr r0 <+> "-", ppr r1]
  ppr (TPlus y z) = fillSep [parens (ppr y) <+> "+", parens (ppr z)] -- oops, need a precedence table...
  ppr (TConOrd k rel t) = ppr k <> pprel rel <+> at 4 (ppr t) where
    pprel Geq = ">"
    pprel Leq = "<"
  ppr t = "<missing: " <> ppre (show t) <> ">"

instance Printable Pred where
  ppr (PLeq t u) = fillSep [ppr t <+> "<", ppr u ]
  ppr (PPlus t u v) = fillSep [ppr t <+> "+", ppr u <+> "~", ppr v]
  ppr (PEq t u) = fillSep [ppr t <+> "~", ppr u]
  ppr (PFold z) = fillSep ["Fold", ppr z]

-- Precedence table:
--   lambda           0
--   ++, |            1
--   :=               2
--   application      3

instance Printable Term where
  ppr (EVar _ s) = ppr s
  ppr (ELam x (Just t) m) = with 0 $ nest 2 $ fillSep ["\\" <> ppre x <:> ppr t <> ".", ppr m]
  ppr (ELam x Nothing m) = with 0 $ nest 2 $ fillSep ["\\" <> ppre x <> ".", ppr m]
  ppr (EApp (EApp (EInst (EConst CConcat) _) e1) e2) =
    with 1 $ fillSep [at 2 (ppr e1), "++", ppr e2]
  ppr (EApp (EApp (EInst (EConst CBranch) _) e1) e2) =
    with 1 $ fillSep [at 2 (ppr e1), "|", ppr e2]
  ppr (EApp (EApp (EConst CStringCat) e1) e2) =
    with 1 $ fillSep [at 2 (ppr e1), "^", ppr e2]
  ppr (EApp m n) = with 4 $ fillSep [ppr m, at 5 (ppr n)]
  ppr (ETyLam x (Just k) m) = with 0 $ nest 2 $ fillSep ["/\\" <> ppre x <:> ppr k <> ".", ppr m]
  ppr (ETyLam x Nothing m) = with 0 $ nest 2 $ fillSep ["/\\" <> ppre x <> ".", ppr m]
  ppr (EInst m (Known is)) = with 4 $ fillSep (ppr m : map pprI is) where
    pprI (TyArg t) = brackets (ppr t)
    pprI (PrArg v) = brackets (ppre (show v))
  ppr (EInst m (Unknown n (Goal (s, r)))) =
    do minst <- liftIO $ readIORef r
       case minst of
         Nothing -> with 4 (fillSep [ppr m, brackets (ppre s)])
         Just is -> ppr (EInst m is)
  ppr (ESing t) = "#" <> at 4 (ppr t)
  ppr (ELabel Nothing l m) = with 3 (fillSep [ppr l <+> ":=", at 3 (ppr m)])
  ppr (ELabel (Just k) l m) = with 3 (fillSep [ppr l <+> ":=" <> ppr k, at 3 (ppr m)])
  ppr (EUnlabel Nothing m l) = with 3 (fillSep [ppr m <+> "/", at 3 (ppr l)])
  ppr (EUnlabel (Just k) m l) = with 3 (fillSep [ppr m <+> "/" <> ppr k, at 3 (ppr l)])
  ppr (EConst c) = name c where
    name CPrj = "prj"
    name CConcat = "(++)"
    name CInj = "inj"
    name CBranch = "(|)"
    name CFix = "fix"
    name CStringCat = "(^)"
    name CSyn = "syn"
    name CAna = "ana"
    name CFold = "fold"
  ppr (ELet x m n) = with 0 $ nest 2 $ fillSep ["let" <+> ppre x <+> "=" <+> ppr m <+> "in", ppr n]
  ppr (ETyped e t) = with 1 (fillSep [ppr e <+> ":", ppr t])
  -- Not printing internals (yet)
  ppr (EPrLam _ m) = ppr m
  ppr (ECast m VEqRefl) = ppr m
  ppr (ECast m q) = parens (fillSep [ppr m <+> "<|", fromString (show q)])
  ppr (EStringLit s) = "\"" <> ppre s <> "\""
  ppr (EHole s) = "?" <> ppre s

instance Printable Evid where
  ppr _ = "<evid>"

pprTyDecl :: QName -> Ty -> RDoc ann
pprTyDecl x ty = fillSep [ppr x <+> ":", ppr ty]

pprTyping (x, ty, e) =
  vcat [fillSep [ppr x <+> ":", ppr ty], fillSep [ppr x <+> "=", ppr e]]

pprTypeError :: Error -> RDoc ann
pprTypeError te = vsep ctxts <> pure P.line <> indent 2 (pprErr te')
  where d <:> (ds, te) = (d : ds, te)
        contexts (ErrContextDefn d te) = ("Whilst checking the definition of" <+> ppr d) <:> contexts te
        contexts (ErrContextType ty te) = ("Whilst checking the type" <+> ppr ty) <:> contexts te
        contexts (ErrContextPred pr te) = ("Whilst checking the predicate" <+> ppr pr) <:> contexts te
        contexts (ErrContextTerm t te) = ("While checking the term" <+> ppr t) <:> contexts te
        contexts (ErrContextTyEq t u te) = ("While comparing the types" <+> ppr t <+> "and" <+> ppr u) <:> contexts te
        contexts (ErrContextOther s te) = ppre s <:> contexts te
        contexts te = ([], te)

        (ctxts, te') = contexts te

        pprErr (ErrTypeMismatch actual expected actual' expected') = vsep ["Actual type" <+> ppr actual, "was expected to be" <+> ppr expected, "specifically: " <+> ppr actual' <+> "~/~" <+> ppr expected']
        pprErr (ErrTypeMismatchFD p) = "Type mismatch in functional dependencies for" <+> ppr p
        pprErr (ErrTypeMismatchPred p t u) = vsep ["Type mismatch in functional dependencies for" <+> ppr p, "type" <+> ppr t, "was expected to be" <+> ppr u]
        pprErr (ErrKindMismatch k k') = vsep ["Actual kind" <+> ppr k, "was expected to be" <+> ppr k']
        pprErr (ErrNotEntailed errs) = vsep (map pprOne errs)
          where pprOne (p, qs) = vsep ["The predicate" <+> ppr p, hang 2 ("is not entailed by" <+> fillSep (punctuate "," (map ppr qs)))]
        pprErr (ErrUnboundTyVar v) = "Unbound type variable" <+> ppr v
        pprErr (ErrUnboundVar v) = "Unbound variable" <+> ppr v
        pprErr (ErrDuplicateDefinition v) = "Duplicate definition o" <+> ppr v
        pprErr (ErrTypeDesugaring t) = "Error in desugaring" <+> ppr t
        pprErr (ErrOther s) = ppre s

renderString :: RDoc ann -> String
renderString doc =
  unsafePerformIO $
  do d <- runReaderT doc (PO {level = 0, printKinds = False, printMaps = False, printInstantiations = True})
     return (P.renderString (P.layoutPretty (P.LayoutOptions P.Unbounded) d))
