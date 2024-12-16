{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
module Printer where

import Control.Monad.Reader
import Data.IORef (readIORef)
import Data.String
import qualified Prettyprinter as P
import qualified Prettyprinter.Util as P
import Syntax

data PrinterOptions = PO { level :: Int, printKinds :: Bool }
type RDoc ann = ReaderT PrinterOptions IO (P.Doc ann)

instance Semigroup (RDoc ann) where
  (<>) = liftA2 (<>)

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

vsep :: [RDoc ann] -> RDoc ann
vsep = fmap P.vsep . sequence

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

instance Printable Ty where
  ppr (TVar _ s mk) =
    do pk <- asks printKinds
       case mk of
         Just k | pk -> ppre s <:> (P.align <$> ppr k)
         _ -> ppre s
  ppr (TUnif n j (Goal (s, rmt)) k) =
    do mt <- liftIO (readIORef rmt)  
       case mt of
         Just t -> ppr t
         Nothing ->
           do pk <- asks printKinds
              if pk
              then ("^" <> ppre n <> "," <> ppre j <> "%" <> ppre s) <:> (P.align <$> ppr k)
              else "^" <> ppre n <> "," <> ppre j <> "%" <> ppre s
  ppr TFun = "(->)"
  ppr (TThen p t) = fillSep [ppr p <+> "=>", ppr t]
  ppr (TForall x k t) = with 0 $ nest 2 $ fillSep ["forall" <+> ppre x <:> ppr k <> ".", ppr t]
  ppr (TLam x k t) = with 0 $ nest 2 $ fillSep ["\\" <> ppre x <:> ppr k <> ".", ppr t]
  ppr (TApp (TApp TFun t) u) = with 2 $ fillSep [at 3 (ppr t) <+> "->", ppr u]
  ppr (TApp t u) = with 3 $ fillSep [at 3 (ppr t), at 4 (ppr u)]
  ppr (TLab s) = "'" <> ppre s
  ppr (TSing t) = "#" <> at 5 (ppr t)
  ppr (TLabeled l t) = fillSep [ppr l <+> ":=", ppr t]
  ppr (TRow ts) = braces (fillSep (punctuate "," (map ppr ts)))
  ppr (TPi t) = with 3 $ "Pi " <> at 4 (ppr t)
  ppr (TSigma t) = with 3 $ "Sigma " <> at 4 (ppr t)
  ppr (TMapFun t) = ppr t
  ppr (TMapArg t) = ppr t
  -- ppr (TShift t) = "^" <> at 4 (ppr t)
  ppr t = "<missing: " <> ppre (show t) <> ">"

instance Printable Pred where
  ppr (PLeq t u) = fillSep [ppr t <+> "<", ppr u ]
  ppr (PPlus t u v) = fillSep [ppr t <+> "+", ppr u <+> "~", ppr v]

-- Precedence table: 
--   lambda           0
--   ++, ?            1
--   :=               2
--   application      3         


instance Printable Term where
  ppr (EVar _ s) = ppre s
  ppr (ELam x t m) = with 0 $ nest 2 $ fillSep ["\\" <> ppre x <:> ppr t <> ".", ppr m]
  ppr (EApp m n) = with 3 $ fillSep [ppr m, at 4 (ppr n)]
  ppr (ETyLam x k m) = with 0 $ nest 2 $ fillSep ["/\\" <> ppre x <:> ppr k <> ".", ppr m]
  ppr (ETyApp m t) = with 3 $ fillSep [ppr m, brackets (ppr t)]
  ppr (ESing t) = "#" <> at 4 (ppr t)
  ppr (ELabel l m) = with 2 (fillSep [ppr l <+> ":=", at 3 (ppr m)]) 
  ppr (EUnlabel m l) = with 2 (fillSep [ppr m <+> "/", at 3 (ppr l)])
  ppr (EPrj _ _ _ m) = with 3 (fillSep ["prj", at 4 (ppr m)])
  ppr (EConcat _ _ _ _ m n) = with 1 (fillSep [at 2 (ppr m) <+> "++", ppr n])
  ppr (EInj _ _ _ m) = with 3 (fillSep ["inj", at 4 (ppr m)])
  ppr (EBranch _ _ _ _ m n) = with 1 (fillSep [at 2 (ppr m) <+> "?", ppr n])
  ppr (ESyn f m) = with 3 (fillSep ["syn", brackets (ppr f), at 4 (ppr m)])
  ppr (EAna f m) = with 3 (fillSep ["ana", brackets (ppr f), at 4 (ppr m)])
  ppr (EFold {}) = "<fold>"
  ppr (EIn {}) = "<in>"
  ppr (EOut {}) = "<out>"
  ppr (EFix {}) = "<fix>"
  -- Not printing internals (yet)
  ppr (EPrLam _ m) = ppr m
  ppr (EPrApp m _) = ppr m
  ppr (ETyEqu m _) = ppr m


instance Printable Evid where
  ppr _ = "<evid>"

instance Printable TyEqu where
  ppr _ = "<equ>"


pprTyDecl :: String -> Ty -> RDoc ann
pprTyDecl x ty = fillSep [ppre x <+> ":", ppr ty]

pprTypeError :: Error -> RDoc ann
pprTypeError te = vsep ctxts <> pure P.line <> indent 2 (pprErr te')
  where d <:> (ds, te) = (d : ds, te)
        contexts (ErrContextType ty te) = ("Whilst checking the type" <+> ppr ty) <:> contexts te
        contexts (ErrContextPred pr te) = ("Whilst checking the predicate" <+> ppr pr) <:> contexts te
        contexts (ErrContextTerm t te) = ("While checking the term" <+> ppr t) <:> contexts te
        contexts (ErrContextOther s te) = ppre s <:> contexts te
        contexts te = ([], te)

        (ctxts, te') = contexts te

        pprErr (ErrTypeMismatch m actual expected) = vsep ["The term" <+> ppr m, "has type" <+> ppr actual, "but expected" <+> ppr expected]
        pprErr (ErrTypeMismatchFD p _) = "Type mismatch in functional dependencies for" <+> ppr p
        pprErr (ErrTypeMismatchPred p t u) = vsep ["Type mismatch in functional dependencies for" <+> ppr p, "type" <+> ppr t, "was expected to be" <+> ppr u]
        pprErr (ErrKindMismatch t k k') = vsep ["The type" <+> ppr t, "has kind" <+> ppr k, "but expected" <+> ppr k']
        pprErr (ErrNotEntailed errs) = vsep (map pprOne errs)
          where pprOne (p, qs) = vsep ["The predicate" <+> ppr p, hang 2 ("is not entailed by" <+> fillSep (punctuate "," (map ppr qs)))]
        pprErr (ErrUnboundTyVar v) = "Unbound type variable" <+> ppre v
        pprErr (ErrUnboundVar v) = "Unbound variable" <+> ppre v
        pprErr (ErrOther s) = ppre s

f :: Int -> Bool -> RDoc ann -> IO ()
f n pk d = do P.putDocW n =<< runReaderT d (PO {level = 0, printKinds = pk})
              putStrLn ""              