module FunList where

data FunList a b t = Done t | More a (b -> t)

instance (Show a, Show t) => Show (FunList a b t) where
    show (Done t) = "Done " ++ show t
    show (More a f) = "More " ++ show a ++ " <function>"

data Identity x = Identity x 
data Const a b = Const a