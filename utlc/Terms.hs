{-# LANGUAGE GADTs #-} -- allows us to explicity write down the types of data constructors


module Terms where

import Prelude

data Term where
    Var    :: String -> Term
    Lambda :: String -> Term -> Term
    App    :: Term   -> Term -> Term 

term2String :: Term -> String
term2String t =
    case t of
        Var s       -> s
        Lambda s t1 -> "(λ" ++ s ++ ". " ++ term2String t1 ++ ")" 
        App t1 t2   -> "[" ++ term2String t1 ++ " " ++ term2String t2 ++ "]"

instance Show Term where
    show t = term2String t