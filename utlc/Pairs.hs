
module Pairs where


import Prelude
import Terms
import Subst
import Beta
import YComb
import Booleans
import Church

pairH :: Term
pairH = 
    Lambda "x" 
    (
        Lambda "y"
        (
            Lambda "f"
            (
                App (App(Var "f")(Var "x"))(Var "y")
            )
        )
    )

pair :: Term -> Term -> Term
pair t1 t2 = App (App (pairH)(t1))(t2)

firstH :: Term
firstH = Lambda "p" (App (Var "p") true)

first :: Term -> Term
first p = App firstH p

secondH :: Term
secondH = Lambda "p" (App (Var "p") false)

second  :: Term -> Term
second p = App secondH p