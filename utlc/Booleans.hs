
module Booleans where

import Prelude
import Terms
import Subst
import Beta

true :: Term
true = Lambda "x" (Lambda "y" (Var "x"))

false :: Term
false = Lambda "x" (Lambda "y" (Var "y"))

notH :: Term
notH =
    Lambda "x" (Lambda "y" (Lambda "z" (App (Var "x") (App (Var "z") (Var "y")))))

not :: Term -> Term 
not b = App notH b

andH :: Term
andH =
    Lambda "p"
    (
        Lambda "q"
        (
            App(App(Var "p")(Var "q"))(Var "p")
        )
    )

and :: Term -> Term -> Term
and p q = App(App(andH)(p))(q)

orH :: Term
orH =
    Lambda "p"
    (
        Lambda "q"
        (
            App(App(Var "p")(Var "p"))(Var "q")
        )
    )

or :: Term -> Term -> Term
or p q = App(App(orH)(p))(q)

ite :: Term
ite =
    Lambda "f"
    (
        Lambda "a"
        (
            Lambda "b"
            (
                App (App (Var "f") (Var "a")) (Var "b")
            )
        )
    )

ite' :: Term -> Term -> Term -> Term
ite' b f g = App(App(App(ite)(b))(f))(g)