
module Factorial where

import Prelude
import Terms
import Subst
import Beta
import YComb
import Booleans
import Church

{- recursive factorial calculation: very slow on numbers greater than 6
   example use: refl_trans_beta (factorial (num 4))
-}
fact :: Term
fact =
    Lambda "f"
    (
        Lambda "x"
        (
            App (App (App (ite) (App (isZeroH) (Var "x"))) (one))
                (App (App (mult) (Var "x")) (App (Var "f") (App (Church.pred) (Var "x"))))

        )
    )

factorial :: Term -> Term
factorial n = App (App yComb fact) n

fact' :: Term
fact' =
    Lambda "f"
    (
        Lambda "x"
        (
            ite' (isZero (Var "x")) (one) (multiplication (Var "x") (App (Var "f") (predecessor (Var "x"))))
        )
    )

factorial' :: Term -> Term
factorial' n = App (App yComb fact') n


