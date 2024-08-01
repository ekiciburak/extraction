
module Fibonacci where

import Prelude
import Terms
import Subst
import Beta
import YComb
import Booleans
import Church

{- recursive fibonacci function: very slow on numbers greater than 5
   example use: refl_trans_beta (fibonacci (num 3))
-}
fib :: Term
fib =
    Lambda "f"
    (
        Lambda "x"
        (
            ite' (isZero (Var "x"))
                 (zero) 
                 (
                    ite' (isZero (predecessor (Var "x")))
                         (one)
                         (
                            addition (App (Var "f") (predecessor (Var "x"))) 
                                     (App (Var "f") (predecessor (predecessor (Var "x"))))
                         )
                 )
        )
    ) 

fibonacci :: Term -> Term
fibonacci n = App (App yComb fib) n

{- tail recursive fibonacci function: relatively faster -- still handle with care
   example use: refl_trans_beta (fibTL (num 4))
-}
fibTLH :: Term
fibTLH =
    Lambda "f"
    (
        Lambda "n"
        (
            Lambda "i"
            (
                Lambda "a"
                (
                    Lambda "b"
                    (
                        ite'
                        (eq (Var "n")(Var "i"))
                        (Var "a")
                        (App(App(App(App(Var "f")(Var "n"))(addition (Var "i")(one)))(Var "b"))(addition(Var "a")(Var "b")))
                    )
                )
            )
        )
    )

fibTL :: Term -> Term
fibTL n = App(App(App(App(App(yComb)(fibTLH))(n))(zero))(zero))(one)
