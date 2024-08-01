module Church where

import Prelude
import Terms
import Subst
import Beta
import Booleans

zero :: Term
zero = Lambda "s" (Lambda "z" (Var "z"))

one :: Term
one = Lambda "s" (Lambda "z" (App (Var "s") (Var "z")))

two :: Term
two = Lambda "s" (Lambda "z" (App (Var "s") (App (Var "s") (Var "z"))))

three :: Term
three = Lambda "s" (Lambda "z" (App (Var "s") (App (Var "s") (App (Var "s") (Var "z")))))

four :: Term
four = Lambda "s" (Lambda "z" (App (Var "s") (App (Var "s") (App (Var "s") (App (Var "s") (Var "z"))))))

five :: Term
five = Lambda "s" (Lambda "z" (App (Var "s") (App (Var "s") (App (Var "s") (App (Var "s") (App (Var "s") (Var "z")))))))

six :: Term
six = Lambda "s" (Lambda "z" (App (Var "s") (App (Var "s") (App (Var "s") (App (Var "s") (App (Var "s") (App (Var "s") (Var "z"))))))))

{- computes Church numeral out of (positive) Haskell integers 
   example use: num 8
-}
numH :: Integer -> Term
numH n = if n == 0 then (Var "z") else (App (Var "s") (numH (n-1)))

num :: Integer -> Term
num n = Lambda "s" (Lambda "z" (numH n)) 

{- recursive sum
   example use: refl_trans_beta (addition (num 4) (num 6))
-}
add :: Term
add =
    Lambda "M"
    (
        Lambda "N"
        (
            Lambda "s"
            (
                Lambda "z"
                (
                    App (App (Var "N") (Var "s")) (App (App (Var "M") (Var "s")) (Var "z"))
                    --App (App (Var "N") (Var "s")) 
                    --    (App (App (Var "M") (Var "s")) (Var "z"))
                )
            )
        )
    )

addition :: Term -> Term -> Term
addition t1 t2 = App (App add t1) t2

{- recursive multiplication
   example use: refl_trans_beta (multiplication (num 4) (num 6))
-}

mult :: Term
mult =
    Lambda "M"
    (
        Lambda "N"
        (
            Lambda "s"
            (
                Lambda "z"
                (
                    App (App (Var "N") (App (Var "M") (Var "s"))) (Var "z")
                )
            )
        )
    )

multiplication :: Term -> Term -> Term
multiplication t1 t2 = App (App mult t1) t2 

{- recursive predecessor
   example use: refl_trans_beta (predecessor (num 6))
-}
pred :: Term
pred =
    Lambda "n" 
    (
        Lambda "f"
        (
            Lambda "x"
            (   App 
                    (App
                        (App (Var "n") 
                             (Lambda "g" (Lambda "h" (App (Var "h") (App (Var "g") (Var "f"))))))
                        (Lambda "u" (Var "x")))
                    (Lambda "u" (Var "u"))
                
            )
        )
    )

predecessor :: Term -> Term
predecessor n = App Church.pred n 

{- recursive subtraction
   example use: refl_trans_beta (subtraction (num 9) (num 6))
-}
minus :: Term
minus = 
    Lambda "m"
    (
        Lambda "n"
        (
            App (App(Var "n")(Church.pred))(Var "m")
        )
    )

subtraction :: Term -> Term -> Term
subtraction m n = App (App(minus)(m))(n)


isZeroH :: Term
isZeroH = Lambda "n" (App (App (Var "n") (Lambda "x" false)) (true))

isZero :: Term -> Term
isZero n = App isZeroH n 

{- recursive comparison
   example use: refl_trans_beta (leq (num 9) (num 6))
-}
leqH :: Term
leqH =
    Lambda "m"
    (
        Lambda "n"
        (
            isZero (subtraction (Var "m")(Var "n"))
        )
    )

leq :: Term -> Term -> Term
leq m n = App(App(leqH)(m))(n)

{- recursive equality check
   example use: refl_trans_beta (eq (num 9) (num 6))
-}
eqH :: Term
eqH =
    Lambda "m"
    (
        Lambda "n"
        (
            Booleans.and (leq (Var "m")(Var "n"))(leq (Var "n")(Var "m"))
        )
    )

eq :: Term -> Term -> Term
eq m n = App(App(eqH)(m))(n)

