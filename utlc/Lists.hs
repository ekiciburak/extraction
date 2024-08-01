
module Lists where

import Prelude
import Terms
import Subst
import Beta
import YComb
import Booleans
import Church
import Pairs

consH :: Term
consH =
    Lambda "x"
    (
        Lambda "y"
        (
            App(App(pairH)(false))(App(App(pairH)(Var "x"))(Var "y"))
            --pair (false) (pair (Var "x")(Var "y"))
        )
    )

cons :: Term -> Term -> Term
cons t1 l = App (App(consH)(t1))(l)

nil :: Term
nil = Lambda "x" (Var "x")

hdH :: Term
hdH = Lambda "z" (App(firstH)(App(secondH)(Var "x")))
--hdH = Lambda "z" (first (second (Var "z")))

hd :: Term -> Term
hd l = App hdH l

tlH :: Term
tlH = Lambda "z" (App(secondH)(App(secondH)(Var "x")))
--tlH = Lambda "z" (second (second (Var "z")))

tl :: Term -> Term
tl l = App tlH l

isNullH :: Term
isNullH = firstH

isNull :: Term -> Term
isNull t = App isNullH t
--isNull t = first t

{- list append
   example use: refl_trans_beta (Lists.length (cons (num 12) (cons (num 6) (cons (num 8) nil))))
-}
lengthH :: Term
lengthH = 
    Lambda "f"
    (
        Lambda "x"
        (
            ite'
            (isNull (Var "x"))
            (zero)
            (addition one (App (Var "f")(tl (Var "x"))))
        )
    )

length :: Term -> Term
length l = App (App(yComb)(lengthH))(l)

{- list append
   example use: refl_trans_beta (Lists.append (cons (num 7) (cons (num 5) nil))  (cons (num 12) (cons (num 6) (cons (num 8) nil))))
-}
appendH :: Term
appendH = 
    Lambda "f"
    (
        Lambda "x"
        (
            Lambda "y"
            (
                ite'
                (isNull (Var "x"))
                (Var "y")
                (cons (hd (Var "x"))(App (App(Var "f")(tl (Var "x")))(Var "y")))
            )
        )
    )

append :: Term -> Term -> Term
append l1 l2 = App(App(App(yComb)(appendH))(l1))(l2)

{- recursive list reversal: very slow; run with patience :) rather consider running below tail recursive version
   example use: refl_trans_beta (Lists.reverse (cons (num 7) (cons (num 5) nil)))
-}
reverseH :: Term
reverseH = 
    Lambda "f"
    (
        Lambda "x"
        (
            ite'
            (isNull (Var "x"))
            (nil)
            (append (App(Var "f")(tl (Var "x")))(cons(hd (Var "x"))(nil)))
        )
    )

reverse :: Term -> Term
reverse l = App (App(yComb)(reverseH))(l)

{- tail recursive list reversal: relatively faster but still slow on lists with more than 5 members 
   example use: refl_trans_beta (Lists.reverseAcc (cons (num 7) (cons (num 5) (cons (num 4) nil))))
-}
reverseAccH :: Term
reverseAccH = 
    Lambda "f"
    (
        Lambda "x"
        (
            Lambda "acc"
            (
                ite'
                (isNull (Var "x"))
                (Var "acc")
                (App (App(Var "f")(tl (Var "x")))(cons (hd (Var "x"))(Var "acc")))
            )
        )
    )

reverseAcc :: Term -> Term
reverseAcc l = App(App(App(yComb)(reverseAccH))(l))(nil)