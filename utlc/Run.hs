
module Run where

import Prelude
import Terms
import Subst
import Beta
import YComb
import Booleans
import Church
import Factorial
import Fibonacci

main :: IO ()
main =
    do
        let t = refl_trans_beta (factorial three) in print t
        let m = Lambda "x" (Lambda "y" (App (App (Lambda "z" (Lambda "v" (App (Var "z") (App (Var "z") (Var "v"))))) (App (Var "x") (Var "y"))) (App (Var "z") (Var "u")))) 
            fvm = fv m 
            in print fvm
        let two = num 2 
            three = num 3 
            r = refl_trans_beta (addition two three)
            in print r
        let tttt = Lambda "c" (Var "c")
            in print tttt
        let t1 = Lambda "x" (App (Var "x") (Var "x")) 
            in print t1        
        let t2  = App (Lambda "y" (Var "y")) (Var "x")
            at2 = alpha "x" t2 
            in print at2
        let t1 = Lambda "x" (Var "x") 
            t2 = Lambda "y" (Var "y")
            in print (termEq t1 t2)
        let t1 = App (Lambda "u" (Var "u"))(Var "x")
            t2 = beta t1
            in print t2
        let t1 = Lambda "x" (Lambda "y" (Lambda "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))
            t2 = Lambda "x" (Var "x")
            t3 = App t1 t2
            t4 = beta t3
            t5 = beta t4
            in print t5
        let t1 = Lambda "z" (Lambda "v" (App (Var "z") (App (Var "z")(Var "v"))))
            t2 = App (Var "x") (Var "y")
            t3 = App (Var "z") (Var "u")
            t4 = Lambda "x" (Lambda "y" (App (App t1 t2) t3))
            in print (fv t4)
        let t1 = Lambda "x" (Lambda "y" (App (App (Var "x") (Var "y")) (Var "z")))
            t2 = subst t1 "z" (Var "w")
            in print t2
        let t1 = Lambda "x" (Lambda "y" (App (App (Var "x") (Var "y")) (Var "z")))
            t2 = Lambda "x" (App (Var "x") (Var "y"))
            t3 = subst t1 "z" t2
            in print t3
        print yComb
        print add
        let t1 = App (App add two) one 
            t2 = refl_trans_beta t1 
            t3 = App (App add two) t2 
            t4 = refl_trans_beta t3
            in print t4
        let t1 = App (App mult two) two 
            t2 = refl_trans_beta t1 
            t3 = App (App mult two) t2 
            t4 = refl_trans_beta t3
            in print t4 
        let t1 = predecessor two
            in print (refl_trans_beta t1)
        let t1 = App (App yComb fact) three
            t2 = refl_trans_beta t1
            in print t2
        let t1 = App (App add two) three
            t2 = factorial t1
            in print (refl_trans_beta t2)
        let t = addition one three
            in print (refl_trans_beta t)
        let t = factorial' four
            in print (refl_trans_beta t)  
        let t = fibTL three
            in print (refl_trans_beta t)
