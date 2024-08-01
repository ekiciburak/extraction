
module YComb where

import Terms
import Subst
import Beta
import Booleans
import Church

yComb :: Term
yComb =
  Lambda "f" ( 
    App 
    (Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))) 
    (Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))) 
  )