
module Beta where

import Prelude
import Terms
import Subst

{- parallel full beta reduction -}
beta :: Term -> Term
beta e =
    case e of
        App (Lambda x t) s -> subst t x s
        Lambda x t         -> Lambda x (beta t)
        App s t            -> App (beta s) (beta t)
        _                  -> e

refl_trans_beta :: Term -> Term
refl_trans_beta e =
    if e == (beta e) then e else let e' = beta e in refl_trans_beta e'

{- call by name reduction -}
cbn :: Term -> Term
cbn t =
    case t of
        App (Lambda y t1) v -> subst t1 y v
        App t1 t2           -> App (cbn t1) t2
        _                   -> t 

{- normal reduction order: left-most outer-most (cbn variant) -}
normal :: Term -> Term
normal t =
    case t of
        App (Lambda y t1) v -> subst t1 y v
        App t1 t2           -> if t1 == normal t1 
                               then App t1 (normal t2)
                               else App (normal t1) t2
        Lambda y t1         -> Lambda y (normal t1) 
        _                   -> t

normal_multi :: Integer -> Term -> Term
normal_multi n t = if n > 0 then normal_multi (n - 1) (normal t)  else t 

{- call by value reduction -}
cbv :: Term -> Term
cbv t =
    case t of
        App (Lambda y t1) t2 -> if t2 == cbv t2 
                                then subst t1 y t2
                                else t
        App t1 t2            -> if cbv t1 == t1 
                                then App t1 (cbv t2)
                                else App (cbv t1) t2
        _                    -> t

cbv_multi :: Integer -> Term -> Term
cbv_multi n t = if n > 0 then cbv_multi (n - 1) (cbv t)  else t 

{- applicative reduction order: right-most inner-most (cbv variant) -}
applicative :: Term -> Term
applicative t =
    case t of
        App (Lambda y t1) t2 -> if t2 == applicative t2 
                                then subst t1 y t2
                                else App (Lambda y t1) (applicative t2)
        App t1 t2            -> if t1 == applicative t1
                                then App t1 (applicative t2)
                                else App (applicative t1) t2 
        Lambda y t1          -> Lambda y (applicative t1) 
        _                    -> t

applicative_multi :: Integer -> Term -> Term
applicative_multi n t = if n > 0 then applicative_multi (n - 1) (applicative t)  else t 