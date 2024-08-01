
module Subst where

import Prelude
import Terms
import Data.IORef
import System.IO.Unsafe

counterRef :: IORef Int
counterRef = unsafePerformIO (newIORef 0)

incrementCount :: IO Int
incrementCount = atomicModifyIORef counterRef (\v -> (v+1,v+1))

readCount :: IO Int
readCount = readIORef counterRef

resetCount :: IO Int
resetCount = atomicModifyIORef counterRef (\v -> (0,0))

freshVar :: String -> String
freshVar s = let x = unsafePerformIO incrementCount in s ++ (show x)

find :: Eq a => a -> [a] -> Bool
find e l =
    case l of
        []   -> False
        x:xs -> if x == e then True else find e xs

uniqueH :: Eq a => [a] -> [a] -> [a]
uniqueH l acc =
    case l of
        []   -> acc
        x:xs -> if find x acc then uniqueH xs acc else uniqueH xs (acc ++ [x])

unique :: Eq a => [a] -> [a]
unique l = uniqueH l []

replace :: String -> String -> Term -> Term
replace x y t =
    case t of
        Var s       -> if s == x then Var y else t
        Lambda s t1 -> if s == x then Lambda y (replace x y t1) else Lambda s (replace x y t1)
        App t1 t2   -> App (replace x y t1) (replace x y t2)

swap :: (String -> String) -> Term -> Term
swap f t = 
    case t of
        Var s       -> Var (f s)
        Lambda s t1 -> Lambda (f s) (swap f t1)
        App t1 t2   -> App (swap f t1) (swap f  t2)

fvH :: Term -> [String] -> [String]
fvH t acc =
    case t of
        Var s       -> s : acc
        Lambda x t1 -> filter (\a -> a /= x) (fvH t1 acc)
        App t1 t2   -> unique (fvH t1 acc ++ fvH t2 acc)

fv :: Term -> [String]
fv t = fvH t []

alpha :: String -> Term -> Term
alpha x t =
    case t of
        Lambda y t1 -> if (y /= x && (find x (fv t1) == False)) then Lambda x (replace y x t1) else t
        App t1 t2   -> App (alpha x t1) (alpha x t2)
        Var y       -> Var y


freshness:: [String] -> Term -> Bool
freshness l t = 
    let fvl = fv t in next l fvl
    where
        next l fvl =
            case l of
                []   -> True
                x:xs -> if find x fvl then False else next xs fvl

subst :: Term -> String -> Term -> Term
subst t x s =
    case t of
        Var y       -> if x == y then s else t
        Lambda y t1 -> if x /= y &&  (find y (fv s) == False) -- freshness [y] s 
                       then Lambda y (subst t1 x s)
                   --    else if x == y &&  (find y (fv s) == False) then t
                       else let z  = freshVar y
                                t' = alpha z t
                            in subst t' x s
        App t1 t2   -> App (subst t1 x s) (subst t2 x s)


termEq :: Term -> Term -> Bool
termEq t1 t2 =
  case (t1, t2) of
    (Lambda x1 e1, Lambda x2 e2) -> let fv = freshVar "x" in
                                       let te1 = subst e1 x1 (Var fv) in
                                       let te2 = subst e2 x2 (Var fv) in
                                       termEq te1 te2
    (App t1 t2, App t3 t4)       -> termEq t1 t3 && termEq t2 t4
    (Var s1, Var s2)             -> s1 == s2
    (_, _)                       -> False

termSame :: Term -> Term -> Bool
termSame t1 t2 =
    case (t1, t2) of
        (Lambda x1 e1, Lambda x2 e2) -> x1 == x2 && termSame e1 e2
        (App t1 t2, App t3 t4)       -> termSame t1 t3 && termSame t2 t4
        (Var s1, Var s2)             -> s1 == s2
        (_,_)                        -> False

instance Eq Term where
    t1 == t2 = termEq t1 t2