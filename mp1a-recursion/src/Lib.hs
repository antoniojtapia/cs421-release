--- Getting Started
--- ===============

--- Relevant Files
--- --------------

module Lib where

-- This line imports the Prelude module without certain functions
import Prelude hiding ( take, drop, reverse
                      , zip, zipWith
                      , map, foldl, foldr
                      , iterate, repeat
                      , replicate, cycle
                      , (++)
                      )
-- When you are allowed to use builtin functions Prepend them with "P."
-- for example `P.take`
import qualified Prelude as P

--- Metadata for autograder
--- -----------------------
tag1 = 21923
tag2 = 44437
tag3 = 24929

--- Problems
--- ========

--- Recursion
--- ---------

--- ### mytake

mytake :: Int -> [a] -> [a]
mytake n [] = []
mytake n (x:xs)
    | n <= 0 = []
    | otherwise = x : mytake (n - 1) xs

--- ### mydrop

mydrop :: Int -> [a] -> [a]
mydrop n [] = []
mydrop n (x:xs)
    | n > 0 = mydrop (n - 1) xs
    | otherwise = (x:xs)

--- ### rev

rev :: [a] -> [a]
rev [] = []
rev xx = aux xx []
    where aux [] list = list
          aux (x:xs) list = aux xs (x:list)

--- ### app

app :: [a] -> [a] -> [a]
app [] y = y
app (x:xs) ys = x : app xs ys

--- ### inclist

inclist :: Num a => [a] -> [a]
inclist [] = []
inclist (x:xs) = (x + 1) : inclist xs

--- ### sumlist

sumlist xx = aux xx 0
    where aux [] a = a
          aux (x:xs) a = aux xs (a + x)

--- ### myzip

myzip :: [a] -> [b] -> [(a,b)]
myzip xx [] = []
myzip [] yy = []
myzip (x:xs) (y:ys) = (x, y) : myzip xs ys

--- ### addpairs

addpairs :: (Num a) => [a] -> [a] -> [a]
addpairs xx yy =
    let
        zipped = myzip xx yy
    in
        aux zipped []
            where aux [] list = list
                  aux ((x, y):xs) list = (x + y) : aux xs list

--- ### ones

ones :: [Integer]
ones = 1 : ones

--- ### nats

nats = aux 0
    where aux x = x : aux (x + 1)

--- ### fib

fib :: [Integer]
fib = aux 0 1
    where aux x y = x : aux y (x + y)

--- Set Theory
--- ----------

--- ### add

add :: Ord a => a -> [a] -> [a]
add n [] = [n]
add n (x:xs)
    | n == x = n : xs
    | n < x = n : x : xs
    | otherwise = x : add n xs

--- ### union

union :: Ord a => [a] -> [a] -> [a]
union xx [] = xx
union [] yy = yy
union (x:xs) (y:ys)
    | x < y = x : union xs (y:ys)
    | x == y = x : union xs ys
    | x > y = y : union (x:xs) ys

--- ### intersect

intersect :: Ord a => [a] -> [a] -> [a]
intersect xx [] = []
intersect [] yy = []
intersect (x:xs) (y:ys)
    | x < y = intersect xs (y:ys)
    | x == y = x : intersect xs ys
    | x > y = intersect (x:xs) ys

--- ### powerset

powerset :: Ord a => [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) =
    let
        subsets = powerset xs
        added = [add x s | s <- subsets]
    in
        union subsets added

--- Higher Order Functions
--- ----------------------

--- ### inclist'

inclist' :: Num a => [a] -> [a]
inclist' = P.map (+1)

--- ### sumlist'

sumlist' :: (Num a) => [a] -> a
sumlist' = P.foldl (+) 0
