--- Getting Started
--- ===============

--- Relevant Files
--- --------------

module Lib where

--- Metadata for autograder
--- -----------------------
tag1 = 21923
tag2 = 44437
tag3 = 24929

--- Problems
--- ========

--- Algebraic Data Types
--- --------------------

data List a = Cons a (List a)
            | Nil
  deriving (Show, Eq)

data Exp = IntExp Integer
         | PlusExp [Exp]
         | MultExp [Exp]
  deriving (Show, Eq)

--- ### list2cons

list2cons :: [a] -> List a
list2cons [] = Nil
list2cons (x:xs) = Cons x (list2cons xs)

--- ### cons2list

cons2list :: List a -> [a]
cons2list Nil = []
cons2list (Cons x xs) = x : cons2list xs

--- ### eval

eval :: Exp -> Integer
eval (IntExp int) = int
eval (PlusExp exp)
    | exp == [] = 0
    | otherwise = sum (map eval exp)
eval (MultExp exp)
    | exp == [] = 1
    | otherwise = product (map eval exp)

--- ### list2cons'

list2cons' :: [a] -> List a
list2cons' = foldr Cons Nil

--- ### BinTree

-- BinTree
data BinTree a = Node a (BinTree a) (BinTree a)
               | Leaf
  deriving (Show)

--- ### sumTree

sumTree :: Num a => BinTree a -> a
sumTree Leaf = 0
sumTree (Node val left right) = val + sumTree left + sumTree right

--- ### SimpVal

-- SimpVal
data SimpVal = IntVal Integer
             | BoolVal Bool
             | StrVal String
             | ExnVal String
  deriving (Show)

--- ### liftIntOp

liftIntOp :: (Integer -> Integer -> Integer) -> SimpVal -> SimpVal -> SimpVal
liftIntOp op (IntVal x) (IntVal y) = IntVal (op x y)
liftIntOp _ _ _ = ExnVal "not an IntVal!"
