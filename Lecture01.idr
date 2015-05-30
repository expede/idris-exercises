module ExerciseOne

import Data.Vect

%default total

-- | Ex1
-- | Write a function:
-- | > repeat : (n : Nat) -> a -> Vect n a
-- | which constructs a vector of n copies of an item.

repeat : (n : Nat) -> a -> Vect n a
repeat Z     _ = []
repeat (S k) e = e :: repeat k e

--------------------------------------------------------------------------------
-- 2. Consider the following functions over Lists:
--     take : Nat -> List a -> List a
--     drop : Nat -> List a -> List a
-- (a) What are the types of the corresponding functions for Vect, vtake and vdrop?
-- Hint: What are the invariants? i.e. how many items need to be in the vector in each case?
-- (b) Implement vtake and vdrop

-- | A. Types for Vect, vtake and vdrop
vtake : (n : Nat) -> Vect (n + m) t -> Vect n t
vtake Z     _         = []
vtake (S k) (x :: xs) = x :: vtake k xs

vdrop : (n : Nat) -> Vect (n + m) t -> Vect m t
vdrop Z     xs        = xs
vdrop (S k) (x :: xs) = vdrop k xs

--------------------------------------------------------------------------------
-- 3. A matrix is a 2-dimensional vector, and could be defined as follows:
Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

-- (a) Using repeat, above, and Vect.zipWith, write a function which transposes a matrix.
-- Hints: Remember to think carefully about its type first! zipWith for vectors is defined as follows:
--         zipWith : (a -> b -> c) -> Vect a n -> Vect b n -> Vect c n
--         zipWith f []      []      = []
--         zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys
transpose' : Matrix x y t -> Matrix y x t
transpose' {x = Z} []      = repeat _ []
transpose'         (x::xs) = zipWith (::) x (transpose' xs)

-- (b) Write a function to multiply two matrices.
matX : Num t => Matrix x y t -> Matrix y z t -> Matrix x z t
matX []    _  = []
matX (x::xs) ys = (map (sum . zipWith (*) x) $ transpose' ys) :: (matX xs ys)

--------------------------------------------------------------------------------
-- 4. The following view describes a pair of numbers as a difference:
data Cmp : Nat -> Nat -> Type where
  cmpLT : (y : _) -> Cmp x (x + S y)
  cmpEQ : Cmp x x
  cmpGT : (x : _) -> Cmp (y + S x) y

-- (a) Write the function cmp : (n : Nat) -> (m : Nat) -> Cmp n m
--   which proves that every pair of numbers can be expressed in this way.
-- Hint: recall parity from the lecture. You will find the with construct very useful!
cmp' : (n : Nat) -> (m : Nat) -> Cmp n m
cmp'  Z     Z    = cmpEQ {x = Z}
cmp'  Z    (S k) = cmpLT k
cmp' (S k)  Z    = cmpGT k
cmp' (S k) (S j) with (cmp' k j)
  cmp' (S k) (S k) | cmpEQ = cmpEQ {x = S k}
  cmp' (S k) (S (k + S h)) | cmpLT h = cmpLT h
  cmp' (S (j + S h)) (S j) | cmpGT h = cmpGT h

-- (b) Assume you have a vector xs : Vect a n, where n is unknown.
--   How could you use cmp to construct a suitable input to vtake and vdrop from xs?

-- >>> Huh? What is this even asking?

--------------------------------------------------------------------------------
-- 5. Implement the following functions:
--   plus_nSm : (n : Nat) -> (m : Nat) -> n + S m = S (n + m)
--   plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
--   plus_assoc : (n : Nat) -> (m : Nat) -> (p : Nat) ->
--                n + (m + p) = (n + m) + p

--------------------------------------------------------------------------------
-- 6. One way to define a reverse function for lists is as follows:
--   reverse : List a -> List a
--   reverse xs = revAcc [] xs where
--     revAcc : List a -> List a -> List a
--     revAcc acc [] = acc
--     revAcc acc (x :: xs) = revAcc (x :: acc) xs
-- Write the equivalent function for vectors, vect reverse : Vect a
-- n ->
-- Hint: You can use the same structure as the definition for List, but you will need to think carefully
-- Vect a n
-- about the type for revAcc, and may need to do some theorem proving.

--------------------------------------------------------------------------------
-- 7. You are given the following definition of binary trees:
-- data Tree a = Leaf | Node (Tree a) a (Tree a)
-- Define a membership predicate ElemTree and a function elemInTree which calculates whether a
-- value in in the tree, and a corresponding proof.
--     data ElemTree  : a -> Tree a -> Type where ...
--     elemInTree : DecEq a =>
--                  (x : a) -> (t : Tree a) -> Maybe (ElemTree x t)
