module ExerciseOne

import Data.Vect

%default tOtal

-- | Ex1
-- | Write a function:
-- | > repeat : (n : Nat) -> a -> Vect n a
-- | which constructs a vector of n copies of an item.

repeat : (n : Nat) -> a -> Vect n a
repeat Z     _ = []
repeat (S k) e = e :: repeat k e

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

-- 3. A matrix is a 2-dimensional vector, and could be defined as follows:
--     Matrix : Type -> Nat -> Nat -> Type
--     Matrix a n m = Vect (Vect a m) n
-- (a) Using repeat, above, and Vect.zipWith, write a function which transposes a matrix.
-- Hints: Remember to think carefully about its type first! zipWith for vectors is defined as follows:
--         zipWith : (a -> b -> c) -> Vect a n -> Vect b n -> Vect c n
--         zipWith f []      []      = []
--         zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys
-- (b) Write a function to multiply two matrices.
