{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_52_no_cyclic: (count n xs) = (count n (rev1 xs))
module Prop52Manual where
import Language.Haskell.Liquid.Equational hiding (eq)

-- {-@ autosize List @-}
data List a where
  Nil :: (List a)
  Cons :: (a -> (List a) -> (List a))

-- {-@ autosize N @-}
data N where
  Z :: N
  S :: (N -> N)

{-@ reflect eq @-}
eq :: (N -> N -> Bool)
eq Z Z = True
eq Z (S y) = False
eq (S x) Z = False
eq (S x) (S y) = (eq x y)

{-@ reflect append @-}
append :: ((List a) -> (List a) -> (List a))
append Nil ys = ys
append (Cons x xs) ys = (Cons x (append xs ys))

{-@ reflect rev1 @-}
rev1 :: ((List a) -> (List a))
rev1 Nil = Nil
rev1 (Cons x xs) = (append xs (Cons x Nil))

{-@ reflect ite @-}
ite :: (Bool -> a -> a -> a)
ite True x y = x
ite False x y = y

{-@ reflect count @-}
count :: (N -> (List N) -> N)
count x Nil = Z
count x (Cons y ys) = (ite (eq x y) (S (count x ys)) (count x ys))

{-@ type Pos = {v: Int | v >= 1 } @-}

{-@ measure natSize @-}
{-@ natSize :: N -> Pos @-}
natSize :: N -> Int
natSize Z = 1
natSize (S n) = 1 + natSize n

{-@ measure listSum @-}
{-@ listSum :: List N -> Pos @-}
listSum :: List N -> Int
listSum Nil = 1
listSum (Cons n xs) = 1 + natSize n + listSum xs

{-@ prop_52_no_cyclic :: n: N -> xs: (List N) -> { (count n xs) = (count n (rev1 xs)) } / [listSum xs] @-}
prop_52_no_cyclic :: N -> List N -> Proof
prop_52_no_cyclic n xs =
  case xs of
    Nil        -> ()
    Cons y ys ->
      case ys of
        Nil -> ()
        Cons z zs ->
          case eq n z of
            True ->
              count n (append (Cons z zs) (Cons y Nil))
              ==. count n (Cons z (append zs (Cons y Nil)))
              ==. S (count n (append zs (Cons y Nil)))
              ==. S (count n (rev1 (Cons y zs)))
              ? prop_52_no_cyclic n (Cons y zs)
              ==. (case eq n y of
                      True ->
                        S (count n (Cons y zs))
                        ==. S (S (count n zs))
                        ==. S (count n (Cons z zs))
                        ==. count n (Cons y (Cons z zs))
                      False ->
                        S (count n (Cons y zs))
                        ==. S (count n zs)
                        ==. count n (Cons z zs)
                        ==. count n (Cons y (Cons z zs))
              )
              *** QED
            False ->
              count n (append (Cons z zs) (Cons y Nil))
              ==. count n (Cons z (append zs (Cons y Nil)))
              ==. count n (append zs (Cons y Nil))
              ==. count n (rev1 (Cons y zs))
              ? prop_52_no_cyclic n (Cons y zs)
              ==. (case eq n y of
                      True ->
                        count n (Cons y zs)
                        ==. S (count n zs)
                        ==. S (count n (Cons z zs))
                        ==. count n (Cons y (Cons z zs))
                      False ->
                        count n (Cons y zs)
                        ==. count n zs
                        ==. count n (Cons z zs)
                        ==. count n (Cons y (Cons z zs))
              )
              *** QED
