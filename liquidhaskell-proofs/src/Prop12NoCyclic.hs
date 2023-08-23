{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_12_no_cyclic: (cyclegg_drop cyclegg_n (cyclegg_map cyclegg_f cyclegg_xs)) = (cyclegg_map cyclegg_f (cyclegg_drop cyclegg_n cyclegg_xs))
module Prop12NoCyclic where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_Expr @-}
data Cyclegg_Expr cyclegg_a where
  Cyclegg_MkExpr :: ((Cyclegg_Tm cyclegg_a) -> Cyclegg_Nat -> (Cyclegg_Expr cyclegg_a))

{-@ autosize Cyclegg_Tree @-}
data Cyclegg_Tree cyclegg_a where
  Cyclegg_Leaf :: (Cyclegg_Tree cyclegg_a)
  Cyclegg_Node :: ((Cyclegg_Tree cyclegg_a) -> cyclegg_a -> (Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))

{-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

{-@ autosize Cyclegg_Tm @-}
data Cyclegg_Tm cyclegg_a where
  Cyclegg_Var :: (cyclegg_a -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_Cst :: (Cyclegg_Nat -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_App :: ((Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Tm cyclegg_a))

{-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

{-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ reflect cyclegg_map @-}
cyclegg_map :: ((cyclegg_a -> cyclegg_b) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_b))
cyclegg_map f Cyclegg_Nil = Cyclegg_Nil
cyclegg_map f (Cyclegg_Cons x xs) = (Cyclegg_Cons (($) f x) (cyclegg_map f xs))

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ prop_12_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_f: (cyclegg_a -> cyclegg_b) -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_drop cyclegg_n (cyclegg_map cyclegg_f cyclegg_xs)) = (cyclegg_map cyclegg_f (cyclegg_drop cyclegg_n cyclegg_xs)) } @-}
prop_12_no_cyclic :: Cyclegg_Nat -> (cyclegg_a -> cyclegg_b) -> (Cyclegg_List cyclegg_a) -> Proof
prop_12_no_cyclic cyclegg_n cyclegg_f cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_70) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121) ->
          -- prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
          -- prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121) =>
          -- (cyclegg_map ?f (Cyclegg_Cons ?x ?xs)) =>
          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
          prop_12_no_cyclic cyclegg_n_70 cyclegg_f cyclegg_xs_121
          -- ih-equality-cyclegg_n=cyclegg_n_70,cyclegg_f=cyclegg_f,cyclegg_xs=cyclegg_xs_121 =>
          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
          -- <= prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
          -- <= prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121)
        (Cyclegg_Nil ) ->
          -- prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
          -- prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_map ?f Cyclegg_Nil) =>
          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
          -- <= (cyclegg_map ?f Cyclegg_Nil)
          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
          -- <= prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
          -- <= prop_12_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_xs=Cyclegg_Nil
          ()
    (Cyclegg_Z ) ->
      -- prop_12_no_cyclic:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_drop Cyclegg_Z ?xs) =>
      -- <= (cyclegg_drop Cyclegg_Z ?xs)
      -- <= prop_12_no_cyclic:cyclegg_n=Cyclegg_Z
      ()

