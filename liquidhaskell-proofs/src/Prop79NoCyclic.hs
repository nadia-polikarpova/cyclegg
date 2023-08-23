{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_79_no_cyclic: (cyclegg_sub (cyclegg_sub (Cyclegg_S cyclegg_m) cyclegg_n) (Cyclegg_S cyclegg_k)) = (cyclegg_sub (cyclegg_sub cyclegg_m cyclegg_n) cyclegg_k)
module Prop79NoCyclic where
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

{-@ reflect cyclegg_sub @-}
cyclegg_sub :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_sub x Cyclegg_Z = x
cyclegg_sub Cyclegg_Z y = Cyclegg_Z
cyclegg_sub (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_sub x y)

{-@ prop_79_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_k: Cyclegg_Nat -> { (cyclegg_sub (cyclegg_sub (Cyclegg_S cyclegg_m) cyclegg_n) (Cyclegg_S cyclegg_k)) = (cyclegg_sub (cyclegg_sub cyclegg_m cyclegg_n) cyclegg_k) } @-}
prop_79_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat -> Proof
prop_79_no_cyclic cyclegg_n cyclegg_m cyclegg_k =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_90) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_160) ->
          -- prop_79_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_90) =>
          -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- prop_79_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_90):cyclegg_m=(Cyclegg_S cyclegg_m_160) =>
          prop_79_no_cyclic cyclegg_n_90 cyclegg_m_160 cyclegg_k
          -- ih-equality-cyclegg_n=cyclegg_n_90,cyclegg_m=cyclegg_m_160,cyclegg_k=cyclegg_k =>
          -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= prop_79_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_90)
          -- <= prop_79_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_90):cyclegg_m=(Cyclegg_S cyclegg_m_160)
        (Cyclegg_Z ) ->
          (cyclegg_sub (cyclegg_sub (Cyclegg_S cyclegg_m) cyclegg_n) (Cyclegg_S cyclegg_k))
          -- prop_79_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_90) =>
          ==. (cyclegg_sub (cyclegg_sub (Cyclegg_S cyclegg_m) (Cyclegg_S cyclegg_n_90)) (Cyclegg_S cyclegg_k))
          -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          ==. (cyclegg_sub (cyclegg_sub cyclegg_m cyclegg_n_90) (Cyclegg_S cyclegg_k))
          -- prop_79_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_90):cyclegg_m=Cyclegg_Z =>
          ==. (cyclegg_sub (cyclegg_sub Cyclegg_Z cyclegg_n_90) (Cyclegg_S cyclegg_k))
          -- (cyclegg_sub Cyclegg_Z ?y) =>
          ==. (cyclegg_sub Cyclegg_Z (Cyclegg_S cyclegg_k))
          -- (cyclegg_sub Cyclegg_Z ?y) =>
          ==. Cyclegg_Z
          -- <= (cyclegg_sub Cyclegg_Z ?y)
          ==. (cyclegg_sub Cyclegg_Z cyclegg_k)
          -- <= (cyclegg_sub Cyclegg_Z ?y)
          ==. (cyclegg_sub (cyclegg_sub Cyclegg_Z cyclegg_n) cyclegg_k)
          -- <= prop_79_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_90):cyclegg_m=Cyclegg_Z
          ==. (cyclegg_sub (cyclegg_sub cyclegg_m cyclegg_n) cyclegg_k)
          ***
          QED
    (Cyclegg_Z ) ->
      -- prop_79_no_cyclic:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_sub ?x Cyclegg_Z) =>
      -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
      -- <= (cyclegg_sub ?x Cyclegg_Z)
      -- <= prop_79_no_cyclic:cyclegg_n=Cyclegg_Z
      ()

