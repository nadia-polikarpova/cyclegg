{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_02_no_cyclic: (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n cyclegg_ys)) = (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys))
module Prop02NoCyclic where
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

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ prop_02_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> cyclegg_ys: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n cyclegg_ys)) = (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys)) } @-}
prop_02_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_02_no_cyclic cyclegg_n cyclegg_xs cyclegg_ys =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_80) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) ->
          let g_31 = (cyclegg_eq (Cyclegg_S cyclegg_n_80) cyclegg_xs_140) in
            case g_31 of
              (Cyclegg_False ) ->
                -- prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_31=Cyclegg_False =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                -- <= prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_31=Cyclegg_False
                -- <= add guard scrutinee
                prop_02_no_cyclic cyclegg_n cyclegg_xs_141 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_141,cyclegg_ys=cyclegg_ys =>
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                -- <= prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
              (Cyclegg_True ) ->
                -- prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_31=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                prop_02_no_cyclic cyclegg_n cyclegg_xs_141 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_141,cyclegg_ys=cyclegg_ys =>
                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                -- <= prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_31=Cyclegg_True
                -- <= add guard scrutinee
                ? prop_02_no_cyclic cyclegg_n cyclegg_xs_141 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_141,cyclegg_ys=cyclegg_ys =>
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                -- <= prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
        (Cyclegg_Nil ) ->
          -- prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_count ?x Cyclegg_Nil) =>
          -- (cyclegg_add Cyclegg_Z ?y) =>
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= prop_02_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=Cyclegg_Nil
          ()
    (Cyclegg_Z ) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) ->
          let g_23 = (cyclegg_eq Cyclegg_Z cyclegg_xs_90) in
            case g_23 of
              (Cyclegg_False ) ->
                -- prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                -- <= prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False
                -- <= add guard scrutinee
                prop_02_no_cyclic cyclegg_n cyclegg_xs_91 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_91,cyclegg_ys=cyclegg_ys =>
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                -- <= prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
              (Cyclegg_True ) ->
                -- prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                prop_02_no_cyclic cyclegg_n cyclegg_xs_91 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_91,cyclegg_ys=cyclegg_ys =>
                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                -- <= prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                -- <= add guard scrutinee
                ? prop_02_no_cyclic cyclegg_n cyclegg_xs_91 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_91,cyclegg_ys=cyclegg_ys =>
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                -- <= prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
        (Cyclegg_Nil ) ->
          -- prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_count ?x Cyclegg_Nil) =>
          -- (cyclegg_add Cyclegg_Z ?y) =>
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= prop_02_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
          ()

