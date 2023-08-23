{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_03_no_cyclic: (cyclegg_leq (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys))) = Cyclegg_True
module Prop03NoCyclic where
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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_leq @-}
cyclegg_leq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_leq Cyclegg_Z y = Cyclegg_True
cyclegg_leq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_leq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_leq x y)

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ prop_03_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> cyclegg_ys: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_leq (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys))) = Cyclegg_True } @-}
prop_03_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_03_no_cyclic cyclegg_n cyclegg_xs cyclegg_ys =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_80) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) ->
          let g_33 = (cyclegg_eq cyclegg_n_80 cyclegg_xs_130) in
            case g_33 of
              (Cyclegg_False ) ->
                let g_29 = (cyclegg_eq (Cyclegg_S cyclegg_n_80) cyclegg_xs_130) in
                  case g_29 of
                    (Cyclegg_False ) ->
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_False:g_29=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_False:g_29=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      prop_03_no_cyclic cyclegg_n cyclegg_xs_131 cyclegg_ys
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_131,cyclegg_ys=cyclegg_ys =>
                    (Cyclegg_True ) ->
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_False:g_29=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_False:g_29=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                      prop_03_no_cyclic cyclegg_n cyclegg_xs_131 cyclegg_ys
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_131,cyclegg_ys=cyclegg_ys =>
              (Cyclegg_True ) ->
                let g_29 = (cyclegg_eq (Cyclegg_S cyclegg_n_80) cyclegg_xs_130) in
                  case g_29 of
                    (Cyclegg_False ) ->
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_True:g_29=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_True:g_29=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      prop_03_no_cyclic cyclegg_n cyclegg_xs_131 cyclegg_ys
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_131,cyclegg_ys=cyclegg_ys =>
                    (Cyclegg_True ) ->
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_True:g_29=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):g_33=Cyclegg_True:g_29=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                      prop_03_no_cyclic cyclegg_n cyclegg_xs_131 cyclegg_ys
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_131,cyclegg_ys=cyclegg_ys =>
        (Cyclegg_Nil ) ->
          -- prop_03_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_count ?x Cyclegg_Nil) =>
          -- (cyclegg_leq Cyclegg_Z ?y) =>
          ()
    (Cyclegg_Z ) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) ->
          let g_22 = (cyclegg_eq Cyclegg_Z cyclegg_xs_90) in
            case g_22 of
              (Cyclegg_False ) ->
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_22=Cyclegg_False =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_22=Cyclegg_False =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                prop_03_no_cyclic cyclegg_n cyclegg_xs_91 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_91,cyclegg_ys=cyclegg_ys =>
              (Cyclegg_True ) ->
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_22=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_22=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                prop_03_no_cyclic cyclegg_n cyclegg_xs_91 cyclegg_ys
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_91,cyclegg_ys=cyclegg_ys =>
        (Cyclegg_Nil ) ->
          -- prop_03_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_count ?x Cyclegg_Nil) =>
          -- (cyclegg_leq Cyclegg_Z ?y) =>
          ()

