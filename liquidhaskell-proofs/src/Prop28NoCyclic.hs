{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_28_no_cyclic: (cyclegg_elem cyclegg_x (cyclegg_append cyclegg_xs (Cyclegg_Cons cyclegg_x Cyclegg_Nil))) = Cyclegg_True
module Prop28NoCyclic where
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

{-@ reflect cyclegg_elem @-}
cyclegg_elem :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Bool)
cyclegg_elem n Cyclegg_Nil = Cyclegg_False
cyclegg_elem n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) Cyclegg_True (cyclegg_elem n xs))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ prop_28_no_cyclic :: cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_elem cyclegg_x (cyclegg_append cyclegg_xs (Cyclegg_Cons cyclegg_x Cyclegg_Nil))) = Cyclegg_True } @-}
prop_28_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_28_no_cyclic cyclegg_x cyclegg_xs =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_70) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121) ->
          let g_34 = (cyclegg_eq (Cyclegg_S cyclegg_x_70) cyclegg_xs_120) in
            case g_34 of
              (Cyclegg_False ) ->
                -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121) =>
                -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121):g_34=Cyclegg_False =>
                prop_28_no_cyclic cyclegg_xs_120 cyclegg_xs_121
                -- <= ih-equality-cyclegg_x=cyclegg_xs_120,cyclegg_xs=cyclegg_xs_121
                ? prop_28_no_cyclic cyclegg_x cyclegg_xs_121
                -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_121 =>
                ? prop_28_no_cyclic cyclegg_xs_120 cyclegg_xs_121
                -- <= ih-equality-cyclegg_x=cyclegg_xs_120,cyclegg_xs=cyclegg_xs_121
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                ? prop_28_no_cyclic cyclegg_xs_120 cyclegg_xs_121
                -- ih-equality-cyclegg_x=cyclegg_xs_120,cyclegg_xs=cyclegg_xs_121 =>
              (Cyclegg_True ) ->
                -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121) =>
                -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_120 cyclegg_xs_121):g_34=Cyclegg_True =>
                prop_28_no_cyclic cyclegg_xs_120 cyclegg_xs_121
                -- <= ih-equality-cyclegg_x=cyclegg_xs_120,cyclegg_xs=cyclegg_xs_121
                ? prop_28_no_cyclic cyclegg_x cyclegg_xs_121
                -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_121 =>
                ? prop_28_no_cyclic cyclegg_xs_120 cyclegg_xs_121
                -- <= ih-equality-cyclegg_x=cyclegg_xs_120,cyclegg_xs=cyclegg_xs_121
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                ? prop_28_no_cyclic cyclegg_xs_120 cyclegg_xs_121
                -- ih-equality-cyclegg_x=cyclegg_xs_120,cyclegg_xs=cyclegg_xs_121 =>
        (Cyclegg_Nil ) ->
          -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- <= prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=Cyclegg_Nil
          -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
          -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
          -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
          -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_elem ?n Cyclegg_Nil) =>
          -- <= (cyclegg_elem ?n Cyclegg_Nil)
          -- <= prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=Cyclegg_Nil
          -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
          -- prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=Cyclegg_Nil =>
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= prop_28_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_xs=Cyclegg_Nil
          prop_28_no_cyclic cyclegg_x_70 cyclegg_xs
          -- ih-equality-cyclegg_x=cyclegg_x_70,cyclegg_xs=cyclegg_xs =>
    (Cyclegg_Z ) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) ->
          let g_29 = (cyclegg_eq cyclegg_xs_80 cyclegg_xs_80) in
            case g_29 of
              (Cyclegg_False ) ->
                let g_26 = (cyclegg_eq Cyclegg_Z cyclegg_xs_80) in
                  case g_26 of
                    (Cyclegg_False ) ->
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_29=Cyclegg_False:g_26=Cyclegg_False =>
                      prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      ? prop_28_no_cyclic cyclegg_x cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_81 =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81 =>
                    (Cyclegg_True ) ->
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_29=Cyclegg_False:g_26=Cyclegg_True =>
                      prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      ? prop_28_no_cyclic cyclegg_x cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_81 =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81 =>
              (Cyclegg_True ) ->
                let g_26 = (cyclegg_eq Cyclegg_Z cyclegg_xs_80) in
                  case g_26 of
                    (Cyclegg_False ) ->
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_29=Cyclegg_True:g_26=Cyclegg_False =>
                      prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      ? prop_28_no_cyclic cyclegg_x cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_81 =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81 =>
                    (Cyclegg_True ) ->
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
                      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_29=Cyclegg_True:g_26=Cyclegg_True =>
                      prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      ? prop_28_no_cyclic cyclegg_x cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_81 =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- <= ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      ? prop_28_no_cyclic cyclegg_xs_80 cyclegg_xs_81
                      -- ih-equality-cyclegg_x=cyclegg_xs_80,cyclegg_xs=cyclegg_xs_81 =>
        (Cyclegg_Nil ) ->
          -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- <= prop_28_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
          -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
          -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
          -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
          -- <= prop_28_no_cyclic:cyclegg_x=Cyclegg_Z
          -- <= prop_28_no_cyclic:cyclegg_x=Cyclegg_Z
          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
          -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- prop_28_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
          ()

