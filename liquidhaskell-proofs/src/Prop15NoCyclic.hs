{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_15_no_cyclic: (cyclegg_len (cyclegg_ins cyclegg_x cyclegg_xs)) = (Cyclegg_S (cyclegg_len cyclegg_xs))
module Prop15NoCyclic where
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

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_ins @-}
cyclegg_ins :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_ins n Cyclegg_Nil = (Cyclegg_Cons n Cyclegg_Nil)
cyclegg_ins n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_lt n x) (Cyclegg_Cons n (Cyclegg_Cons x xs)) (Cyclegg_Cons x (cyclegg_ins n xs)))

{-@ reflect cyclegg_lt @-}
cyclegg_lt :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_lt x Cyclegg_Z = Cyclegg_False
cyclegg_lt Cyclegg_Z (Cyclegg_S y) = Cyclegg_True
cyclegg_lt (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_lt x y)

{-@ prop_15_no_cyclic :: cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_len (cyclegg_ins cyclegg_x cyclegg_xs)) = (Cyclegg_S (cyclegg_len cyclegg_xs)) } @-}
prop_15_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_15_no_cyclic cyclegg_x cyclegg_xs =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_60) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) ->
          let g_27 = (cyclegg_lt cyclegg_xs_100 cyclegg_xs_100) in
            case g_27 of
              (Cyclegg_False ) ->
                let g_37 = (cyclegg_lt cyclegg_x_60 cyclegg_xs_100) in
                  case g_37 of
                    (Cyclegg_False ) ->
                      let g_32 = (cyclegg_lt (Cyclegg_S cyclegg_x_60) cyclegg_xs_100) in
                        case g_32 of
                          (Cyclegg_False ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_False:g_37=Cyclegg_False:g_32=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            prop_15_no_cyclic cyclegg_x cyclegg_xs_101
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_101 =>
                            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                          (Cyclegg_True ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_False:g_37=Cyclegg_False:g_32=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            ()
                    (Cyclegg_True ) ->
                      let g_32 = (cyclegg_lt (Cyclegg_S cyclegg_x_60) cyclegg_xs_100) in
                        case g_32 of
                          (Cyclegg_False ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_False:g_37=Cyclegg_True:g_32=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            prop_15_no_cyclic cyclegg_x cyclegg_xs_101
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_101 =>
                            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                          (Cyclegg_True ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_False:g_37=Cyclegg_True:g_32=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            ()
              (Cyclegg_True ) ->
                let g_37 = (cyclegg_lt cyclegg_x_60 cyclegg_xs_100) in
                  case g_37 of
                    (Cyclegg_False ) ->
                      let g_32 = (cyclegg_lt (Cyclegg_S cyclegg_x_60) cyclegg_xs_100) in
                        case g_32 of
                          (Cyclegg_False ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_True:g_37=Cyclegg_False:g_32=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            prop_15_no_cyclic cyclegg_x cyclegg_xs_101
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_101 =>
                            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                          (Cyclegg_True ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_True:g_37=Cyclegg_False:g_32=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            ()
                    (Cyclegg_True ) ->
                      let g_32 = (cyclegg_lt (Cyclegg_S cyclegg_x_60) cyclegg_xs_100) in
                        case g_32 of
                          (Cyclegg_False ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_True:g_37=Cyclegg_True:g_32=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            prop_15_no_cyclic cyclegg_x cyclegg_xs_101
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_101 =>
                            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                          (Cyclegg_True ) ->
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101) =>
                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101):g_27=Cyclegg_True:g_37=Cyclegg_True:g_32=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_100 cyclegg_xs_101)
                            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                            ()
        (Cyclegg_Nil ) ->
          -- prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_ins ?n Cyclegg_Nil) =>
          -- <= prop_15_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=Cyclegg_Nil
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          ()
    (Cyclegg_Z ) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) ->
          let g_22 = (cyclegg_lt cyclegg_xs_70 cyclegg_xs_70) in
            case g_22 of
              (Cyclegg_False ) ->
                let g_27 = (cyclegg_lt Cyclegg_Z cyclegg_xs_70) in
                  case g_27 of
                    (Cyclegg_False ) ->
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_22=Cyclegg_False:g_27=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                      prop_15_no_cyclic cyclegg_x cyclegg_xs_71
                      -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_71 =>
                      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
                      -- <= prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71)
                    (Cyclegg_True ) ->
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_22=Cyclegg_False:g_27=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- <= prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71)
                      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                      ()
              (Cyclegg_True ) ->
                let g_27 = (cyclegg_lt Cyclegg_Z cyclegg_xs_70) in
                  case g_27 of
                    (Cyclegg_False ) ->
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_22=Cyclegg_True:g_27=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                      prop_15_no_cyclic cyclegg_x cyclegg_xs_71
                      -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_71 =>
                      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
                      -- <= prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71)
                    (Cyclegg_True ) ->
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                      -- add guard scrutinee =>
                      -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_22=Cyclegg_True:g_27=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- <= prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71)
                      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                      ()
        (Cyclegg_Nil ) ->
          -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- <= (cyclegg_len Cyclegg_Nil)
          -- <= prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
          -- prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_ins ?n Cyclegg_Nil) =>
          -- <= prop_15_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          ()

