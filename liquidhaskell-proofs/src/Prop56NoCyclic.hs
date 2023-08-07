{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_56_no_cyclic: (cyclegg_drop cyclegg_n (cyclegg_drop cyclegg_m cyclegg_xs)) = (cyclegg_drop (cyclegg_add cyclegg_n cyclegg_m) cyclegg_xs)
module Prop56NoCyclic where
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

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ prop_56_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_drop cyclegg_n (cyclegg_drop cyclegg_m cyclegg_xs)) = (cyclegg_drop (cyclegg_add cyclegg_n cyclegg_m) cyclegg_xs) } @-}
prop_56_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
prop_56_no_cyclic cyclegg_n cyclegg_m cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_70) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_130) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) ->
              case cyclegg_n_70 of
                (Cyclegg_S cyclegg_n_70_360) ->
                  case cyclegg_m_130 of
                    (Cyclegg_S cyclegg_m_130_580) ->
                      case cyclegg_xs_231 of
                        (Cyclegg_Cons cyclegg_xs_231_960 cyclegg_xs_231_961) ->
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          prop_56_no_cyclic cyclegg_n cyclegg_m_130 cyclegg_xs_231
                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_130,cyclegg_xs=cyclegg_xs_231 =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
                          -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=(Cyclegg_S cyclegg_m_130_580):cyclegg_xs_231=(Cyclegg_Cons cyclegg_xs_231_960 cyclegg_xs_231_961) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          ? prop_56_no_cyclic cyclegg_n_70 cyclegg_m_130 cyclegg_xs_231_961
                          -- <= ih-equality-cyclegg_n=cyclegg_n_70,cyclegg_m=cyclegg_m_130,cyclegg_xs=cyclegg_xs_231_961
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=(Cyclegg_S cyclegg_m_130_580):cyclegg_xs_231=(Cyclegg_Cons cyclegg_xs_231_960 cyclegg_xs_231_961)
                          ? prop_56_no_cyclic cyclegg_n_70 cyclegg_m cyclegg_xs_231
                          -- ih-equality-cyclegg_n=cyclegg_n_70,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_231 =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231)
                        (Cyclegg_Nil ) ->
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          prop_56_no_cyclic cyclegg_n cyclegg_m_130 cyclegg_xs_231
                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_130,cyclegg_xs=cyclegg_xs_231 =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
                          -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=(Cyclegg_S cyclegg_m_130_580):cyclegg_xs_231=Cyclegg_Nil =>
                          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=(Cyclegg_S cyclegg_m_130_580):cyclegg_xs_231=Cyclegg_Nil
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231)
                    (Cyclegg_Z ) ->
                      case cyclegg_xs_231 of
                        (Cyclegg_Cons cyclegg_xs_231_650 cyclegg_xs_231_651) ->
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          prop_56_no_cyclic cyclegg_n cyclegg_m_130 cyclegg_xs_231
                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_130,cyclegg_xs=cyclegg_xs_231 =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
                          -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=Cyclegg_Z:cyclegg_xs_231=(Cyclegg_Cons cyclegg_xs_231_650 cyclegg_xs_231_651) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          ? prop_56_no_cyclic cyclegg_n_70 cyclegg_m_130 cyclegg_xs_231_651
                          -- <= ih-equality-cyclegg_n=cyclegg_n_70,cyclegg_m=cyclegg_m_130,cyclegg_xs=cyclegg_xs_231_651
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=Cyclegg_Z:cyclegg_xs_231=(Cyclegg_Cons cyclegg_xs_231_650 cyclegg_xs_231_651)
                          ? prop_56_no_cyclic cyclegg_n_70 cyclegg_m cyclegg_xs_231
                          -- ih-equality-cyclegg_n=cyclegg_n_70,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_231 =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231)
                        (Cyclegg_Nil ) ->
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=Cyclegg_Z =>
                          -- (cyclegg_drop Cyclegg_Z ?xs) =>
                          -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=Cyclegg_Z:cyclegg_xs_231=Cyclegg_Nil =>
                          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360):cyclegg_m_130=Cyclegg_Z:cyclegg_xs_231=Cyclegg_Nil
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=(Cyclegg_S cyclegg_n_70_360)
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
                          -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231)
                          ()
                (Cyclegg_Z ) ->
                  -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130) =>
                  -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                  prop_56_no_cyclic cyclegg_n cyclegg_m_130 cyclegg_xs_231
                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_130,cyclegg_xs=cyclegg_xs_231 =>
                  -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
                  -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                  -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=Cyclegg_Z =>
                  -- (cyclegg_add Cyclegg_Z ?y) =>
                  -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130)
                  -- <= (cyclegg_add Cyclegg_Z ?y)
                  -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231):cyclegg_n_70=Cyclegg_Z
                  -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                  -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                  -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
                  -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231)
            (Cyclegg_Nil ) ->
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130) =>
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
              -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
              -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=Cyclegg_Nil
              ()
        (Cyclegg_Z ) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161) ->
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z
              prop_56_no_cyclic cyclegg_n_70 cyclegg_m cyclegg_xs_161
              -- ih-equality-cyclegg_n=cyclegg_n_70,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_161 =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
              -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
              -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161)
            (Cyclegg_Nil ) ->
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
              -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70)
              -- <= prop_56_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
              ()
    (Cyclegg_Z ) ->
      -- prop_56_no_cyclic:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_drop Cyclegg_Z ?xs) =>
      -- <= (cyclegg_add Cyclegg_Z ?y)
      -- <= prop_56_no_cyclic:cyclegg_n=Cyclegg_Z
      ()

