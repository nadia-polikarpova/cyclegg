{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_86_no_cyclic: (cyclegg_mapE cyclegg_id cyclegg_e) = cyclegg_e
module Prop86NoCyclic where
import Language.Haskell.Liquid.Equational

-- {-@ autosize Cyclegg_Expr @-}
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

-- {-@ autosize Cyclegg_Tm @-}
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

{-@ lazy tmSize @-}
{-@ measure tmSize @-}
{-@ tmSize :: Cyclegg_Tm a -> Nat @-}
tmSize :: Cyclegg_Tm a -> Int
tmSize (Cyclegg_Var _) = 0
tmSize (Cyclegg_Cst _) = 0
tmSize (Cyclegg_App e1 e2) = 1 + eSize e1 + eSize e2

{-@ lazy eSize @-}
{-@ measure eSize @-}
{-@ eSize :: Cyclegg_Expr a -> Nat @-}
eSize :: Cyclegg_Expr a -> Int
eSize (Cyclegg_MkExpr t _n) = 1 + tmSize t

{-@ reflect cyclegg_mapT @-}
{-@ cyclegg_mapT :: f: (a -> b) -> x: (Cyclegg_Tm a) -> (Cyclegg_Tm b) / [tmSize x] @-}
cyclegg_mapT :: ((cyclegg_a -> cyclegg_b) -> (Cyclegg_Tm cyclegg_a) -> (Cyclegg_Tm cyclegg_b))
cyclegg_mapT f (Cyclegg_Var x) = (Cyclegg_Var (f x))
cyclegg_mapT f (Cyclegg_Cst n) = (Cyclegg_Cst n)
cyclegg_mapT f (Cyclegg_App e1 e2) = (Cyclegg_App (cyclegg_mapE f e1) (cyclegg_mapE f e2))

{-@ reflect cyclegg_mapE @-}
{-@ cyclegg_mapE :: f: (a -> b) -> x: (Cyclegg_Expr a) -> (Cyclegg_Expr b) / [eSize x] @-}
cyclegg_mapE :: ((cyclegg_a -> cyclegg_b) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_b))
cyclegg_mapE f (Cyclegg_MkExpr t n) = (Cyclegg_MkExpr (cyclegg_mapT f t) n)

{-@ reflect cyclegg_id @-}
cyclegg_id :: (cyclegg_a -> cyclegg_a)
cyclegg_id x = x

{-@ prop_86_no_cyclic :: cyclegg_e: (Cyclegg_Expr cyclegg_a) -> { (cyclegg_mapE cyclegg_id cyclegg_e) = cyclegg_e } @-}
prop_86_no_cyclic :: (Cyclegg_Expr cyclegg_a) -> Proof
prop_86_no_cyclic cyclegg_e =
  case cyclegg_e of
    (Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31) ->
      case cyclegg_e_30 of
        (Cyclegg_App cyclegg_e_30_80 cyclegg_e_30_81) ->
          -- prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31) =>
          -- (cyclegg_mapE ?f (Cyclegg_MkExpr ?t ?n)) =>
          -- prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31):cyclegg_e_30=(Cyclegg_App cyclegg_e_30_80 cyclegg_e_30_81) =>
          -- (cyclegg_mapT ?f (Cyclegg_App ?e1 ?e2)) =>
          prop_86_no_cyclic cyclegg_e_30_80
          -- ih-equality-cyclegg_e=cyclegg_e_30_80 =>
          ? prop_86_no_cyclic cyclegg_e_30_81
          -- ih-equality-cyclegg_e=cyclegg_e_30_81 =>
          -- <= prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31):cyclegg_e_30=(Cyclegg_App cyclegg_e_30_80 cyclegg_e_30_81)
          -- <= prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31)
        (Cyclegg_Cst cyclegg_e_30_80) ->
          -- prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31) =>
          -- (cyclegg_mapE ?f (Cyclegg_MkExpr ?t ?n)) =>
          -- prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31):cyclegg_e_30=(Cyclegg_Cst cyclegg_e_30_80) =>
          -- (cyclegg_mapT ?f (Cyclegg_Cst ?n)) =>
          -- <= prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31):cyclegg_e_30=(Cyclegg_Cst cyclegg_e_30_80)
          -- <= prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31)
          ()
        (Cyclegg_Var cyclegg_e_30_80) ->
          -- prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31) =>
          -- (cyclegg_mapE ?f (Cyclegg_MkExpr ?t ?n)) =>
          -- prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31):cyclegg_e_30=(Cyclegg_Var cyclegg_e_30_80) =>
          -- (cyclegg_mapT ?f (Cyclegg_Var ?x)) =>
          -- apply-cyclegg_id =>
          -- (cyclegg_id ?x) =>
          -- <= prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31):cyclegg_e_30=(Cyclegg_Var cyclegg_e_30_80)
          -- <= prop_86_no_cyclic:cyclegg_e=(Cyclegg_MkExpr cyclegg_e_30 cyclegg_e_31)
          ()
