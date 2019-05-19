{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
module HKD.Traversal
  ( TraverseForN(..)
  , MakeTraverseFor
  , NProxyK (..)
  , ToNProxyK
  , makeTraversal
  ) where

import GHC.Generics
import GHC.TypeLits hiding ( (*) )
import Data.Kind
import Data.Functor.Const


data PxK (a::k) (b::j)

-- Cutail Lens dependency
type Traversal s t a b = forall f . Applicative f => (a -> f b) -> s -> f t
iso :: (s -> a) -> (b -> t) -> (forall f . Functor f => (a -> f b) -> s -> f t)
iso into outof f = fmap outof . f . into

-- TraversForN s t n:
-- Holds a traversal for some subset of changes, 'n', between 's' and 't'
newtype TraverseForN s t n = TraverseForN
  { getTraverseForN ::
      Traversal s                   (SubSub s t n)
                (GetNProxyFrom s n) (GetNProxyFrom t n)}
-- SubSub s t n: changes s to some type s' with a mixture of variables from
-- s and t, determined by n.
-- GetNProxyFrom s n: Builds a type based on the specification, n, that
-- includes type parameter indices and concrete types (rigid variables)
-- Fyi: n will be types like 'NProx0 1'--which specifies the first type
-- parameter (of kind *), and 'NProxK1 1 (Either String (NProx0 2))'--which
-- specifies the first type parameter applied to 'Either String' of the 2nd
-- type parameter, e.g. '[Either String Int]' for data type 'A [] Int'.
-- NB, although the traversal says 's' and 't', the actual traversal contained
-- will be between 's' and some type 's2'--that may or may not be 't'. 't' acts
-- as a sort of "upper bound" on the type 's2' may take.

makeTraversal :: forall c o s t i .
              ( ReplacingTraverseForN o s ~ i
              , GetTraverseFor o ~ (s,t)
              , Generic o, Generic s, Generic t, Generic i
              , GTraversal End c s t (Rep i) (Rep o)
              ) => o
makeTraversal = to $ gTraversal @End @c @s @t @(Rep i) @(Rep o)


-- type family LookupN (x :: k) :: Maybe Nat where
--   LookupN (NProxyK n a) = Just n
--   LookupN x             = Nothing
type family ToNProxyK (n :: Nat) (a :: k) :: k where
  ToNProxyK n (a :: Type) = NProxyK n a
  ToNProxyK n (a :: j -> k) = NProxyK n a

class HasNProxyK j where
  data NProxyK (n :: Nat) (a::j) :: k
instance HasNProxyK Bool where
  data NProxyK n a = NProxyKB
instance HasNProxyK Type where
  data NProxyK n a = NProxyK0
instance HasNProxyK k => HasNProxyK (j -> k) where
  data NProxyK n f = NProxyK1 -- (NProxyK n (f a))


-- The following turn (T a b c) into the type with Nat Proxies at the
-- paramters, (T 1 2 3)
-- This one will substitute HK0 at index i
-- type MakeNProxyHK0 (s :: Type) i = MakeNProxyHK HK0 s i
-- This one will make the traverseFor type at index i
type MakeTraverseFor (s :: Type) (t :: Type) (i::Nat)  =
  MakeNProxyHK (TraverseForN s t) s i
-- This one singles out a special type parameter for substitution
type MakeNProxyHK (f :: k -> Type) (s ::Type) (hki :: Nat)  =
  MakeNProxyHK_ f s hki (CountParams s)
type family MakeNProxyHK_ (f :: j -> *) (s :: k) (h :: Nat) (i :: Nat) :: k where
  MakeNProxyHK_ f (s a) 1 1 = s f
  MakeNProxyHK_ f (s a) h 1 = s (ToNProxyK 1 a)
  MakeNProxyHK_ f (s a) h h = (MakeNProxyHK_ f s h (h - 1)) f
  MakeNProxyHK_ f (s a) h i = (MakeNProxyHK_ f s h (i - 1)) (ToNProxyK i a)

-- Turn a parameter proxy into a type
-- E.g. given 'T a g w', turn `3 (2 Int) 1` into `w (g Int) a`
type family GetNProxyFrom (s :: j) (pxy :: k) :: k where
  GetNProxyFrom s (NProxyK n a) = GetN s n
  GetNProxyFrom s (f a) = GetNProxyFrom s f (GetNProxyFrom s a)
  GetNProxyFrom s a = a

-- Remake a the data type according to a targeted subtype
-- (Either a b) (Either c d) (Maybe 2) -> Either a d
type SubSub (s :: Type) (t :: Type) (n::k) =
  (SubNProxyWith s n (GetNProxyFrom t n) :: Type)
-- Replace a subset of variables according to a proxy specification.
type family SubNProxyWith (s :: j) (n :: k) (a :: k) :: j where
  SubNProxyWith s (NProxyK n _) a = SubNProxyWith' s (CountParams s - n) a
  SubNProxyWith s (u n) (f a) = SubNProxyWith (SubNProxyWith s n a) u f
  SubNProxyWith s n a = s
type family SubNProxyWith' (s :: j) (n :: Nat) (a :: k) :: j where
  SubNProxyWith' (s a :: j) 0 b = (s b :: j)
  SubNProxyWith' (s a) n b = (SubNProxyWith' s (n - 1) b) a

type family CountParams (f :: k) :: Nat where
  CountParams (f a) = 1 + CountParams f
  CountParams f     = 0

type GetN f n = GetN_ f (CountParams f - n)
type family GetN_ (f :: j) (i :: Nat) :: k where
  GetN_ (f a) 0 = a
  GetN_ (f a) i = GetN_ f (i - 1)

type family GetTraverseFor (f :: k) :: * where
  GetTraverseFor (f (TraverseForN s t)) = (s, t)
  GetTraverseFor (f a) = GetTraverseFor f

type ReplacingTraverseForN o s = SubSub o s (GetNProxyKOfTraverseFor o ())
type family GetNProxyKOfTraverseFor f :: * -> * where
   GetNProxyKOfTraverseFor f = GetNProxyKOfTraverseFor_ f (CountParams f)
type family GetNProxyKOfTraverseFor_ (f :: k) (n :: Nat) :: j where
  GetNProxyKOfTraverseFor_ (f (TraverseForN s t :: * -> *)) n =
    ToNProxyK n (TraverseForN s t :: * -> *)
  GetNProxyKOfTraverseFor_ (f a) n = GetNProxyKOfTraverseFor_ f (n-1)


-- For Recording Path in a Generic Representation.
type family Push (pth :: * ) (stp :: * -> *) :: * where
  Push (f g) h = f (Push g h)
  Push End f = f End
data End
data Thru :: * -> *
data LeftP :: * -> *
data RightP :: * -> *
data LeftS :: * -> *
data RightS :: * -> *

newtype TraverseFor s t a b = TraverseFor
  { getTraverseFor :: Traversal s t a b }

-- GTraversal populates a HK data structure with Traversals at all its nodes.
-- This class creates the data structure, it relies on GTraverseForTarget
-- to build the traversals. It works by building a path through the generic
-- representation to a K1 node and asking GTraverseForTarget for that traversal.
class GTraversal ( pth :: *) (c::Symbol) s t (i :: * -> * ) o where
  gTraversal :: o p
instance        ( s' ~ SubSub s t n
                , a ~ GetNProxyFrom s n, b ~ GetNProxyFrom t n
                , Generic s, Generic s'
                , GTraverseForTarget (Push pth (K1 _x n)) c s s'
                     (Rep s) (Rep s') (Const (TraverseFor s s' a b))
                ) =>
  GTraversal pth c s t (K1 _x n) (K1 _x (TraverseForN s t n)) where
  gTraversal = K1 $ TraverseForN $ getTraverseFor t
    where
      (Const t) = gTraverseForTarget @(Push pth (K1 _x n)) @c @s @(SubSub s t n)
                $ iso from to

instance                GTraversal (Push pth Thru) c s t i o =>
  GTraversal pth c s t (M1 D x i) (M1 D x o) where
  gTraversal = M1 $ gTraversal @(Push pth Thru) @c @s @t @i
instance                GTraversal (Push pth Thru) c s t i o =>
  GTraversal pth c s t (M1 S x i) (M1 S x o) where
  gTraversal = M1 $ gTraversal @(Push pth Thru) @c @s @t @i
instance             GTraversal (Push pth Thru) c' s t i o =>
  GTraversal pth c' s t (M1 C x i) (M1 C x o) where
  gTraversal = M1 $ gTraversal @(Push pth Thru) @c' @s @t @i

instance                ( GTraversal (Push pth LeftP) c s t il ol
                        , GTraversal (Push pth RightP) c s t ir or ) =>
  GTraversal pth c s t (il :*: ir) (ol :*: or) where
  gTraversal = gTraversal @(Push pth LeftP) @c @s @t @il @ol
                      :*:
               gTraversal @(Push pth RightP) @c @s @t @ir @or
-- Following instances are to avoid inconherent overlaps. Probably reduce?
instance             ( GTraversal (Push pth LeftS) c s t il ol ) =>
  GTraversal pth c s t
    (C1 (MetaCons c f b) il :+: C1 (MetaCons c' f' b') ir)
    (C1 (MetaCons c f b) ol :+: C1 (MetaCons c' f' b') or) where
  gTraversal = L1 . M1 $ gTraversal @(Push pth LeftS) @c @s @t @il @ol
instance             ( GTraversal (Push pth LeftS) c s t il ol ) =>
  GTraversal pth c s t
    (C1 (MetaCons c f b) il :+: (irl :+: irr))
    (C1 (MetaCons c f b) ol :+: (orl :+: orr)) where
  gTraversal = L1 . M1 $ gTraversal @(Push pth LeftS) @c @s @t @il @ol
instance                ( GTraversal (Push pth LeftS) c s t
                            (ill :+: ilr)
                            (oll :+: olr) ) =>
  GTraversal pth c s t
    ((ill :+: ilr) :+: C1 (MetaCons c' f' b') ir)
    ((oll :+: olr) :+: C1 (MetaCons c' f' b') ir) where
  gTraversal = L1 $ gTraversal @(Push pth LeftS) @c @s @t
                               @(ill :+: ilr) @(oll :+: olr)
instance            ( GTraversal (Push pth LeftS) c s t
                             (ill :+: ilr)
                             (oll :+: olr) ) =>
  GTraversal pth c s t
    ((ill :+: ilr) :+: (irl :+: irr))
    ((oll :+: olr) :+: (orl :+: orr)) where
  gTraversal = L1 $ gTraversal @(Push pth LeftS) @c @s @t
                               @(ill :+: ilr) @(oll :+: olr)

instance      ( GTraversal (Push pth RightS) c s t ir or ) =>
  GTraversal pth c s t
    (C1 (MetaCons c' f' b') il :+: C1 (MetaCons c f b) ir)
    (C1 (MetaCons c' f' b') ol :+: C1 (MetaCons c f b) or) where
  gTraversal = R1 . M1 $ gTraversal @(Push pth RightS) @c @s @t @ir @or
instance            ( GTraversal (Push pth RightS) c s t ir or ) =>
  GTraversal pth c s t
    ((ill :+: ilr) :+: C1 (MetaCons c f b) ir)
    ((oll :+: olr) :+: C1 (MetaCons c f b) or) where
  gTraversal = R1 . M1 $ gTraversal @(Push pth RightS) @c @s @t @ir @or
instance {-# Overlappable #-} ( GTraversal (Push pth RightS) c s t ir or ) =>
  GTraversal pth c s t
    (il :+: ir)
    (ol :+: or) where
  gTraversal = R1 $ gTraversal @(Push pth RightS) @c @s @t @ir @or


-- GTraverseForTarget makes Traversals to paths within a generic structure.
class GTraverseForTarget pth (c :: Symbol) s s' a b o where
  gTraverseForTarget :: Traversal s s' (a p) (b p) -> o p
instance                ( b ~ GetNProxyFrom s' n
                        , s' ~ SubSub s s' n ) =>
  GTraverseForTarget (K1 _x n End) c s s' (K1 _x a) (K1 _x b)
                (Const (TraverseFor s s' a b)) where
  gTraverseForTarget t = Const $ TraverseFor $ t . iso unK1 K1
instance                            GTraverseForTarget pth c s s' a b o =>
  GTraverseForTarget (Thru pth) c s s' (M1 _x _y a) (M1 _x _y b) o where
  gTraverseForTarget t = gTraverseForTarget @pth @c $ t . iso unM1 M1
instance                        GTraverseForTarget pth c s s' al bl ol =>
  GTraverseForTarget (LeftP pth) c s s' (al :*: ar) (bl :*: ar) ol where
  gTraverseForTarget t = gTraverseForTarget @pth @c $ t . t'
    where
      t' f (l :*: r) = ( :*: r) <$> f l
instance                        GTraverseForTarget pth c s s' ar br or =>
  GTraverseForTarget (RightP pth) c s s' (al :*: ar) (al :*: br) or where
  gTraverseForTarget t = gTraverseForTarget @pth @c $ t . t' --ens getr putr
    where
      t' f (l :*: r) = (l :*:) <$> f r


instance                        GTraverseForTarget pth c s s' al bl ol =>
  GTraverseForTarget (LeftS pth) c s s'
    (C1 (MetaCons c f b) al :+: C1 (MetaCons c' f' b') ar)
    (C1 (MetaCons c f b) bl :+: C1 (MetaCons c' f' b') ar)
    ol
    where
    gTraverseForTarget t = gTraverseForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 . M1 <$> f (unM1 a)
        g f (R1 a) = R1 <$> pure a
instance                        GTraverseForTarget pth c s s' al bl ol =>
  GTraverseForTarget (LeftS pth) c s s'
    (C1 (MetaCons c f b) al :+: (arl :+: arr))
    (C1 (MetaCons c f b) bl :+: (arl :+: arr))
    ol
    where
    gTraverseForTarget t = gTraverseForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 . M1 <$> f (unM1 a)
        g f (R1 a) = R1 <$> pure a
instance       GTraverseForTarget pth c s s' (all :+: alr) (bll :+: blr) ol =>
  GTraverseForTarget (LeftS pth) c s s'
    ((all :+: alr) :+: C1 (MetaCons c' f' b') ar)
    ((bll :+: blr) :+: C1 (MetaCons c' f' b') ar)
    ol
    where
    gTraverseForTarget t = gTraverseForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> f a
        g f (R1 a) = R1 <$> pure a
instance       GTraverseForTarget pth c s s' (all :+: alr) (bll :+: blr) ol =>
  GTraverseForTarget (LeftS pth) c s s'
    ((all :+: alr) :+: (arl :+: arr))
    ((bll :+: blr) :+: (arl :+: arr))
    ol
    where
    gTraverseForTarget t = gTraverseForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> f a
        g f (R1 a) = R1 <$> pure a
instance                        GTraverseForTarget pth c s s' ar br or =>
  GTraverseForTarget (RightS pth) c s s'
    (C1 (MetaCons c' f' b') al :+: C1 (MetaCons c f b) ar)
    (C1 (MetaCons c' f' b') al :+: C1 (MetaCons c f b) br)
    or
    where
    gTraverseForTarget t = gTraverseForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> pure a
        g f (R1 a) = R1 . M1 <$> f (unM1 a)
instance                        GTraverseForTarget pth c s s' ar br or =>
  GTraverseForTarget (RightS pth) c s s'
    ((all :+: alr) :+: C1 (MetaCons c f b) ar)
    ((all :+: alr) :+: C1 (MetaCons c f b) br)
    or
    where
    gTraverseForTarget t = gTraverseForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> pure a
        g f (R1 a) = R1 . M1 <$> f (unM1 a)

instance  {-# Overlappable #-}  GTraverseForTarget pth c s s' ar br ol =>
  GTraverseForTarget (RightS pth) c s s'
    (al :+: ar )
    (al :+: br )
    ol
    where
    gTraverseForTarget t = gTraverseForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> pure a
        g f (R1 a) = R1 <$> f a
