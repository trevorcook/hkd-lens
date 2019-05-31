module HKD.Lens
  ( TraversalsOf
  , makeTraversalsOf
  , TraversalOf(..)
  , LensesOf
  , makeLensesOf
  , LensOf(..)
  , PrismsOf
  , makePrismsOf
  , PrismOf(..)
  , NProxyK (..)
  , ToNProxyK
  ) where

import GHC.Generics
import GHC.TypeLits hiding ( (*) )
import Data.Kind
import Data.Functor.Const
import Data.Profunctor


-- Coppied from lens
type Traversal s t a b = forall f . Applicative f => (a -> f b) -> s -> f t
type Lens s t a b      = forall f . Functor f     => (a -> f b) -> s -> f t
type Prism s t a b     =
  forall f p . (Choice p, Applicative f) => p a (f b) -> p s (f t)
iso :: (s -> a) -> (b -> t) ->
  (forall f p .(Profunctor p, Functor f) => p a (f b) -> p s (f t))
iso into outof = dimap into (fmap outof)
prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism mk e = dimap e (either pure (fmap mk)) . right'

-- TraversForN s t n:
-- Holds a traversal for some subset of changes, 'n', between 's' and 't'
newtype TraversalOf s t n = TraversalOf
  { getTraversalOf ::
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


makeTraversalsOf :: forall c o s t i .
              ( SubstituteLensParam o s ~ i
              , GetSourceAndTarget o ~ (s,t)
              , Generic o, Generic s, Generic t, Generic i
              , GLensLike End c (TraversalOf s t) (Rep i) (Rep o)
              ) => o
makeTraversalsOf = to $ gLensLike @End @c @(TraversalOf s t) @(Rep i) @(Rep o)


newtype LensOf s t n = LensOf
  { getLensOf ::
      Lens s                   (SubSub s t n)
                (GetNProxyFrom s n) (GetNProxyFrom t n)}
makeLensesOf :: forall o s t i .
              ( SubstituteLensParam o s ~ i
              , GetSourceAndTarget o ~ (s,t)
              , Generic o, Generic s, Generic t, Generic i
              , GLensLike End "" (LensOf s t) (Rep i) (Rep o)
              ) => o
makeLensesOf = to $ gLensLike @End @"" @(LensOf s t) @(Rep i) @(Rep o)

newtype PrismOf s t n = PrismOf
  { getPrismOf ::
      Prism s                   (SubSub s t n)
                (GetNProxyFrom s n) (GetNProxyFrom t n)}
makePrismsOf :: forall c o s t i .
              ( SubstituteLensParam o s ~ i
              , GetSourceAndTarget o ~ (s,t)
              , Generic o, Generic s, Generic t, Generic i
              , GLensLike End c (PrismOf s t) (Rep i) (Rep o)
              ) => o
makePrismsOf = to $ gLensLike @End @c @(PrismOf s t) @(Rep i) @(Rep o)


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
type TraversalsOf (s :: Type) (t :: Type) (i::Nat)  =
  MakeNProxyHK (TraversalOf s t) s i
type LensesOf (s :: Type) (t :: Type) (i::Nat)  =
  MakeNProxyHK (LensOf s t) s i
type PrismsOf (s :: Type) (t :: Type) (i::Nat)  =
  MakeNProxyHK (PrismOf s t) s i
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

type family GetSourceAndTarget (f :: k) :: * where
  GetSourceAndTarget (f (TraversalOf s t)) = (s, t)
  GetSourceAndTarget (f (LensOf s t)) = (s, t)
  GetSourceAndTarget (f (PrismOf s t)) = (s, t)
  GetSourceAndTarget (f a) = GetSourceAndTarget f

type SubstituteLensParam o s = SubSub o s (GetNProxyKOfLensParam o ())
type family GetNProxyKOfLensParam f :: * -> * where
   GetNProxyKOfLensParam f = GetNProxyKOfLensParam_ f (CountParams f)
type family GetNProxyKOfLensParam_ (f :: k) (n :: Nat) :: j where
  GetNProxyKOfLensParam_ (f (TraversalOf s t :: * -> *)) n =
    ToNProxyK n (TraversalOf s t :: * -> *)
  GetNProxyKOfLensParam_ (f (LensOf s t :: * -> *)) n =
    ToNProxyK n (LensOf s t :: * -> *)
  GetNProxyKOfLensParam_ (f (PrismOf s t :: * -> *)) n =
    ToNProxyK n (PrismOf s t :: * -> *)
  GetNProxyKOfLensParam_ (f a) n = GetNProxyKOfLensParam_ f (n-1)


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

newtype TraversalOfAB s t a b = TraversalOfAB
  { getTraversalOfAB :: Traversal s t a b }
newtype LensOfAB s t a b = LensOfAB
  { getLensOfAB :: Lens s t a b }
newtype PrismOfAB s t a b = PrismOfAB
  { getPrismOfAB :: Prism s t a b }

-- GLensLike populates a HK data structure with Traversals at all its nodes.
-- This class creates the data structure, it relies on GTraversalForTarget
-- to build the traversals. It works by building a path through the generic
-- representation to a K1 node and asking GTraversalForTarget for that traversal.
class GLensLike ( pth :: *) (c::Symbol) l (i :: * -> * ) o where
  gLensLike :: o p
instance        ( s' ~ SubSub s t n
                , a ~ GetNProxyFrom s n, b ~ GetNProxyFrom t n
                , Generic s, Generic s'
                , GTraversalForTarget (Push pth (K1 _x n)) c s s'
                     (Rep s) (Rep s') (Const (TraversalOfAB s s' a b))
                ) =>
  GLensLike pth c (TraversalOf s t) (K1 _x n) (K1 _x (TraversalOf s t n)) where
  gLensLike = K1 $ TraversalOf $ getTraversalOfAB t
    where
      (Const t) = gTraversalForTarget @(Push pth (K1 _x n)) @c
                                     @s @(SubSub s t n)
                $ iso from to
instance        ( s' ~ SubSub s t n
                , a ~ GetNProxyFrom s n, b ~ GetNProxyFrom t n
                , Generic s, Generic s'
                , GLensForTarget (Push pth (K1 _x n)) c s s'
                     (Rep s) (Rep s') (Const (LensOfAB s s' a b))
                ) =>
  GLensLike pth c (LensOf s t) (K1 _x n) (K1 _x (LensOf s t n)) where
  gLensLike = K1 $ LensOf $ getLensOfAB t
    where
      (Const t) = gLensForTarget @(Push pth (K1 _x n)) @c
                                     @s @(SubSub s t n)
                $ iso from to
instance        ( s' ~ SubSub s t n
                , a ~ GetNProxyFrom s n, b ~ GetNProxyFrom t n
                , Generic s, Generic s'
                , GPrismForTarget (Push pth (K1 _x n)) c s s'
                     (Rep s) (Rep s') (Const (PrismOfAB s s' a b))
                ) =>
  GLensLike pth c (PrismOf s t) (K1 _x n) (K1 _x (PrismOf s t n)) where
  gLensLike = K1 $ PrismOf $ getPrismOfAB t
    where
      (Const t) = gPrismForTarget @(Push pth (K1 _x n)) @c
                                     @s @(SubSub s t n)
                $ iso from to

instance                GLensLike (Push pth Thru) c l i o =>
  GLensLike pth c l (M1 t x i) (M1 t x o) where
  gLensLike = M1 $ gLensLike @(Push pth Thru) @c @l @i

instance                ( GLensLike (Push pth LeftP) c (TraversalOf s t) il ol
                        , GLensLike (Push pth RightP) c (TraversalOf s t) ir or ) =>
  GLensLike pth c (TraversalOf s t) (il :*: ir) (ol :*: or) where
  gLensLike = gLensLike @(Push pth LeftP) @c @(TraversalOf s t) @il @ol
                      :*:
               gLensLike @(Push pth RightP) @c @(TraversalOf s t) @ir @or
instance                ( GLensLike (Push pth LeftP) c (LensOf s t) il ol
                        , GLensLike (Push pth RightP) c (LensOf s t) ir or ) =>
  GLensLike pth c (LensOf s t) (il :*: ir) (ol :*: or) where
  gLensLike = gLensLike @(Push pth LeftP) @c @(LensOf s t) @il @ol
                      :*:
               gLensLike @(Push pth RightP) @c @(LensOf s t) @ir @or

-- Following instances are to avoid inconherent overlaps. Probably reduce?
instance             ( GLensLike (Push pth LeftS) c (TraversalOf s t) il ol ) =>
  GLensLike pth c (TraversalOf s t)
    (C1 (MetaCons c f b) il :+: C1 (MetaCons c' f' b') ir)
    (C1 (MetaCons c f b) ol :+: C1 (MetaCons c' f' b') or) where
  gLensLike = L1 . M1 $ gLensLike @(Push pth LeftS) @c @(TraversalOf s t) @il @ol
instance             ( GLensLike (Push pth LeftS) c (PrismOf s t) il ol ) =>
  GLensLike pth c (PrismOf s t)
    (C1 (MetaCons c f b) il :+: C1 (MetaCons c' f' b') ir)
    (C1 (MetaCons c f b) ol :+: C1 (MetaCons c' f' b') or) where
  gLensLike = L1 . M1 $ gLensLike @(Push pth LeftS) @c @(PrismOf s t) @il @ol

instance             ( GLensLike (Push pth LeftS) c (TraversalOf s t) il ol ) =>
  GLensLike pth c (TraversalOf s t)
    (C1 (MetaCons c f b) il :+: (irl :+: irr))
    (C1 (MetaCons c f b) ol :+: (orl :+: orr)) where
  gLensLike = L1 . M1 $ gLensLike @(Push pth LeftS) @c @(TraversalOf s t) @il @ol
instance             ( GLensLike (Push pth LeftS) c (PrismOf s t) il ol ) =>
  GLensLike pth c (PrismOf s t)
    (C1 (MetaCons c f b) il :+: (irl :+: irr))
    (C1 (MetaCons c f b) ol :+: (orl :+: orr)) where
  gLensLike = L1 . M1 $ gLensLike @(Push pth LeftS) @c @(PrismOf s t) @il @ol
instance                ( GLensLike (Push pth LeftS) c (TraversalOf s t)
                            (ill :+: ilr)
                            (oll :+: olr) ) =>
  GLensLike pth c (TraversalOf s t)
    ((ill :+: ilr) :+: C1 (MetaCons c' f' b') ir)
    ((oll :+: olr) :+: C1 (MetaCons c' f' b') ir) where
  gLensLike = L1 $ gLensLike @(Push pth LeftS) @c @(TraversalOf s t)
                               @(ill :+: ilr) @(oll :+: olr)
instance                ( GLensLike (Push pth LeftS) c (PrismOf s t)
                            (ill :+: ilr)
                            (oll :+: olr) ) =>
  GLensLike pth c (PrismOf s t)
    ((ill :+: ilr) :+: C1 (MetaCons c' f' b') ir)
    ((oll :+: olr) :+: C1 (MetaCons c' f' b') ir) where
  gLensLike = L1 $ gLensLike @(Push pth LeftS) @c @(PrismOf s t)
                               @(ill :+: ilr) @(oll :+: olr)
instance            ( GLensLike (Push pth LeftS) c (TraversalOf s t)
                             (ill :+: ilr)
                             (oll :+: olr) ) =>
  GLensLike pth c (TraversalOf s t)
    ((ill :+: ilr) :+: (irl :+: irr))
    ((oll :+: olr) :+: (orl :+: orr)) where
  gLensLike = L1 $ gLensLike @(Push pth LeftS) @c @(TraversalOf s t)
                               @(ill :+: ilr) @(oll :+: olr)
instance            ( GLensLike (Push pth LeftS) c (PrismOf s t)
                             (ill :+: ilr)
                             (oll :+: olr) ) =>
  GLensLike pth c (PrismOf s t)
    ((ill :+: ilr) :+: (irl :+: irr))
    ((oll :+: olr) :+: (orl :+: orr)) where
  gLensLike = L1 $ gLensLike @(Push pth LeftS) @c @(PrismOf s t)
                               @(ill :+: ilr) @(oll :+: olr)
instance      ( GLensLike (Push pth RightS) c (TraversalOf s t) ir or ) =>
  GLensLike pth c (TraversalOf s t)
    (C1 (MetaCons c' f' b') il :+: C1 (MetaCons c f b) ir)
    (C1 (MetaCons c' f' b') ol :+: C1 (MetaCons c f b) or) where
  gLensLike = R1 . M1 $ gLensLike @(Push pth RightS) @c @(TraversalOf s t) @ir @or
instance      ( GLensLike (Push pth RightS) c (PrismOf s t) ir or ) =>
  GLensLike pth c (PrismOf s t)
    (C1 (MetaCons c' f' b') il :+: C1 (MetaCons c f b) ir)
    (C1 (MetaCons c' f' b') ol :+: C1 (MetaCons c f b) or) where
  gLensLike = R1 . M1 $ gLensLike @(Push pth RightS) @c @(PrismOf s t) @ir @or
instance            ( GLensLike (Push pth RightS) c (TraversalOf s t) ir or ) =>
  GLensLike pth c (TraversalOf s t)
    ((ill :+: ilr) :+: C1 (MetaCons c f b) ir)
    ((oll :+: olr) :+: C1 (MetaCons c f b) or) where
  gLensLike = R1 . M1 $ gLensLike @(Push pth RightS) @c @(TraversalOf s t) @ir @or
instance            ( GLensLike (Push pth RightS) c (PrismOf s t) ir or ) =>
  GLensLike pth c (PrismOf s t)
    ((ill :+: ilr) :+: C1 (MetaCons c f b) ir)
    ((oll :+: olr) :+: C1 (MetaCons c f b) or) where
  gLensLike = R1 . M1 $ gLensLike @(Push pth RightS) @c @(PrismOf s t) @ir @or
instance {-# Overlappable #-} ( GLensLike (Push pth RightS) c (TraversalOf s t) ir or ) =>
  GLensLike pth c (TraversalOf s t)
    (il :+: ir)
    (ol :+: or) where
  gLensLike = R1 $ gLensLike @(Push pth RightS) @c @(TraversalOf s t) @ir @or
instance {-# Overlappable #-} ( GLensLike (Push pth RightS) c (PrismOf s t) ir or ) =>
  GLensLike pth c (PrismOf s t)
    (il :+: ir)
    (ol :+: or) where
  gLensLike = R1 $ gLensLike @(Push pth RightS) @c @(PrismOf s t) @ir @or



class GLensForTarget pth (c :: Symbol) s t a b o where
  gLensForTarget :: Lens s t (a p) (b p) -> o p
instance                ( b ~ GetNProxyFrom t n
                        , t ~ SubSub s t n ) =>
  GLensForTarget (K1 _x n End) c s t (K1 _x a) (K1 _x b)
                (Const (LensOfAB s t a b)) where
  gLensForTarget t = Const $ LensOfAB $ t . iso unK1 K1
instance                            GLensForTarget pth c s t a b o =>
  GLensForTarget (Thru pth) c s t (M1 _x _y a) (M1 _x _y b) o where
  gLensForTarget t = gLensForTarget @pth @c $ t . iso unM1 M1
instance                        GLensForTarget pth c s t al bl ol =>
  GLensForTarget (LeftP pth) c s t (al :*: ar) (bl :*: ar) ol where
  gLensForTarget t = gLensForTarget @pth @c $ t . t'
    where
      t' f (l :*: r) = ( :*: r) <$> f l
instance                        GLensForTarget pth c s t ar br or =>
  GLensForTarget (RightP pth) c s t (al :*: ar) (al :*: br) or where
  gLensForTarget t = gLensForTarget @pth @c $ t . t' --ens getr putr
    where
      t' f (l :*: r) = (l :*:) <$> f r



-- -- GTraversalForTarget makes Traversals to paths within a generic structure.
-- type family GetLensLikeFor (l :: * -> *) (a :: *) (b :: *) where
--   GetLensLikeFor (TraversalOf s t) a b = Traversal s t a b
--   GetLensLikeFor (LensOf s t) a b = Lens s t a b
class GTraversalForTarget pth (c :: Symbol) s t a b o where
  gTraversalForTarget :: Traversal s t (a p) (b p) -> o p
instance                ( b ~ GetNProxyFrom t n
                        , t ~ SubSub s t n ) =>
  GTraversalForTarget (K1 _x n End) c s t (K1 _x a) (K1 _x b)
                (Const (TraversalOfAB s t a b)) where
  gTraversalForTarget t = Const $ TraversalOfAB $ t . iso unK1 K1
instance                            GTraversalForTarget pth c s t a b o =>
  GTraversalForTarget (Thru pth) c s t (M1 _x _y a) (M1 _x _y b) o where
  gTraversalForTarget t = gTraversalForTarget @pth @c $ t . iso unM1 M1
instance                        GTraversalForTarget pth c s t al bl ol =>
  GTraversalForTarget (LeftP pth) c s t (al :*: ar) (bl :*: ar) ol where
  gTraversalForTarget t = gTraversalForTarget @pth @c $ t . t'
    where
      t' f (l :*: r) = ( :*: r) <$> f l
instance                        GTraversalForTarget pth c s t ar br or =>
  GTraversalForTarget (RightP pth) c s t (al :*: ar) (al :*: br) or where
  gTraversalForTarget t = gTraversalForTarget @pth @c $ t . t' --ens getr putr
    where
      t' f (l :*: r) = (l :*:) <$> f r
instance                        GTraversalForTarget pth c s t al bl ol =>
  GTraversalForTarget (LeftS pth) c s t
    (C1 (MetaCons c f b) al :+: C1 (MetaCons c' f' b') ar)
    (C1 (MetaCons c f b) bl :+: C1 (MetaCons c' f' b') ar)
    ol
    where
    gTraversalForTarget t = gTraversalForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 . M1 <$> f (unM1 a)
        g f (R1 a) = R1 <$> pure a
instance                        GTraversalForTarget pth c s t al bl ol =>
  GTraversalForTarget (LeftS pth) c s t
    (C1 (MetaCons c f b) al :+: (arl :+: arr))
    (C1 (MetaCons c f b) bl :+: (arl :+: arr))
    ol
    where
    gTraversalForTarget t = gTraversalForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 . M1 <$> f (unM1 a)
        g f (R1 a) = R1 <$> pure a
instance       GTraversalForTarget pth c s t (all :+: alr) (bll :+: blr) ol =>
  GTraversalForTarget (LeftS pth) c s t
    ((all :+: alr) :+: C1 (MetaCons c' f' b') ar)
    ((bll :+: blr) :+: C1 (MetaCons c' f' b') ar)
    ol
    where
    gTraversalForTarget t = gTraversalForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> f a
        g f (R1 a) = R1 <$> pure a
instance       GTraversalForTarget pth c s t (all :+: alr) (bll :+: blr) ol =>
  GTraversalForTarget (LeftS pth) c s t
    ((all :+: alr) :+: (arl :+: arr))
    ((bll :+: blr) :+: (arl :+: arr))
    ol
    where
    gTraversalForTarget t = gTraversalForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> f a
        g f (R1 a) = R1 <$> pure a
instance                        GTraversalForTarget pth c s t ar br or =>
  GTraversalForTarget (RightS pth) c s t
    (C1 (MetaCons c' f' b') al :+: C1 (MetaCons c f b) ar)
    (C1 (MetaCons c' f' b') al :+: C1 (MetaCons c f b) br)
    or
    where
    gTraversalForTarget t = gTraversalForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> pure a
        g f (R1 a) = R1 . M1 <$> f (unM1 a)
instance                        GTraversalForTarget pth c s t ar br or =>
  GTraversalForTarget (RightS pth) c s t
    ((all :+: alr) :+: C1 (MetaCons c f b) ar)
    ((all :+: alr) :+: C1 (MetaCons c f b) br)
    or
    where
    gTraversalForTarget t = gTraversalForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> pure a
        g f (R1 a) = R1 . M1 <$> f (unM1 a)

instance  {-# Overlappable #-}  GTraversalForTarget pth c s t ar br ol =>
  GTraversalForTarget (RightS pth) c s t
    (al :+: ar )
    (al :+: br )
    ol
    where
    gTraversalForTarget t = gTraversalForTarget @pth @c $ t . g
      where
        g f (L1 a) = L1 <$> pure a
        g f (R1 a) = R1 <$> f a


-- type Prism s t a b     =
--   forall f p . (Choice p, Applicative f) => p a (f b) -> p s (f t)
class GPrismForTarget pth (c :: Symbol) s t a b o where
  gPrismForTarget :: Prism s t (a p) (b p) -> o p
instance                ( b ~ GetNProxyFrom t n
                        , t ~ SubSub s t n ) =>
  GPrismForTarget (K1 _x n End) c s t (K1 _x a) (K1 _x b)
                (Const (PrismOfAB s t a b)) where
  gPrismForTarget t = Const $ PrismOfAB $ t . iso unK1 K1
instance                            GPrismForTarget pth c s t a b o =>
  GPrismForTarget (Thru pth) c s t (M1 _x _y a) (M1 _x _y b) o where
  gPrismForTarget t = gPrismForTarget @pth @c $ t . iso unM1 M1
instance                        GPrismForTarget pth c s t al bl ol =>
  GPrismForTarget (LeftS pth) c s t
    (C1 (MetaCons c f b) al :+: C1 (MetaCons c' f' b') ar)
    (C1 (MetaCons c f b) bl :+: C1 (MetaCons c' f' b') ar)
    ol
    where
    gPrismForTarget t = gPrismForTarget @pth @c
                      $ t . prism (L1 . M1) selectL
      -- where
      --   go (L1 (M1 a)) = Right a
      --   go (R1 (M1 b)) = Left (R1 (M1 b))
-- selectL :: (M1 t x a :)
selectL (L1 (M1 a)) = Right a
selectL (R1 x) = Left (R1 x)
selectL' (L1 a) = Right a
selectL' (R1 x) = Left (R1 x)
selectR (L1 a) = Left (L1 a)
selectR (R1 (M1 b)) = Right b
selectR' (L1 a) = Left (L1 a)
selectR' (R1 b) = Right b

instance                        GPrismForTarget pth c s t al bl ol =>
  GPrismForTarget (LeftS pth) c s t
    (C1 (MetaCons c f b) al :+: (arl :+: arr))
    (C1 (MetaCons c f b) bl :+: (arl :+: arr))
    ol
    where
    gPrismForTarget t = gPrismForTarget @pth @c
                      $ t . prism (L1 . M1) selectL
instance       GPrismForTarget pth c s t (all :+: alr) (bll :+: blr) ol =>
  GPrismForTarget (LeftS pth) c s t
    ((all :+: alr) :+: C1 (MetaCons c' f' b') ar)
    ((bll :+: blr) :+: C1 (MetaCons c' f' b') ar)
    ol
    where
    gPrismForTarget t = gPrismForTarget @pth @c $ t . prism L1 selectL'
instance       GPrismForTarget pth c s t (all :+: alr) (bll :+: blr) ol =>
  GPrismForTarget (LeftS pth) c s t
    ((all :+: alr) :+: (arl :+: arr))
    ((bll :+: blr) :+: (arl :+: arr))
    ol
    where
    gPrismForTarget t = gPrismForTarget @pth @c $ t . prism L1 selectL'
instance                        GPrismForTarget pth c s t ar br or =>
  GPrismForTarget (RightS pth) c s t
    (C1 (MetaCons c' f' b') al :+: C1 (MetaCons c f b) ar)
    (C1 (MetaCons c' f' b') al :+: C1 (MetaCons c f b) br)
    or
    where
    gPrismForTarget t = gPrismForTarget @pth @c $ t . prism (R1 . M1) selectR
instance                        GPrismForTarget pth c s t ar br or =>
  GPrismForTarget (RightS pth) c s t
    ((all :+: alr) :+: C1 (MetaCons c f b) ar)
    ((all :+: alr) :+: C1 (MetaCons c f b) br)
    or
    where
    gPrismForTarget t = gPrismForTarget @pth @c $ t . prism (R1 . M1) selectR
instance  {-# Overlappable #-}  GPrismForTarget pth c s t ar br ol =>
  GPrismForTarget (RightS pth) c s t
    (al :+: ar )
    (al :+: br )
    ol
    where
    gPrismForTarget t = gPrismForTarget @pth @c $ t . prism R1 selectR'
