# generic-lens-HKD

A library for creating Free Traversals a la Sandy Macguire HKD,
(http://reasonablypolymorphic.com/blog/higher-kinded-data). It expands
on the methodology given there by including sum types and by allowing type-
changing traversals, 'Traverse s t a b'. 

This library currently supplies traversals, though only ones which target a specific location in a data structure. It
could be expanded to deliver tighter types: lenses, prisms, or traversals,
depending on need, but the method only applies to those that only targe single locations.

## A simple example

The Higher Kinded Data we'll be working with follows the pattern of ```C```, below. 

```haskell
type C = C' HK0
data C' f a = C1 { c1_a :: HK f a } deriving Generic
deriving instance (Constraints (C' f a ) Show) => Show (C' f a) --from package "one-liner"
```
Each HKD is parmeterized by a control type--
```f``` in the case of ```C```--that works in conjunction with a type family, ```HK```, to control the expression of sub-data.

```haskell
data HK0 a
type family HK (f :: ( * -> * ) ) a
type instance HK HK0    a = a
```

The special type ```HK0``` acts like the identity on types, leaving in the case of ```C``` something analogous to:
```haskell
-- data C' HK0 = C1 { c1_a :: a }
```

This library provides a newtype, ```TraverseForN s t n```, which acts as a wrapper around some ```Traversal s s' a b```, where 
```s```, ```t```, and ```n``` are used to determine ```s'```, ```a```, and ```b```. 

```haskell
newtype TraverseForN s t n = TraverseForN { getTraverseForN :: ... }

type instance HK (TraverseForN s t) a = TraverseForN s t a
```

And so ```C' (TraverseForN (C a) (C b))``` is the form of ```C``` that holds traversals on the ```C' HK0``` structure:
```haskell
-- C' (TraverseForN (C a) (C b)) = C1 {c1_a :: Traversal (C a) (C b) a b}
```
In other words, its a type holding traversals to the locations where the traversals are held.

The ```TraverseForN``` higher kinded data is made by calling ```makeTraversal @c @o```, where ```c```
is the symbol of the constructor targeted (or any symbol if non-Sum
type) and ```o``` is the data with traversals at it's points. (the ```@Type``` is enabled with 
```{-# Language TypeAnnotations #-}```).

```haskell
-- The Traversal
tCat1 :: C' (TraverseForN (C a) (C a')) (NProxy0 2)
tCat1 = makeTraversal @""

-- A data
cat1 :: C Int -- Note C = C' HK0
cat1 = C1 1

-- An application of that data (Using Control.Lens from "lens")
cat2 = cat1 & getTraverseForN (c1_a tCat1) .~ "a" -- C1 "a"
```

The ```TraverseForN s t``` uses proxies for type level natural numbers in the place of its parameters. This is so a generic
traversal can be derived, and the appropriate traversal types calculated. Each parameter (other than the HK control) must
be appropriately numbered. To ensure the proper type is formulated, ```MakeTraverseFor``` may be used. It takes a source 
type, target type, and a Nat pointing to the HKD control parameter (counting parameters left to right, starting at 1)

```haskell
-- This resolves to the same traversal as tCat1
tCat1' :: MakeTraverseFor (C a) (C a') 1
tCat1' = makeTraversal @""
```

## A Full Example

The following data is designed to show off the capibilities and limitations of this HKD traversal technique.

```haskell
type Dat = Dat' HK0
data Dat' f a b c = D1 { d1_a      :: HK f a
                       , d1_String :: HK f String }
                  | D2 { d2_b :: HK f b
                       , d2_c :: HK f c }
                  | D3 { d3_c :: HK f c }
                  deriving (Generic)
deriving instance (Constraints (Dat' f a b c) Show) =>
  Show (Dat' f a b c)

-- Example Data
dat1, dat2, dat3 :: Dat Int Int Int
dat1 = D1 1 "1"
dat2 = D2 2 2
dat3 = D3 3


-- tDat1 that targets the "D1" constructor.
tDat1 :: Dat' (TraverseForN (Dat a b c) (Dat a' b' c))
              (NProxy0 2) (NProxy0 3) (NProxy0 4)
tDat1 = makeTraversal @"D1"
-- tDat2 and tDat3 target the other constructors, MakeTraverseFor is used, but resolves to the same
-- type as tDat1
tDat2 , tDat3 :: MakeTraverseFor (Dat a b c) (Dat a' b' c) 1
tDat2 = makeTraversal @"D2"
tDat3 = makeTraversal @"D3"

-- Here's an example of a traversal being used.
dat2' :: Dat Int String Int
dat2' = dat2 & getTraverseForN (d2_b tDat2) .~ "B"
-- Note: the error messages are confusing when using mismatched data and
-- traversal types, uncomment the below (cat ^? dat) to see what I mean.
-- dat1' = cat1 ^? getTraverseForN (d2_b tDat2)

-- VALID TRAVERSALS-----------
-- Note in the above "Dat" traversals, 'c' remains unchanged. We actually
-- cannot create a valid traversal if 'c' changes because it is mentioned in
-- two different constructors. Imagine we were to target one constructor,
-- "D3", but were given the other construction, "D2". The ".~"  operation
-- would have to return the value unchanged but with a changed type. Not good!
-- A similar invalid situation arises in constructors with two
-- or more mentions of a type variable. Targeting one will require the type of
-- the collection to change, but only one can be changed, so thats bad. In
-- any case, trying to make a traversal with one of these will be an instance
-- not found failure.
-- tDat2wrong, tDat3wrong :: MakeTraverseFor (Dat a b c) (Dat a' b' c') 1
-- tDat2wrong = makeTraversal @"D2"
-- tDat3wrong = makeTraversal @"D3"
-- Traversals can be made that target multiple/all instances of a type variable
-- see generic-lens for a good solution to that problem.
-- incidentally, we can make the traversal for the first constructor:
tDat1ProbablyShouldn't :: MakeTraverseFor (Dat a b c) (Dat a' b' c') 1
tDat1ProbablyShouldn't = makeTraversal @"D1"
-- THis works because we are actually only checking for a valid traversal of
-- the first parameter:
-- t = D1
--   { d1_a :: TraverseForN {
--          getTraverseForN :: Traversal (Dat a b c) (Dat a' b c) a a' }
--   , d1_String :: TraverseForN {
--          getTraverseForN :: Traversal (Dat a b c) (Dat a b c) String String }
--   }
--

-- This system also works some higher kinded parameters, namely:
--    *, k1 -> *, k1 -> k2 -> *, k1 -> ... -> k7 -> *.
-- However, for the type family to work, and the instances to resolve, the kind
-- of each parameter may have to be specified, as below.
type H = H' HK0
data H' f (a :: *) (g :: * -> *) w = H { getH :: HK f (w (g Int) a) }
 deriving Generic
deriving instance (Constraints (H' f a g w) Show) =>
  Show (H' f a g w)
tH :: MakeTraverseFor (H a g w) (H a' g' w') 1
tH = makeTraversal @"H"
-- and an example application
anAppOfHT = h1 & getTraverseForN (getH tH) %~ fh
  where
    -- h1 :: H Int Maybe Either
    h1 = H (Left (Just 1))
    -- hl :: Maybe Int -> [Int]
    hl = maybe [] pure
    -- hr :: Int -> String
    hr = show
    fh :: Either (Maybe Int) Int -> ([Int],String)
fh = either ((,"WasLeft") . hl) (([],) . hr)
```
