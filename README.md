# generic-lens-HKD

A library for creating Free Traversals a la Sandy Macguire HKD,
(http://reasonablypolymorphic.com/blog/higher-kinded-data). It expands
on the methodology given there by including sum types and by allowing type-
changing traversals, ```Traverse s t a b```. 

This library currently supplies only traversals, though the methodology
could be expanded to deliver tighter types: lenses, prisms, or traversals--
depending on use case. However, the methodology only allows traversals 
which target a single specific location in a data structure. 

## A Simple Example
### Higher Kinded Data
The Higher Kinded Data we'll be working with follows the pattern of ```C'```, below. 

```haskell
data C' f a = C1 { c1_a :: HK f a } deriving Generic
```

Each HKD, such as ```C'```, is parmeterized by a control type, ```f``` in this case,
that works in conjunction with a type family, ```HK```, to control the expression of sub-data, 
the data at ```c1_a```

```haskell
{-# LANGUAGE TypeFamilies #-}
type family HK (f :: ( * -> * ) ) a
```
The special type ```HK0``` is defined so that ```HK HK0``` is the identity on types, 

```haskell
data HK0 a
type instance HK HK0 a = a
```
And we might generally define a type allias such as: 
```haskell
type C = C' HK0
```
to ease our minds when working with the basic higher kinded form of a data type. 
That is, ```C' HK0``` leaves us with something analogous to:
```haskell
-- data C' HK0 = C1 { c1_a :: a }
```
#### Standalone Deriving for HKD
Note, that the "one-liner" package (possibly "barbies" also) can be used to make
deriving class instances for HKD easier.

```haskell
{-# LANGUAGE StandaloneDeriving #-}
import Generics.OneLiner
deriving instance (Constraints (C' f a ) Show) => Show (C' f a)
```
### Traversal Kinded Data

This library provides a newtype, ```TraverseForN s t n```, which acts as a wrapper around some 
```Traversal s s' a b```, where  ```s```, ```t```, and ```n``` are used to determine 
```s'```, ```a```, and ```b```. 

```haskell
newtype TraverseForN s t n = TraverseForN { getTraverseForN :: ... }
type instance HK (TraverseForN s t) a = TraverseForN s t a
```

The traversal form of ```C'```, ```C' (TraverseForN (C a) (C b))``` is the form of ```C'``` that 
holds traversals of the ```C' HK0``` structure. Something analogous to the below:

```haskell
-- C' (TraverseForN (C a) (C b)) = C1 {c1_a :: Traversal (C a) (C b) a b}
```

#### Generating Traversal Kinded Data

The traversal kinded data is made by calling ```makeTraversal @c @o```, where ```c```
is the symbol of the constructor targeted (or any symbol if non-Sum
type) and ```o``` is the data with traversals at it's points. (the ```@Type``` is 
enabled with  ```{-# Language TypeAnnotations #-}```).

```haskell
{-# LANGUAGE TypeFamilies #-}
import Control.Lens

-- The Traversal (NProxy0 explained below)
tC :: C' (TraverseForN (C a) (C a')) (NProxy0 2)
tC = makeTraversal @""

-- A data
c1 :: C Int 
c1 = C1 1

-- An application of that data (Using Control.Lens from "lens")
c2 = C String
c2 = c1 & getTraverseForN (c1_a tC) .~ "a" -- Yields C1 "a"
```

#### NProxyK

The ```TraverseForN s t``` uses proxies for type level natural numbers in the place of its parameters.
This allows generic traversals to be derived, and the appropriate traversal types calculated. Each 
parameter (other than the HK control) must be appropriately numbered. With an appropriately kinded proxy,
i.e ```NProxy0 1``` for the first parameter of kind ```*```, ```NProxy2 1``` for the first parameter, which
has the kind, ```k0 -> k1 -> *```. There are ```NProxyK```s defined for K = 0 to 7.

#### MakeTraverseFor

To ensure the proper type is formulated, ```MakeTraverseFor``` may be used. It takes a source 
type, target type, and a ```Nat``` pointing to the HK control parameter (counting parameters 
left to right, starting at 1)

```haskell
-- This resolves to the same traversal as tC
tC' :: MakeTraverseFor (C a) (C a') 1
tC' = makeTraversal @""
```

## A Full Example

The following data is designed to demonstrate the capibilities and limitations of this 
HKD traversal technique.

```haskell
type D = D' HK0
data D' f g a b c = D1 { d1_a      :: HK f (g (Int, a))
                       , d1_String :: HK f String }
                  | D2 { d2_b :: HK f b
                       , d2_c :: HK f c }
                  | D3 { d3_c :: HK f c }
                  deriving (Generic)
deriving instance (Constraints (D' f a b c) Show) =>
  Show (D' f a b c)

-- Example Data
d1, d2, d3 :: D [] Int Int Int
d1 = D1 [(1,1)] "1"
d2 = D2 2 2
d3 = D3 3

-- tD1 targets the "D1" constructor.
tD1 :: D' (TraverseForN (D g a b c) (D g' a' b' c))
              (NProxy1 2) (NProxy0 3) (NProxy0 4) (NProxy0 5)
tD1 = makeTraversal @"D1"
```
Note that ```tD1``` has the form:
```haskell
-- D1 { d1_a :: Traversal (D g a b c) (D g' a' b' c) a a'
      , d1_String :: Traversal (D g a b c) (D g a b c) String String }
```

Traversals nested in the other constructors are made below using ```MakeTraverseFor```, 
but resolve to the same type as tD1

```haskell
tD2 , tD3 :: MakeTraverseFor (D g a b c) (D g' a' b' c) 1
tD2 = makeTraversal @"D2"
tD3 = makeTraversal @"D3"
``` 

Here's an example of a traversal being used.
```haskell
d2' :: D [] Int String Int
d2' = d2 & getTraverseForN (d2_b tD2) .~ "B"
```

#### Error in mismatch data and traversal types
Note: the error messages are confusing when using mismatched data and
traversal types. Try the below (cat ^? dat) to see what I mean.
```haskell
d1' = c1 ^? getTraverseForN (d2_b tD2)
```

###  VALID TRAVERSALS
In the above "D" traversals, 'c' remains unchanged. We actually
cannot create a valid traversal if 'c' changes because it is mentioned in
two different constructors.

Imagine we were to target one constructor, "D3", but were given the other construction, 
"D2". The ".~"  operation would have to return the value unchanged but with a changed type. 
Not good!

A similar invalid situation arises in constructors with two
or more mentions of a type variable. Targeting one will require the type of
the collection to change, but only one can be changed, so thats bad. In
any case, trying to make a traversal with one of these will be an instance
not found failure.

```haskell
tDat2wrong, tDat3wrong :: MakeTraverseFor (Dat a b c) (Dat a' b' c') 1
tDat2wrong = makeTraversal @"D2" --error
tDat3wrong = makeTraversal @"D3" --error
```

Traversals can be made that target multiple/all instances of a type variable
see generic-lens for a good solution to that problem.
Incidentally, we can make the traversal for the first constructor:

```haskell
tDat1ProbablyShouldn't :: MakeTraverseFor (Dat a b c) (Dat a' b' c') 1
tDat1ProbablyShouldn't = makeTraversal @"D1"
```

This works because we are actually only checking for a valid traversal of
the first parameter. An inspection of the Traversal kinded type should
be helpful.
```haskell
t = D1
   { d1_a :: TraverseForN {
          getTraverseForN :: Traversal (Dat a b c) (Dat a' b c) a a' }
   , d1_String :: TraverseForN {
          getTraverseForN :: Traversal (Dat a b c) (Dat a b c) String String }
   }


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
