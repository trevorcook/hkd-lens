# generic-lens-HKD

A library for creating traversals for higher kinded data (HKD)
following the method detailed by Sandy Maguire
(http://reasonablypolymorphic.com/blog/higher-kinded-data). It expands
on the methodology given there by including data with multiple
constructors and by allowing type-changing traversals, ```Traverse s t a b```.

This library currently supplies only traversals, though the methodology
will be expanded to derive lenses and prisms as well. However, the
methodology only allows traversals which target a single specific location
in a data structure. This is an inherent feature of the method and will
not change. Consult the package "generic-lens" for generic ways of targeting
multiple locations.

## Quick Start
```haskell
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PolyKinds #-}

module Test where

import Generics.OneLiner --package one-liner
import Control.Lens      --package lens
import HKD.Traversal
import GHC.TypeLits
import GHC.Generics(Generic)

-- Higher Kind 0, used for "Un" higher kinding.
data HK0 a
type family HK (f :: ( * -> * ) ) a where
  HK HK0 a = a
  HK f   a = f a

type AB = AB' HK0
data AB' f a b = A { a_A :: HK f a, num_A :: HK f Int }
               | B { bs_B :: HK f [b] }
              deriving Generic
deriving instance (Constraints (AB' f a b) Show) => Show (AB' f a b)

thisABs :: [AB String Int]
thisABs = [ A "1" 1
          , B [0,1,2] ]
thisABs' :: [ (AB Int Int, AB String Int, AB String String) ]
thisABs' = foo thisABs
--   = [ (A 1 1, A "1" 10, A "1" 1)
--     , (B [0,1,2], B [0,1,2], B ["0","1","2"]) ]

foo :: [AB String Int] -> [ (AB Int Int, AB String Int, AB String String) ]
foo = map $ \ab -> ( ab & getTraverseForN (a_A tA) %~ read
                   , ab & getTraverseForN (num_A tA) %~ (*10)
                   , ab & getTraverseForN (bs_B tB) %~ map show )

tA, tB :: MakeTraverseFor (AB a b) (AB c d) 1
tA = makeTraversal @"A"
tB = makeTraversal @"B"
```

## A Simple Example Explained
### Higher Kinded Data
The Higher Kinded Data we'll be working with follows the pattern of ```C'```, below.

```haskell
data C' f a = C1 { c1_a :: HK f a } deriving Generic
```

Each HKD, such as ```C'```, is parmeterized by a control type, ```f``` in this case,
that works in conjunction with a type family, ```HK```, to control the expression of
sub-data, the data at ```c1_a```.
```haskell
{-# LANGUAGE TypeFamilies #-}
data HK0 a
type family HK (f :: ( * -> * ) ) a where
  HK HK0 a = a
  HK f   a = f a
```
The special type ```HK0``` is defined so that ```HK HK0``` is the identity on types. Additionally, the definition of HK is not defined in this library,
nor necessary. The method works for other similarly defined type families, or
none at all.

And we might generally define a type allias such as:
```haskell
type C = C' HK0
```
to ease our minds when working with the basic higher kinded form of a data type.
That is, ```C' HK0``` makes it as if we had defined:
```haskell
data C = C1 { c1_a :: a }
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
```

The traversal form of ```C'```, ```C' (TraverseForN (C a) (C b))``` is the form of ```C'``` that
holds traversals of the ```C' HK0``` structure. Something analogous to the below:

```haskell
C' (TraverseForN (C a) (C b)) = C1 {c1_a :: Traversal (C a) (C b) a b }
```
In other words, every point in a traversal kinded data holds a traversal between
the basic form of that data and the same point in the basic data at which the
traversal is stored.

#### Generating Traversal Kinded Data

The traversal kinded data is made by calling ```makeTraversal @c```, where ```c```
is the symbol of the constructor targeted (or any symbol for single constructor
types). (Note, the ```@Type``` syntax is enabled with
```{-# Language TypeAnnotations #-}```).

The type for the traversal kinded data is derived with the ```MakeTraverseFor``` type family.
It takes a source type, target type, and a ```Nat``` pointing to the HK control parameter
(counting parameters left to right, starting at 1). Note that for complicated data
structures not all type parameters may be able to change their type, this is explained
in the Valid Traversals section of this document.

```haskell
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
import Control.Lens((.~),(&))

-- Generate the traversal
tC :: MakeTraverseFor (C a) (C b) 1
tC = makeTraversal @""

-- Define some data to traverse
c1 :: C Int
c1 = C1 1

-- An application of the traversal
c2 = C String
c2 = c1 & getTraverseForN (c1_a tC) .~ "a" -- Yields C1 "a"
```

#### The Traversal Kinded Data/NProxyK

For the sake of exposition, it may be helpful to know that
```MakeTraverseFor (C a) (C b) 1``` resolves to ``` C' (TraverseForN (C a) (C b)) (NProxyK 2 a)```.
And so, the following definition is the same as ```tC```.

```haskell
tC' :: C' (TraverseForN (C a) (C b)) (NProxyK 2 a)
tC' = makeTraversal @""
```

The traversal kind uses proxies for type level natural numbers, ```Nat```, for its type parameters.
This allows the appropriate traversal type to be calculated at the various places within the HKD,
and for generic traversals to be derived. Each parameter (other than the HK control) must be
appropriately numbered with an appropriately-kinded proxy. These proxies
are created through the data family ```NProxyK n a```; where ```n``` is the ```Nat``` of the parameter position, and ```a``` is an example data type
of the appropriate kind.

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
deriving instance (Constraints (D' f g a b c) Show) =>
  Show (D' f g a b c)

-- Example Data
d1, d2, d3 :: D [] Int Int Int
d1 = D1 [(1,1)] "1"
d2 = D2 2 2
d3 = D3 3

-- tD1 targets the "D1" constructor.
tD1 :: D' (TraverseForN (D g a b c) (D g' a' b' c))
              (NProxyK 2 g) (NProxyK 3 a) (NProxyK 4 b) (NProxyK 5 c)
tD1 = makeTraversal @"D1"
```
Note that ```tD1``` has a form analogous to:
```haskell
D1 { d1_a :: Traversal (D g a b c) (D g' a' b c) (g (Int, a)) (g' (Int,a'))
   , d1_String :: Traversal (D g a b c) (D g a b c) String String }
```
Its a ```D1``` constructor with two traversals. Note that the
two traversals do not match exaclty the types specified in the
traversal type, ```D' (TraverseForN ...) ...```. Rather, the data types
specified in the traversal type serve as lower and upper bounds for
the types that may be traversed at every point. The traversal at ```d1_a```
involves the ```g``` and ```a``` type parameters, and so the traversal is between
two forms of ```D'``` that (may) change those parameters. Similarly, the
traversal at ```d1_String``` does not involve any type parmeters and so
it is a non-type changing traversal.

Traversals nested in the other constructors are made using ```MakeTraverseFor```,
but resolve to the same type as tD1.

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
In the above ```D``` traversals, the type variable ```c``` remains unchanged.
We actually cannot create a valid traversal if ```c``` changes because it is
mentioned in two different constructors: ```D2``` and ```D3```.

Why? Imagine we were to target one constructor, ```D3```, but were given the
other construction, ```D2```, as in:

```haskell
... = (D3 1) & getTraverseForN (d2_c tD2') .~ "string for d2_c"
```

The traversal ```(d2_c tD2')``` misses its target, and so the  ```.~```
operation is supposed to return the supplied value unchanged. However
the traversal we are asking for promises that we can change ```c``` to
a ```String```--we can't.

A similar invalid situation arises in constructors with two
or more mentions of a type variable. Targeting one will require the type of
all instances in the constructor to change--but only one will be changed.
In any case, trying to make such a traversal kind will be a compile
time error.

```haskell
tD2_wrong, tDat3wrong :: MakeTraverseFor (D g a b c) (D g' a' b' c') 1
tD2_wrong = makeTraversal @"D2" --error (Instance not Found)
tD3_wrong = makeTraversal @"D3" --error (Instance not Found)
```

Traversals can be made that target multiple/all instances of a type variable,
of course--just not with this library. The "generic-lens" package provides
a solution to that problem.

Incidentally, we can make the traversal for the first constructor:

```haskell
tD1_ProbablyShouldn't :: MakeTraverseFor (D g a b c) (D g a' b' c') 1
tD1_ProbablyShouldn't = makeTraversal @"D1"
```

This works because we are actually only checking for a valid traversal of
the first parameter. An inspection of the traversal kinded type should
be helpful.

```haskell
t = D1
   { d1_a :: TraverseForN {
          getTraverseForN :: Traversal (D g a b c) (D g' a' b c) (g (Int, a)) (g' (Int,a')) }
   , d1_String :: TraverseForN {
          getTraverseForN :: Traversal (Dat a b c) (Dat a b c) String String }
   }
```
