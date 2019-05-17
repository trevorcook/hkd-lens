{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeAnnotations #-}
{-# LANGUAGE TypeAnnotations #-}
{-# LANGUAGE DeriveGeneric  #-}

module Test
import Generics.OneLiner --package one-liner
import Control.Lens      --package lens
import HKD.Traversal

-- Higher Kind 0, used for "Un" higher kinding.
data HK0 a
type family HK (f :: ( * -> * ) ) a
type instance HK HK0    a = a
type instance HK (TraverseForN s t) a = TraverseForN s t a

-- The traversal is made by calling "makeTraversal @c @o", where c
-- is the symbol of the constructor targeted (or any symbol if non-Sum
-- type) and o is the data with traversals at it's points. The type
-- families should take care of resolving the rest of the many variables
-- used in the 'gTraversal' class.
-- Examples
type Dat = Dat' HK0
data Dat' f a b c = D1 { d1_a      :: HK f a
                       , d1_String :: HK f String }
                  | D2 { d2_b :: HK f b
                       , d2_c :: HK f c }
                  | D3 { d3_c :: HK f c }
                  deriving (Generic)
deriving instance (Constraints (Dat' f a b c) Show) =>
  Show (Dat' f a b c)

type Cat = Cat' HK0
data Cat' f a = C1 { c1_a :: HK f a } deriving Generic
deriving instance (Constraints (Cat' f a ) Show) =>
  Show (Cat' f a)

cat1 :: Cat Int
cat1 = C1 1
dat1, dat2, dat3 :: Dat Int Int Int
dat1 = D1 1 "1"
dat2 = D2 2 2
dat3 = D3 3

-- Below, makeTraversal yeilds a Cat' structure, shaped like a cat, but with
-- Traversal at it's data cites, something like:
--  C1 { c1_a = Traversal (Cat a) (Cat b) a b }
tCat1 :: Cat' (TraverseForN (Cat a) (Cat a')) (NProxy0 2)
tCat1 = makeTraversal @""
-- The type uses (TraverseForN s t) as its HKD control type and a kind matched
-- proxy for a natural number, (NProxy{K} n), for all its "data" variables.
-- Here is a Dat example that targets the "D1" constructor.
tDat1 :: Dat' (TraverseForN (Dat a b c) (Dat a' b' c))
              (NProxy0 2) (NProxy0 3) (NProxy0 4)
tDat1 = makeTraversal @"D1"

-- Writing out the TraverseFor type can be a bother, "MakeTraverseFor"
-- is used to simplify the process. It takes a source type, target type,
-- and a Nat pointing to the HKD control parameter (counting parameters left
-- to right, starting at 1)
-- This resolves to the same traversal as tCat1
tCat1' :: MakeTraverseFor (Cat a) (Cat a') 1
tCat1' = makeTraversal @""
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

--------------------------------------------------------------------------


type AB = AB' HK0
data AB' f a b = A { a_A :: HK f a, num_A :: HK f Int }
               | B { bs_B :: HK f [b] }
              deriving Generic
deriving instance (Constraints (AB' f a b) Show) => Show (AB' f a b)

abs :: [AB String Int]
abs = [ A "1" 1
      , B [0,1,2] ]
abs' :: [ (AB Int Int, AB String Int, AB String String) ]
abs' = foo abs
--   = [ (A 1 1, A "1" 10, A "1" 1)
--     , (B [0,1,2], B [0,1,2], B ["0","1","2"]) ]

foo :: [AB String Int] -> [ (AB Int Int, AB String Int, AB String String) ]
foo = map $ \ab -> ( ab & trav_a_A %~ read
                   , ab & trav_num_A %~ (*10)
                   , ab & trav_bs_B %~ map show )
  where
    tA, tB :: MakeTraversal (AB a b) (AB c d) 1
    tA@A{ a_A = (TraverseForN trav_a_A)
        , num_a = (TraverseForN trav_num_a) } = makeTraversal @"A"
    tB@B{ bs_B = (TraverseForN trav_bs_B) } = makeTraversal @"B"
