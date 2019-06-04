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
import Control.Lens      --package lens, used here for operators, e.g. (^.)
import HKD.Lens
import GHC.TypeLits
import GHC.Generics(Generic)

-- First, define a higher kinded data.
type Character = Character' Z
data Character' f a = Character { name :: HK f String
                                , role :: HK f a }
                    deriving Generic
data Protagonist = Hero | Sidekick deriving Show
data Antagonist = Villian | Henchman deriving Show
deriving instance (Constraints (Character' f a) Show)  --provided by one-liner
  => Show (Character' f a)

-- The 'Character' data is built using a type family, 'HK' which wraps its data
-- in a constructor, except if that constructor is the "zero" constructor, `Z`.
data Z a
type family HK (f :: ( * -> * ) ) a where
  HK Z a = a
  HK f a = f a

-- Make the lenses for the `Character`. The lenses will be held in the fields of
-- the "Lens-kinded data". The Natural Number is the index of the "control"
-- parameter `f`
lensesForCharacters :: LensesOf (Character a) (Character b) 1
lensesForCharacters = makeLensesOf

-- For instance, the `role` lens is taken from the `lensesForCharacters`
roleLens :: Lens (Character a) (Character b) a b
roleLens = getLensOf $ role lensesForCharacters

-- The `nameLens` doesn't involve the type variable,
-- so Character type is unchanged.
nameLens :: Lens (Character a) (Character a) String String
nameLens = getLensOf $ name lensesForCharacters
-- Here's a function we have for turning `Villians` into `Heroes`
redemption :: Antagonist -> Protagonist
redemption Villian = Hero
redemption Henchman = Sidekick

-- Here's a sidekick
evilNumberOne :: Character Antagonist
evilNumberOne = Character "Number One" Henchman
-- And here we use the "role" lens make him switch sides
goodNumberOne = evilNumberOne & roleLens %~ redemption
-- goodNumberOne = Character {name = "Number One", role = Sidekick}

-- And Here, we make some data where things will happen.
type Scene = Scene' Z
data Scene' f a b = Meeting { inAttendence :: HK f [a]
                            , meetingPlace :: HK f Place }
                  | Confrontation { attacker :: HK f [a]
                                  , attackee :: HK f [b]
                                  , confrontationPlace :: HK f Place}
                deriving Generic
data Place = ARoom | TheMountainTop deriving Show
deriving instance (Constraints (Scene' f a b) Show) => Show (Scene' f a b)

-- Make Traversals `Meeting`
meetingTraversals :: TraversalsOf (Scene a b) (Scene a b) 1
meetingTraversals = makeTraversalsOf @"Meeting"
-- like the case of Lenses, individual traversals are held in fields.
meetingAttendeeTraversal :: Traversal (Scene a b) (Scene a b) [a] [a]
meetingAttendeeTraversal = getTraversalOf $ inAttendence meetingTraversals
-- Using the traversal, we can add to the meeting.
someoneWalksIn :: a -> Scene a b -> Scene a b
someoneWalksIn a = meetingAttendeeTraversal %~ (a:)

-- NB: We wouldn't be able to make a type changing traversal,
-- `Traversal (Scene a b) (Scene a' b) [a] [a']`. This is in general true
-- for any type parameter appearing at more than one location in the definition
-- of the data.

-- With the above, however, we could create a traversal that changes the type
-- of `b`
confrontationTraversals :: TraversalsOf (Scene a b) (Scene a b') 1
confrontationTraversals = makeTraversalsOf @"Confrontation"

--Here, villians can change a scene by use of a mindControl Traversal
evilMindControl :: Protagonist -> Antagonist
evilMindControl _ = Henchman
useMindControlGun :: Scene (Character Antagonist) (Character Protagonist)
                  -> Scene (Character Antagonist) (Character Antagonist)
useMindControlGun = getTraversalOf (attackee confrontationTraversals)
                  . mapped . roleLens
                  %~ evilMindControl
--turning this
poorNumberOneTrappedInARoom
  :: Scene (Character Antagonist) (Character Protagonist)
poorNumberOneTrappedInARoom = Confrontation [] [goodNumberOne] ARoom
--into this
numberOneReadyForEvilOnceAgain
  :: Scene (Character Antagonist) (Character Antagonist)
numberOneReadyForEvilOnceAgain = useMindControlGun poorNumberOneTrappedInARoom
-- Confrontation [] [Character "Number One" Henchman}] ARoom

--Also, prisms.
type AB = AB' Z
data AB' f a b = A {getA::(HK f a)} | B (HK f b) deriving Generic
deriving instance (Constraints (AB' f a b) Show) => Show (AB' f a b)
aPrism :: PrismsOf (AB a b) (AB c d) 1
aPrism = makePrismsOf @"A"

its1 = (A 1 :: AB Int ()) ^? getPrismOf (getA aPrism)

--Also, lenses can be made for simple data types, by specifying the
-- target HKD parameter with 0
_1 :: Lens (a,b) (c,b) a c
_1 = getLensOf . fst $ (makeLensesOf :: LensesOf (a,b) (c,d) 0)
