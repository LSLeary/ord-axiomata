
-- --< Header >-- {{{

{-#
LANGUAGE
  TypeFamilyDependencies, DataKinds, PatternSynonyms, RankNTypes,
  TypeOperators, PolyKinds, TypeApplications, ScopedTypeVariables,
  TypeSynonymInstances, BangPatterns
#-}


{- |

Description : Axiomata & lemmata for easier use of "Data.Type.Ord"
Copyright   : (c) L. S. Leary, 2025

Axiomata & lemmata for easier use of "Data.Type.Ord".

-}

-- }}}

-- --< Exports >-- {{{

module Data.Type.Ord.Axiomata (

  -- * Sing
  Sing,

  -- * Axiomata

  -- ** Equivalence
  Equivalence(..),

  -- ** Total Order
  TotalOrder(..),
  Reflect,
  minTO, maxTO,

  -- ** Bounding
  BoundedBelow(..),
  BoundedAbove(..),

  -- * Lemmata

  -- ** Min
  minDefl1,
  minDefl2,
  minMono,

  -- ** Max
  maxInfl1,
  maxInfl2,
  maxMono,

) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.TypeNats
  ( Nat   , SNat   , pattern SNat   , natSing   , decideNat   , cmpNat
  )
import GHC.TypeLits
  (         SChar  , pattern SChar  , charSing  , decideChar  , cmpChar
  , Symbol, SSymbol, pattern SSymbol, symbolSing, decideSymbol, cmpSymbol
  )

-- base
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))
import Data.Type.Ord (OrderingI(..), Compare, Min, Max, type (<=?))
import Data.Void (Void)

-- }}}

-- --< Sing >-- {{{

-- | Maps kinds to their corresponding singleton type constructors.
type family   Sing k      = (s :: k -> Type) | s -> k
type instance Sing Nat    = SNat
type instance Sing Char   = SChar
type instance Sing Symbol = SSymbol

-- }}}

-- --< Axiomata: Equivalence >-- {{{

-- | 'Eq' for @'Sing' e@ with @'Compare' \@e@.
class Equivalence e where
  (===)
    :: Sing e a -> Sing e b {- ^ -}
    -> Either (a :~: b -> Void) (a :~: b)
  refl
    :: Sing e a {- ^ -}
    -> Compare a a :~: EQ
  sym
    :: Compare a b ~ EQ
    => Sing e a -> Sing e b {- ^ -}
    -> Compare b a :~: EQ
  transEq
    :: (Compare a b ~ EQ, Compare b c ~ EQ)
    => Sing e a -> Sing e b -> Sing e c {- ^ -}
    -> Compare a c :~: EQ

instance Equivalence Nat where
  m@SNat === n@SNat = decideNat m n
  refl _  = Refl
  sym m@SNat n@SNat = case cmpNat m n of
    EQI -> Refl
  transEq l@SNat m@SNat n@SNat = case cmpNat l m of
    EQI -> case cmpNat m n of
      EQI -> Refl

instance Equivalence Char where
  m@SChar === n@SChar = decideChar m n
  refl _  = Refl
  sym m@SChar n@SChar = case cmpChar m n of
    EQI -> Refl
  transEq l@SChar m@SChar n@SChar = case cmpChar l m of
    EQI -> case cmpChar m n of
      EQI -> Refl

instance Equivalence Symbol where
  m@SSymbol === n@SSymbol = decideSymbol m n
  refl _  = Refl
  sym m@SSymbol n@SSymbol = case cmpSymbol m n of
    EQI -> Refl
  transEq l@SSymbol m@SSymbol n@SSymbol = case cmpSymbol l m of
    EQI -> case cmpSymbol m n of
      EQI -> Refl

-- }}}

-- --< Axiomata: Total Order >-- {{{

-- | 'Ord' for @'Sing' e@ with @'Compare' \@e@.
class Equivalence o => TotalOrder o where
  (<?=?>)
    :: Sing o a -> Sing o b {- ^ -}
    -> OrderingI a b
  antiSym
    :: Compare a b ~ p
    => Sing o a -> Sing o b {- ^ -}
    -> Compare b a :~: Reflect p
  transTO
    :: ((a <=? b) ~ True, (b <=? c) ~ True)
    => Sing o a -> Sing o b -> Sing o c {- ^ -}
    -> (a <=? c) :~: True

-- | @Reflect@ an 'Ordering' (to express anti-symmetry).
type family Reflect (o :: Ordering) = (p :: Ordering) | p -> o where
  Reflect LT = GT
  Reflect EQ = EQ
  Reflect GT = LT

instance TotalOrder Nat where
  m@SNat <?=?> n@SNat = cmpNat m n
  antiSym = unsafeAntiSym
  transTO l@SNat m@SNat n@SNat = case cmpNat l m of
    LTI -> case cmpNat m n of
      LTI -> case unsafeLtTrans l m n of
        Refl -> Refl
      EQI -> Refl
    EQI -> case cmpNat m n of
      LTI -> Refl
      EQI -> Refl

instance TotalOrder Char where
  m@SChar <?=?> n@SChar = cmpChar m n
  antiSym = unsafeAntiSym
  transTO l@SChar m@SChar n@SChar = case cmpChar l m of
    LTI -> case cmpChar m n of
      LTI -> case unsafeLtTrans l m n of
        Refl -> Refl
      EQI -> Refl
    EQI -> case cmpChar m n of
      LTI -> Refl
      EQI -> Refl

instance TotalOrder Symbol where
  m@SSymbol <?=?> n@SSymbol = cmpSymbol m n
  antiSym = unsafeAntiSym
  transTO l@SSymbol m@SSymbol n@SSymbol = case cmpSymbol l m of
    LTI -> case cmpSymbol m n of
      LTI -> case unsafeLtTrans l m n of
        Refl -> Refl
      EQI -> Refl
    EQI -> case cmpSymbol m n of
      LTI -> Refl
      EQI -> Refl

unsafeAntiSym
  :: forall a b o sing
  .  Compare a b ~ o
  => sing a -> sing b -> Compare b a :~: Reflect o
unsafeAntiSym !_ !_ = unsafeCoerce (Refl @(Reflect o))

unsafeLtTrans
  :: (Compare a b ~ LT, Compare b c ~ LT)
  => sing a -> sing b -> sing c -> Compare a c :~: LT
unsafeLtTrans !_ !_ !_ = unsafeCoerce (Refl @LT)

-- | The minimum of two totally-ordered singletons.
minTO :: TotalOrder o => Sing o a -> Sing o b -> Sing o (Min a b)
minTO a b = case a <?=?> b of
  LTI -> a
  EQI -> a
  GTI -> b

-- | The maximum of two totally-ordered singletons.
maxTO :: TotalOrder o => Sing o a -> Sing o b -> Sing o (Max a b)
maxTO a b = case a <?=?> b of
  LTI -> b
  EQI -> b
  GTI -> a

-- }}}

-- --< Axiomata: Bounding >-- {{{

-- | 'TotalOrder's with 'LowerBound's.
class TotalOrder o => BoundedBelow o where
  type LowerBound o = (l :: o) | l -> o
  lowerBound :: Sing o (LowerBound o)
  least :: Sing o a -> (LowerBound o <=? a) :~: True

instance BoundedBelow Nat where
  type LowerBound Nat = 0
  lowerBound = natSing
  least n@SNat = case cmpNat lowerBound n of
    LTI -> Refl
    EQI -> Refl
    GTI -> error "least @Nat: n < 0"

instance BoundedBelow Char where
  type LowerBound Char = '\NUL'
  lowerBound = charSing
  least n@SChar = case cmpChar lowerBound n of
    LTI -> Refl
    EQI -> Refl
    GTI -> error "least @Char: c < '\\NUL'"

instance BoundedBelow Symbol where
  type LowerBound Symbol = ""
  lowerBound = symbolSing
  least n@SSymbol = case cmpSymbol lowerBound n of
    LTI -> Refl
    EQI -> Refl
    GTI -> error "least @Symbol: s < \"\""

-- | 'TotalOrder's with 'UpperBound's.
class TotalOrder o => BoundedAbove o where
  type UpperBound o = (u :: o) | u -> o
  upperBound :: Sing o (UpperBound o)
  greatest :: Sing o a -> (a <=? UpperBound o) :~: True

-- }}}

-- --< Lemmata: Min >-- {{{

-- | \[ \mathrm{min} \, a \, b \leq a \]
minDefl1
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (Min a b <=? a) :~: True
minDefl1 a b = case a <?=?> b of
  LTI -> case refl a of
    Refl -> Refl
  EQI -> Refl
  GTI -> case antiSym a b of
    Refl -> Refl

-- | \[ \mathrm{min} \, a \, b \leq b \]
minDefl2
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (Min a b <=? b) :~: True
minDefl2 a b = case a <?=?> b of
  LTI -> case refl b of
    Refl -> Refl
  EQI -> Refl
  GTI -> case refl b of
    Refl -> Refl

-- | \[ a \leq c \land b \leq d
--     \implies \mathrm{min} \, a \, b \leq \mathrm{min} \, c \, d
--   \]
minMono
  :: (TotalOrder o, (a <=? c) ~ True, (b <=? d) ~ True)
  => Sing o a -> Sing o b -> Sing o c -> Sing o d {- ^ -}
  -> (Min a b <=? Min c d) :~: True
minMono a b c d = case c <?=?> d of
  LTI -> case minDefl1 a b of
    Refl -> transTO (minTO a b) a c
  EQI -> case minDefl1 a b of
    Refl -> transTO (minTO a b) a c
  GTI -> case minDefl2 a b of
    Refl -> transTO (minTO a b) b d

-- }}}

-- --< Lemmata: Max >-- {{{

-- | \[ a \leq \mathrm{max} \, a \, b \]
maxInfl1
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (a <=? Max a b) :~: True
maxInfl1 a b = case a <?=?> b of
  LTI -> Refl
  EQI -> Refl
  GTI -> case refl a of
    Refl -> Refl

-- | \[ b \leq \mathrm{max} \, a \, b \]
maxInfl2
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (b <=? Max a b) :~: True
maxInfl2 a b = case a <?=?> b of
  LTI -> case refl b of
    Refl -> Refl
  EQI -> Refl
  GTI -> case antiSym a b of
    Refl -> Refl

-- | \[ a \leq c \land b \leq d
--     \implies \mathrm{max} \, a \, b \leq \mathrm{max} \, c \, d
--   \]
maxMono
  :: (TotalOrder o, (a <=? c) ~ True, (b <=? d) ~ True)
  => Sing o a -> Sing o b -> Sing o c -> Sing o d {- ^ -}
  -> (Max a b <=? Max c d) :~: True
maxMono a b c d = case a <?=?> b of
  LTI -> case maxInfl2 c d of
    Refl -> transTO b d (maxTO c d)
  EQI -> case maxInfl2 c d of
    Refl -> transTO b d (maxTO c d)
  GTI -> case maxInfl1 c d of
    Refl -> transTO a c (maxTO c d)

-- }}}

