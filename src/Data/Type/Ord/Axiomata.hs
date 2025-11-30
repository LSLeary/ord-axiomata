
-- --< Header >-- {{{

{-#
LANGUAGE
  GADTs, TypeFamilyDependencies, DataKinds, PatternSynonyms, FlexibleContexts
#-}


{- |

Description : Axiomata for easier use of "Data.Type.Ord"
Copyright   : (c) L. S. Leary, 2025

Axiomata for easier use of "Data.Type.Ord".

\(\newcommand{\ldot}{.\,\,}\)

-}

-- }}}

-- --< Exports >-- {{{

module Data.Type.Ord.Axiomata (

  -- * Axiomata

  -- ** Equivalence
  Equivalence(..),

  -- ** Total Order
  TotalOrder(..),
  Reflect,
  minTO, maxTO,
  defaultDecideEq,

  -- ** Bounding
  BoundedBelow(..),
  BoundedAbove(..),

  -- * Miscellaneous Types
  Proof(..),
  Sing,

) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.TypeNats
  ( Nat   , SNat   , pattern SNat   , natSing   , cmpNat
  )
import GHC.TypeLits
  (         SChar  , pattern SChar  , charSing  , cmpChar
  , Symbol, SSymbol, pattern SSymbol, symbolSing, cmpSymbol
  )

-- base
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))
import Data.Type.Ord (OrderingI(..), Compare, Min, Max)
import Data.Void (Void)

-- ord-axiomata
import Data.Type.Ord.Relations

-- }}}

-- --< Axiomata: Equivalence >-- {{{

-- | 'Eq' for @'Sing' e@ with @'Compare' \@e@.
--   Due to the inclusion of 'sub', 'Data.Type.Ord.Lemmata.symEq' and 'Data.Type.Ord.Lemmata.transEq' are demoted to lemmata.
class Equivalence e where

  {- |

  Decidability of equivalence.

  \[
    \forall a, b \ldot
      a = b \lor a \neq b
  \]

  Since 'refl' and 'sub' make them interchangeable, however, we actually use regular type equality for better ergonomics:

  \[
    \forall a, b \ldot
      a \sim b \lor a \not\sim b
  \]

  -}
  (=?)
    :: Sing e a -> Sing e b {- ^ -}
    -> Either (a :~: b -> Void) (a :~: b)

  {- |

  Reflexivity of equivalence.

  \[
    \forall a \ldot
      a = a
  \]

  Can also be read as:

  \[
    \forall a, b \ldot
      a \sim b \implies a = b
  \]

  The other direction of 'sub'.

  -}
  refl
    :: Sing e a {- ^ -}
    -> Proof (a == a)

  {- |

  Substitutability: if two types are equivalent, one can be substituted for the other.

  \[
    \forall a, b \ldot
      a = b \implies a \sim b
  \]

  The other direction of 'refl'.

  -}
  sub
    :: a == b
    => Sing e a {- ^ -}
    -> Sing e b
    -> a :~: b

instance Equivalence Nat where
  (=?) = defaultDecideEq
  refl _  = QED
  sub m@SNat n@SNat = case cmpNat m n of
    EQI -> Refl

instance Equivalence Char where
  (=?) = defaultDecideEq
  refl _  = QED
  sub m@SChar n@SChar = case cmpChar m n of
    EQI -> Refl

instance Equivalence Symbol where
  (=?) = defaultDecideEq
  refl _  = QED
  sub m@SSymbol n@SSymbol = case cmpSymbol m n of
    EQI -> Refl

-- }}}

-- --< Axiomata: Total Order >-- {{{

-- | 'Ord' for @'Sing' e@ with @'Compare' \@e@.
class Equivalence o => TotalOrder o where

  {- |

  Decidable connectivity of ordering.

  \[
    \forall a, b \ldot
      a < b \lor a = b \lor a > b
  \]

  -}
  (<|=|>)
    :: Sing o a -> Sing o b {- ^ -}
    -> OrderingI a b

  {- |

  Anti-symmetry of ordering.

  \[
    \forall a, b \ldot
      a < b \iff b > a
  \]

  -}
  antiSym
    :: Sing o a -> Sing o b {- ^ -}
    -> Compare a b :~: Reflect (Compare b a)

  {- |

  Transitivity of \( \leq \).

  \[
    \forall a, b, c \ldot
      a \leq b \land b \leq c \implies a \leq c
  \]

  -}
  transLeq
    :: (a <= b, b <= c)
    => Sing o a -> Sing o b -> Sing o c {- ^ -}
    -> Proof (a <= c)

-- | @Reflect@ an 'Ordering' (to express anti-symmetry).
type family Reflect (o :: Ordering) = (p :: Ordering) | p -> o where
  Reflect LT = GT
  Reflect EQ = EQ
  Reflect GT = LT

instance TotalOrder Nat where
  m@SNat <|=|> n@SNat = cmpNat m n
  antiSym = unsafeAntiSym
  transLeq l@SNat m@SNat n@SNat = case cmpNat l m of
    LTI -> case cmpNat m n of
      LTI -> case unsafeTransLt l m n of
        QED -> QED
      EQI -> QED
    EQI -> case cmpNat m n of
      LTI -> QED
      EQI -> QED

instance TotalOrder Char where
  m@SChar <|=|> n@SChar = cmpChar m n
  antiSym = unsafeAntiSym
  transLeq l@SChar m@SChar n@SChar = case cmpChar l m of
    LTI -> case cmpChar m n of
      LTI -> case unsafeTransLt l m n of
        QED -> QED
      EQI -> QED
    EQI -> case cmpChar m n of
      LTI -> QED
      EQI -> QED

instance TotalOrder Symbol where
  m@SSymbol <|=|> n@SSymbol = cmpSymbol m n
  antiSym = unsafeAntiSym
  transLeq l@SSymbol m@SSymbol n@SSymbol = case cmpSymbol l m of
    LTI -> case cmpSymbol m n of
      LTI -> case unsafeTransLt l m n of
        QED -> QED
      EQI -> QED
    EQI -> case cmpSymbol m n of
      LTI -> QED
      EQI -> QED

unsafeAntiSym
  :: forall o (sing :: o -> Type) (a :: o) (b :: o)
  .  sing a -> sing b
  -> Compare a b :~: Reflect (Compare b a)
unsafeAntiSym !_ !_ = unsafeCoerce (Refl @(Compare a b))

unsafeTransLt
  :: forall sing a b c
  .  (a < b, b < c)
  => sing a -> sing b -> sing c -> Proof (a < c)
unsafeTransLt !_ !_ !_ = unsafeCoerce (QED @(a < b))

-- | The minimum of two totally-ordered singletons.
minTO :: TotalOrder o => Sing o a -> Sing o b -> Sing o (Min a b)
minTO a b = case a <|=|> b of
  LTI -> a
  EQI -> a
  GTI -> b

-- | The maximum of two totally-ordered singletons.
maxTO :: TotalOrder o => Sing o a -> Sing o b -> Sing o (Max a b)
maxTO a b = case a <|=|> b of
  LTI -> b
  EQI -> b
  GTI -> a

-- | A default implementation of '=?' in terms of '<|=|>'.
defaultDecideEq
  :: forall o a b. TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> Either (a :~: b -> Void) (a :~: b)
defaultDecideEq m n = case refl m of
  QED -> case m <|=|> n of
    LTI -> Left \case{}
    EQI -> Right Refl
    GTI -> Left \case{}

-- }}}

-- --< Axiomata: Bounding >-- {{{

-- | 'TotalOrder's with 'LowerBound's.
class TotalOrder o => BoundedBelow o where

  type LowerBound o = (l :: o) | l -> o

  -- | Existence of a lower bound \( b_l \).
  lowerBound :: Sing o (LowerBound o)

  {- |

  \( b_l \) is the @least@ element of @o@.

  \[
    \forall a \ldot
      b_l \leq a
  \]

  -}
  least :: Sing o a -> Proof (LowerBound o <= a)

instance BoundedBelow Nat where
  type LowerBound Nat = 0
  lowerBound = natSing
  least x = case lowerBound <|=|> x of
    LTI -> QED
    EQI -> QED
    _   -> error "Data.Type.Ord.Axiomata.least @Nat: impossible"

instance BoundedBelow Char where
  type LowerBound Char = '\NUL'
  lowerBound = charSing
  least x = case lowerBound <|=|> x of
    LTI -> QED
    EQI -> QED
    _   -> error "Data.Type.Ord.Axiomata.least @Char: impossible"

instance BoundedBelow Symbol where
  type LowerBound Symbol = ""
  lowerBound = symbolSing
  least x = case lowerBound <|=|> x of
    LTI -> QED
    EQI -> QED
    _   -> error "Data.Type.Ord.Axiomata.least @Symbol: impossible"


-- | 'TotalOrder's with 'UpperBound's.
class TotalOrder o => BoundedAbove o where

  type UpperBound o = (u :: o) | u -> o

  -- | Existence of an upper bound \( b_u \).
  upperBound :: Sing o (UpperBound o)

  {- |

  \( b_u \) is the @greatest@ element of @o@.

  \[
    \forall a \ldot
      a \leq b_u
  \]

  -}
  greatest :: Sing o a -> Proof (a <= UpperBound o)

-- }}}

-- --< Miscellaneous Types >-- {{{

-- | Proof terms.
data Proof c = c => QED

-- | A mapping from kinds to their corresponding singleton type constructors.
type family   Sing k      = (s :: k -> Type) | s -> k
type instance Sing Nat    = SNat
type instance Sing Char   = SChar
type instance Sing Symbol = SSymbol

-- }}}

