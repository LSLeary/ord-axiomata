
-- --< Header >-- {{{

{-#
LANGUAGE
  TypeFamilyDependencies, DataKinds, PatternSynonyms, RankNTypes,
  TypeOperators, PolyKinds, TypeApplications, ScopedTypeVariables,
  TypeSynonymInstances, BangPatterns, BlockArguments, LambdaCase, EmptyCase
#-}


{- |

Description : Axiomata & lemmata for easier use of "Data.Type.Ord"
Copyright   : (c) L. S. Leary, 2025

Axiomata & lemmata for easier use of "Data.Type.Ord".

\[
  \newcommand{\colon}{ \! : }
\]

-}

-- }}}

-- --< Exports >-- {{{

module Data.Type.Ord.Axiomata (

  -- * Sing
  Sing,

  -- * Axiomata
  -- $axiomata

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

  -- * Lemmata

  -- ** Equivalence
  sym,
  transEq,

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
import Data.Type.Ord (OrderingI(..), Compare, Min, Max, type (<=?), type (<=))
import Data.Void (Void)

-- }}}

-- --< Sing >-- {{{

-- | Maps kinds to their corresponding singleton type constructors.
type family   Sing k      = (s :: k -> Type) | s -> k
type instance Sing Nat    = SNat
type instance Sing Char   = SChar
type instance Sing Symbol = SSymbol

-- }}}

-- --< Axiomata >-- {{{

{- $axiomata

@'Compare' \@O@ should give rise to an equivalence relation and a total ordering on @O@.
In particular, we can define:

\[
\begin{align}
  a  <   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{LT} \\
  a  =   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{EQ} \\
  a  >   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{GT} \\
  a \leq b &\iff a < b \lor a = b                            \\
  a \geq b &\iff a > b \lor a = b
\end{align}
\]

These aren't consistent by construction, however—we need more axiomata.

-}

-- }}}

-- --< Axiomata: Equivalence >-- {{{

-- | 'Eq' for @'Sing' e@ with @'Compare' \@e@.
--   Due to the inclusion of 'sub', 'sym' and 'transEq' are demoted to lemmata.
class Equivalence e where

  {- |

  Decidability of equivalence.

  \[
    \forall a, b \colon a = b \lor a \neq b
  \]

  Since 'refl' and 'sub' make them interchangeable, however, we actually use regular type equality for better ergonomics:

  \[
    \forall a, b \colon a \sim b \lor a \not\sim b
  \]

  -}
  (=?)
    :: Sing e a -> Sing e b {- ^ -}
    -> Either (a :~: b -> Void) (a :~: b)

  {- |

  Reflexivity of equivalence.

  \[
    \forall a \colon a = a
  \]

  Can also be read as:

  \[
    \forall a, b \colon a \sim b \implies a = b
  \]

  The other direction of 'sub'.

  -}
  refl
    :: Sing e a {- ^ -}
    -> Compare a a :~: EQ

  {- |

  Substitutability: if two types are equivalent, one can be substituted for the other.

  \[
    \forall a, b \colon a = b \implies a \sim b
  \]

  The other direction of 'refl'.

  -}
  sub
    :: Compare a b ~ EQ
    => Sing e a {- ^ -}
    -> Sing e b
    -> a :~: b

instance Equivalence Nat where
  (=?) = defaultDecideEq
  refl _  = Refl
  sub m@SNat n@SNat = case cmpNat m n of
    EQI -> Refl

instance Equivalence Char where
  (=?) = defaultDecideEq
  refl _  = Refl
  sub m@SChar n@SChar = case cmpChar m n of
    EQI -> Refl

instance Equivalence Symbol where
  (=?) = defaultDecideEq
  refl _  = Refl
  sub m@SSymbol n@SSymbol = case cmpSymbol m n of
    EQI -> Refl

-- }}}

-- --< Axiomata: Total Order >-- {{{

-- | 'Ord' for @'Sing' e@ with @'Compare' \@e@.
class Equivalence o => TotalOrder o where

  {- |

  Decidable connectivity of ordering.

  \[
    \forall a, b \colon a \lt b \lor a = b \lor a \gt b
  \]

  -}
  (<|=|>)
    :: Sing o a -> Sing o b {- ^ -}
    -> OrderingI a b

  {- |

  Anti-symmetry of ordering.

  \[
    \forall a, b \colon a \leq b \iff b \geq a
  \]

  -}
  antiSym
    :: Sing o a -> Sing o b {- ^ -}
    -> Compare a b :~: Reflect (Compare b a)

  {- |

  Transitivity of ordering.

  \[
    \forall a, b, c \colon a \leq b \land b \leq c \implies a \leq c
  \]

  -}
  transTO
    :: (a <= b, b <= c)
    => Sing o a -> Sing o b -> Sing o c {- ^ -}
    -> (a <=? c) :~: True

-- | @Reflect@ an 'Ordering' (to express anti-symmetry).
type family Reflect (o :: Ordering) = (p :: Ordering) | p -> o where
  Reflect LT = GT
  Reflect EQ = EQ
  Reflect GT = LT

instance TotalOrder Nat where
  m@SNat <|=|> n@SNat = cmpNat m n
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
  m@SChar <|=|> n@SChar = cmpChar m n
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
  m@SSymbol <|=|> n@SSymbol = cmpSymbol m n
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
  :: forall o (sing :: o -> Type) (a :: o) (b :: o)
  .  sing a -> sing b
  -> Compare a b :~: Reflect (Compare b a)
unsafeAntiSym !_ !_ = unsafeCoerce (Refl @(Compare a b))

unsafeLtTrans
  :: (Compare a b ~ LT, Compare b c ~ LT)
  => sing a -> sing b -> sing c -> Compare a c :~: LT
unsafeLtTrans !_ !_ !_ = unsafeCoerce (Refl @LT)

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
  Refl -> case m <|=|> n of
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
    \forall a \colon b_l \leq a
  \]

  -}
  least :: Sing o a -> (LowerBound o <=? a) :~: True

instance BoundedBelow Nat where
  type LowerBound Nat = 0
  lowerBound = natSing
  least = unsafeLeast

instance BoundedBelow Char where
  type LowerBound Char = '\NUL'
  lowerBound = charSing
  least = unsafeLeast

instance BoundedBelow Symbol where
  type LowerBound Symbol = ""
  lowerBound = symbolSing
  least = unsafeLeast

unsafeLeast :: Sing o a -> (LowerBound o <=? a) :~: True
unsafeLeast !_ = unsafeCoerce (Refl @True)


-- | 'TotalOrder's with 'UpperBound's.
class TotalOrder o => BoundedAbove o where

  type UpperBound o = (u :: o) | u -> o

  -- | Existence of an upper bound \( b_u \).
  upperBound :: Sing o (UpperBound o)

  {- |

  \( b_u \) is the @greatest@ element of @o@.

  \[
    \forall a \colon a \leq b_u
  \]

  -}
  greatest :: Sing o a -> (a <=? UpperBound o) :~: True

-- }}}

-- --< Lemmata: Equivalence >-- {{{

{- |

Symmetry of equivalence.

\[
  \forall a, b \colon a = b \iff b = a
\]

-}
sym
  :: (Equivalence e, Compare a b ~ EQ)
  => Sing e a -> Sing e b {- ^ -}
  -> Compare b a :~: EQ
sym a b = case sub a b of
  Refl -> Refl

{- |

Transitivity of equivalence.

\[
  \forall a, b, c \colon a = b \land b = c \implies a = c
\]

-}
transEq
  :: (Equivalence e, Compare a b ~ EQ, Compare b c ~ EQ)
  => Sing e a -> Sing e b -> Sing e c {- ^ -}
  -> Compare a c :~: EQ
transEq a b c = case sub a b of
  Refl -> case sub b c of
    Refl -> Refl

-- }}}

-- --< Lemmata: Min >-- {{{

{- |

'Min' is deflationary in its first argument.

\[
  \mathrm{min} \, a \, b \leq a
\]

-}
minDefl1
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (Min a b <=? a) :~: True
minDefl1 a b = case a <|=|> b of
  LTI -> case refl a of
    Refl -> Refl
  EQI -> Refl
  GTI -> case antiSym b a of
    Refl -> Refl

{- |

'Min' is deflationary in its second argument.

\[
  \mathrm{min} \, a \, b \leq b
\]

-}
minDefl2
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (Min a b <=? b) :~: True
minDefl2 a b = case a <|=|> b of
  LTI -> case refl b of
    Refl -> Refl
  EQI -> Refl
  GTI -> case refl b of
    Refl -> Refl

{- |

'Min' is monotonic in both arguments.

\[
  a \leq c \land b \leq d
    \implies \mathrm{min} \, a \, b \leq \mathrm{min} \, c \, d
\]

-}
minMono
  :: (TotalOrder o, a <= c, b <= d)
  => Sing o a -> Sing o b -> Sing o c -> Sing o d {- ^ -}
  -> (Min a b <=? Min c d) :~: True
minMono a b c d = case c <|=|> d of
  LTI -> case minDefl1 a b of
    Refl -> transTO (minTO a b) a c
  EQI -> case minDefl1 a b of
    Refl -> transTO (minTO a b) a c
  GTI -> case minDefl2 a b of
    Refl -> transTO (minTO a b) b d

-- }}}

-- --< Lemmata: Max >-- {{{

{- |

'Max' is inflationary in its first argument.

\[
  a \leq \mathrm{max} \, a \, b
\]

-}
maxInfl1
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (a <=? Max a b) :~: True
maxInfl1 a b = case a <|=|> b of
  LTI -> Refl
  EQI -> Refl
  GTI -> case refl a of
    Refl -> Refl

{- |

'Max' is inflationary in its second argument.

\[
  b \leq \mathrm{max} \, a \, b
\]

-}
maxInfl2
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> (b <=? Max a b) :~: True
maxInfl2 a b = case a <|=|> b of
  LTI -> case refl b of
    Refl -> Refl
  EQI -> Refl
  GTI -> case antiSym b a of
    Refl -> Refl

{- |

'Max' is monotonic in both arguments.

\[
  a \leq c \land b \leq d
    \implies \mathrm{max} \, a \, b \leq \mathrm{max} \, c \, d
\]

-}
maxMono
  :: (TotalOrder o, a <= c, b <= d)
  => Sing o a -> Sing o b -> Sing o c -> Sing o d {- ^ -}
  -> (Max a b <=? Max c d) :~: True
maxMono a b c d = case a <|=|> b of
  LTI -> case maxInfl2 c d of
    Refl -> transTO b d (maxTO c d)
  EQI -> case maxInfl2 c d of
    Refl -> transTO b d (maxTO c d)
  GTI -> case maxInfl1 c d of
    Refl -> transTO a c (maxTO c d)

-- }}}

