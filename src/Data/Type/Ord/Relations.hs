
-- --< Header >-- {{{

{-# LANGUAGE GADTs, DataKinds, FlexibleContexts #-}

{- |

Description : Equivalence and order relations
Copyright   : (c) L. S. Leary, 2025

@'Compare' \@O@ should give rise to an equivalence relation and a total ordering on @O@.
In particular, we can define relations:

\[
\begin{align}
  a  <   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{LT} \\
  a  =   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{EQ} \\
  a  >   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{GT} \\
  a \leq b &\iff a < b \lor a = b                            \\
  a \neq b &\iff a < b \lor a > b                            \\
  a \geq b &\iff a = b \lor a > b
\end{align}
\]

These aren't consistent by construction, however—that's why we need axiomata.

N.B. We use and provide fixed versions of these relations from "Data.Type.Ord" as per [#26190](https://gitlab.haskell.org/ghc/ghc/-/issues/26190).

-}

-- }}}

-- --< Exports >-- {{{

module Data.Type.Ord.Relations (

  -- * Assert
  Assert,

  -- ** Precise Relations
  type (<), type (==), type (>),

  -- * Ordering Singletons
  SOrdering(..),
  KnownOrdering,
  knownOrdering,
  compareTypes,

  -- ** Imprecise Relations
  type (<=), type (/=), type (>=),

) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.TypeError (Assert, Unsatisfiable, ErrorMessage(..))

-- base
import Data.Type.Ord
  (Compare, OrdCond, type (<?), type (>?), type (<=?), type (>=?))

-- }}}

-- --< Precise Relations >-- {{{

type x =? y = OrdCond (Compare x y) False True False

type x <  y = (Compare x y ~ LT, Assert (x <? y) (Msg x "<" y))
type x == y = (Compare x y ~ EQ, Assert (x =? y) (Msg x "=" y))
type x >  y = (Compare x y ~ GT, Assert (x >? y) (Msg x ">" y))

-- }}}

-- --< Ordering Singletons >-- {{{

data SOrdering (o :: Ordering) where
  SLT :: SOrdering LT
  SEQ :: SOrdering EQ
  SGT :: SOrdering GT

type KnownOrdering = KnownOrdering_

knownOrdering :: KnownOrdering o => SOrdering o
knownOrdering = knownOrdering_

class    KnownOrdering_ (o :: Ordering) where knownOrdering_ :: SOrdering o
instance KnownOrdering_  LT             where knownOrdering_ = SLT
instance KnownOrdering_  EQ             where knownOrdering_ = SEQ
instance KnownOrdering_  GT             where knownOrdering_ = SGT

compareTypes
  :: KnownOrdering (Compare x y)
  => proxy1 x -> proxy2 y -> SOrdering (Compare x y)
compareTypes _ _ = knownOrdering

-- }}}

-- --< Imprecise Relations >-- {{{

type x /=? y = OrdCond (Compare x y) True False True

type x <= y = (KnownOrdering (Compare x y), Assert (x <=? y) (Msg x "<=" y))
type x /= y = (KnownOrdering (Compare x y), Assert (x /=? y) (Msg x "/=" y))
type x >= y = (KnownOrdering (Compare x y), Assert (x >=? y) (Msg x ">=" y))

-- }}}

-- --< Util >-- {{{

type Msg x op y = Unsatisfiable
  ( Text "Cannot satisfy: " :<>: ShowType x
    :<>: Text " " :<>: Text op :<>: Text " "
    :<>: ShowType y
  )

-- }}}

