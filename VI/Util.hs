{-# LANGUAGE UnicodeSyntax, DataKinds, TypeApplications, RankNTypes, ScopedTypeVariables, TypeOperators, PolyKinds, NoStarIsType, AllowAmbiguousTypes, TypeFamilies #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Util ( ixM, ixΣ, ixU, lixM, lixΣ, embΣM, embUM, cholU ) where

import Data.Maybe
import Data.Proxy
import GHC.TypeLits
import GHC.TypeLits.Extra
import Data.Functor
import Control.Monad
import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'

import qualified Data.List                    as L
import qualified Data.Vector.Generic          as G
import qualified Data.Vector.Generic.Mutable  as GM

ixM ∷ Int → Int → Int → Int
ixM n i j = n*i + j

ixΣ ∷ Int → Int → Int → Int
ixΣ n i j | i <= j = let k = n - i
                      in (n*(n+1) - k*(k+1)) `div` 2 + (j-i)
          | otherwise = ixΣ n j i

ixU ∷ Int → Int → Int → Maybe Int
ixU n i j | i <= j = let k = n - i
                      in Just $ (n*(n+1) - k*(k+1)) `div` 2 + (j-i)
          | otherwise = Nothing

lixM ∷ Int → [(Int,Int)]
lixM n = [(i,j) | i ← [0..n-1], j ← [0..n-1]]

lixΣ ∷ Int → [(Int,Int)]
lixΣ n = [(i,j) | i ← [0..n-1], j ← [i..n-1]]

diagU ∷ Int → [Int]
diagU n = L.unfoldr go (0,n)
            where
               go (i, 0) = Nothing
               go (i, k) = Just (i, (i+k,k-1))

embΣM ∷ ∀ n. KnownNat n ⇒ LA.L (n * n) ((n * (1 + n)) `Div` 2)
embΣM = let n  = fromInteger (natVal (Proxy ∷ Proxy n))
            js = uncurry (ixΣ n) <$> lixM n
            mkr j = G.modify (\v → GM.write v j 1) (G.replicate n 0)
            Just a = LA.create $ LA'.fromRows $ mkr <$> js
         in a

embUM ∷ ∀ n. KnownNat n ⇒ LA.L (n * n) ((n * (1 + n)) `Div` 2)
embUM = let n  = fromInteger (natVal (Proxy ∷ Proxy n))
            js = catMaybes $ uncurry (ixU n) <$> lixM n
            mkr j = G.modify (\v → GM.write v j 1) (G.replicate n 0)
            Just a = LA.create $ LA'.fromRows $ mkr <$> js
         in a

cholU ∷ ∀ n m. (KnownNat n, KnownNat m,  m ~ ((n * (1 + n)) `Div` 2)) ⇒ LA.R m → (LA.R m, LA.L m m)
cholU = let n       = fromInteger (natVal (Proxy ∷ Proxy n))
            js      = diagU n
            f v y   = fromJust . LA.create $ G.modify (\mv → forM_ js (\j → GM.write mv j (y G.! j))) v
         in \x → let y = LA.extract (exp x) in (f (LA.extract x) y, LA.diag $ f (G.replicate n 1) y)

