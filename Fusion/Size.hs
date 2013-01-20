module Fusion.Size
    ( Size
    , exactly
    , exactSize
    , maxSize
    , unknownSize
    , smaller
    , larger
    , upperBound
    , isEmpty
    )
where

data Size = Exact {-# UNPACK #-} !Int
          | Max {-# UNPACK #-} !Int
          | Unknown deriving (Eq, Read, Show) 

exactly :: Size -> Maybe Int
exactly (Exact n) = Just n
exactly _ = Nothing
{-# INLINE exactly #-}

exactSize :: Int -> Size
exactSize n = Exact n
{-# INLINE exactSize #-}

maxSize :: Int -> Size
maxSize n = Max n
{-# INLINE maxSize #-}

unknownSize :: Size
unknownSize = Unknown
{-# INLINE unknownSize #-}

instance Num Size where
    (+) = addSize
    (-) = subtractSize
    (*) = mulSize
    fromInteger = Exact . fromInteger
    {-# INLINE fromInteger #-}
    abs = id
    {-# INLINE abs #-}
    signum = undefined

add :: Int -> Int -> Int
add a b | ab >= 0 = ab
        | otherwise = overflowError
    where ab = a + b
{-# INLINE add #-}

sub :: Int -> Int -> Int
sub a b | ab >= 0 = ab
        | otherwise = 0
    where ab = a - b
{-# INLINE sub #-}

mul :: Int -> Int -> Int
mul a b | a >= maxBound `div` b = overflowError
        | otherwise = a * b
{-# INLINE mul #-}

addSize :: Size -> Size -> Size
addSize (Exact n) (Exact m) = Exact $ add n m
addSize (Max n) (Exact m) = Max $ add n m
addSize (Exact n) (Max m) = Max $ add n m
addSize (Max n) (Max m) = Max $ add n m
addSize _ _ = Unknown
{-# INLINE addSize #-}

subtractSize :: Size -> Size -> Size
subtractSize (Exact n) (Exact m) = Exact $ sub n m
subtractSize (Max n) (Exact m) = Max $ sub n m
subtractSize (Exact n) (Max _) = Max n
subtractSize a@(Max n) (Max _) = a
subtractSize a@(Max n) Unknown = a
subtractSize (Exact n) Unknown = Max n -- TODO: Is it true??
subtractSize _ _ = Unknown
{-# INLINE subtractSize #-}

mulSize :: Size -> Size -> Size
mulSize (Exact n) (Exact m) = Exact $ mul n m
mulSize (Exact n) (Max m) = Max $ mul n m
mulSize (Max n) (Exact m) = Max $ mul n m
mulSize (Max n) (Max m) = Max $ mul n m
mulSize _ _ = Unknown
{-# INLINE mulSize #-}

larger :: Size -> Size -> Size
larger (Exact n) (Exact m) = Exact (min n m)
larger a@(Exact n) b@(Max m) = if n >= m then a else b
larger a@(Max n) b@(Exact m) = if n >= m then a else b
larger (Max n) (Max m) = Max $ max n m
larger _ _ = Unknown
{-# INLINE larger #-}

smaller :: Size -> Size -> Size
smaller (Exact n) (Exact m) = Exact (min n m)
smaller (Exact n) (Max m) = Max (min n m)
smaller (Max n) (Exact m) = Max (min n m)
smaller (Max n) (Max m) = Max (min n m)
smaller (Exact n) Unknown = Max n
smaller a@(Max _) Unknown = a
smaller Unknown (Exact m) = Max m
smaller Unknown b@(Max _) = b
smaller Unknown Unknown = Unknown
{-# INLINE smaller #-}

upperBound :: Int -> Size -> Int
upperBound _ (Exact n) = n
upperBound _ (Max n) = n
upperBound k Unknown = k
{-# INLINE upperBound #-}

isEmpty :: Size -> Bool
isEmpty (Exact n) = n <= 0
isEmpty (Max n) = n <= 0
isEmpty Unknown = False
{-# INLINE isEmpty #-}

overflowError :: Int
overflowError = error "Fusion.Size: size overflow"
