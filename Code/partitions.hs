{-# LANGUAGE FlexibleContexts #-} --Programming with generic mutables ?
{-# LANGUAGE AllowAmbiguousTypes #-}

import Control.Exception
import Control.DeepSeq
import Control.Parallel.Strategies

import Data.List
import Data.Maybe

--https://hackage.haskell.org/package/vector
import qualified Data.Vector as V
-- www.fpcomplete.com/haskell/library/vector/
import qualified Data.Vector.Mutable as MV

--import qualified Data.Vector.Unboxed as UB
--import qualified Data.Vector.Storable as SV

import Control.Monad.Primitive
import Control.Monad.ST
--import Data.STRef

--X-- import Control.Monad.LoopWhile


matrixToString :: (Show a) => [a] -> String
matrixToString [] = ""
matrixToString (first:rest) = (show first) ++ "\n" ++ (matrixToString rest)



insertInCell :: [[a]] -> Int -> Int -> a -> [[a]]
insertInCell matrix row column value =
  let (headMatrix, selectedRow:tailMatrix) = splitAt row matrix
      (headRow, tailRow) = splitAt column selectedRow
      newRow = headRow ++ (value : tailRow)
      newMatrix = headMatrix ++ (newRow : tailMatrix)
  in newMatrix

insertInLastCell :: [[a]] -> a -> [[a]]
insertInLastCell buffer =
  let lenBuffer = length buffer
      lenRow = length (buffer !! (lenBuffer-1))
  in insertInCell buffer (lenBuffer-1) (lenRow)



partitions :: Int -> Integer
partitions 0 = 1
partitions n = sum $ map (partitions) [0..n-1]


descendingPartitions :: Int -> Integer
descendingPartitions n = toSmallerPartitions n n
  where
    toSmallerPartitions :: Int -> Int -> Integer
    toSmallerPartitions _ 0 = 1
    toSmallerPartitions 1 _ = 1 -- Eficiencia
    toSmallerPartitions used free
      | used < free = sum $ zipWith (toSmallerPartitions) [1..used] [free-1, free-2..free-used]
      | otherwise   = sum $ zipWith (toSmallerPartitions) [1..free] [free-1, free-2..0]


descendingPartitions' :: Int -> Integer
descendingPartitions' n = shortcutPartitions n n
  where
    shortcutPartitions :: Int -> Int -> Integer
    shortcutPartitions _ 0 = 1
    shortcutPartitions 1 _ = 1
    shortcutPartitions used free
      | used > free = shortcutPartitions free free
      | otherwise   = sum $ zipWith (shortcutPartitions) [used, used-1] [free-used, free]


descendingPartitions'' :: Int -> Integer
descendingPartitions'' n = toSmallerPartitions n n
  where
    toSmallerPartitions :: Int -> Int -> Integer
    toSmallerPartitions _ 0 = 1
    toSmallerPartitions 1 _ = 1 -- Eficiencia
    toSmallerPartitions used free
      | used > free = toSmallerPartitions free free
      | otherwise   = sum $ zipWith (toSmallerPartitions) [1..used] [free-1, free-2..free-used]



dynamicProgPartitions :: Int -> Integer -- O(n^2) memoria, O(n^2*sqrt(n)) computo (*sqrt(n) culpa de linked lists)
dynamicProgPartitions n = last $ last $ dpPartitions [[]] n n n
--  where
dpPartitions :: [[Integer]] -> Int -> Int -> Int -> [[Integer]]
dpPartitions _ 0 0 _ = [[1]] -- Caso base

dpPartitions [[]] used 0 n = dpPartitions (dpPartitions [[]] (used-1) n n) used 0 n
dpPartitions [[]] used free n = dpPartitions (dpPartitions [[]] used (free-1) n) used free n

dpPartitions buffer 0 _ _ = buffer
dpPartitions buffer _ 0 _ = buffer ++ [[1]]
--dpPartitions buffer 1 _ _ = take 1 buffer ++ [1:(buffer !! 1)] -- ++ drop 2 buffer
dpPartitions buffer 1 _ _ = insertInLastCell buffer 1

dpPartitions buffer used free _
  | used > free =
    let value = buffer !! free !! free
    --in take used buffer ++ [(buffer !! used) ++ [value]] -- ++ drop (used+1) buffer
    in insertInLastCell buffer value
  | otherwise   =
    --let value = sum $ zipWith (!!) (take used $ drop 1 buffer) [free-1, free-2..free-used] -- sin atajo
    --let value = sum $ zipWith (!!) (map (buffer !!) [1..used]) [free-1, free-2..free-used] --igual que el anterior, pero mas inef.
    let value = sum $ zipWith (!!) (drop (used-1) buffer) [free, free-used] -- atajo
    --let value = sum $ zipWith (!!) (map (buffer !!) [used-1, used]) [free, free-used] --igual que el anterior, pero mas inef.
    --in take used buffer ++ [(buffer !! used) ++ [value]] -- ++ drop (used+1) buffer
    in insertInLastCell buffer value



hybridPartitions :: Int -> Integer
hybridPartitions n = head $ diagonalPartitions [] n n
  where
    diagonalPartitions :: [Integer] -> Int -> Int -> [Integer]
    diagonalPartitions [] 0 0 = 1:[1]

    diagonalPartitions [] used free =
      diagonalPartitions (diagonalPartitions [] (used-1) (free-1)) used free

    diagonalPartitions (_:buffer) _ 0 = 1:buffer

    diagonalPartitions diagSaved@(_:buffer) used free
      | used > free   = ( buffer!!(len-1-free) ):buffer --dp
      | used == free  =
        if len > used
          then ( buffer!!(len-1-used) ):buffer --dp
          else recursive:recursive:buffer
      | used < free   = recursive:buffer
      where
        len = length buffer
        recursive = sum $ map (head) $ zipWith (diagonalPartitions diagSaved) [1..used] [free-1, free-2..free-used]



dynamicProgPartitions' :: Int -> Integer -- O(2n) memoria, O(n^2) tiempo
dynamicProgPartitions' n = head $ head $ dfPartitions [[]] n n n
  where
    dfPartitions :: [[Integer]] -> Int -> Int -> Int -> [[Integer]]
    dfPartitions _ 0 0 _ = [[1]] -- Caso base

    dfPartitions [[]] used 0 n =
      let rememberedBuffer = take 1 $ dfPartitions [[]] (used-1) n n
      in dfPartitions rememberedBuffer used 0 n
    dfPartitions [[]] used free n =
      dfPartitions (dfPartitions [[]] used (free-1) n) used free n

    dfPartitions buffer _ 0 _ = [1]:buffer
    dfPartitions (rowZero:rest) 1 _ _ = (1:rowZero):rest

    dfPartitions buffer@(rowZero:rest) used free n
      | used > free =
        let value = (buffer !! 1 !! (n-free))
        in (value:rowZero):rest
      | otherwise   =
        let value = sum $ zipWith (!!) buffer [used-1, n-free]
        in (value:rowZero):rest



-- http://www.cs.utsa.edu/~wagner/CS3723/python/fp/part.html
eulerPartitions :: Int -> Integer
eulerPartitions n
  | n < 0     = 0
  | n < 2     = 1
  | otherwise =
    let
        posArgs = map ((-) n) $ zipWith (div) (zipWith (+) [1..n] $ map (3*) $ map (^2) [1..n]) $ repeat 2
        negArgs = zipWith (+) posArgs [1..n]

        sumOfRec = zipWith (+) (map (eulerPartitions) negArgs) (map (eulerPartitions) posArgs)

        plusMinus = take n $ cycle $ map (toInteger) [1, -1]
    in sum $ zipWith (*) plusMinus sumOfRec


eulerPartitions' :: Int -> Integer
eulerPartitions' n = head $ (dpEuler ([0,1,1] ++ (repeat 0)) n)
  where
    dpEuler :: [Integer] -> Int -> [Integer]
    dpEuler buffer@(_:rest) n
      | n < 0           = 0:rest
      | rest !! n > 0   = (rest !! n):rest
      | otherwise       =
        let
            posArgs = map ((-) n) $ zipWith (div) (zipWith (+) [1..n] $ map (3*) $ map (^2) [1..n]) $ repeat 2
            negArgs = zipWith (+) posArgs [1..n]

            posBuffer = fillBuffer buffer posArgs
            recursivePos = map (head . dpEuler posBuffer) posArgs
            negBuffer = fillBuffer posBuffer negArgs
            recursiveNeg = map (head . dpEuler negBuffer) negArgs

            sumOfRec = zipWith (+) recursivePos recursiveNeg

            plusMinus = take n $ cycle oneMinusOne
            value = sum $ zipWith (*) plusMinus sumOfRec

            recursiveBuffer = tail negBuffer
            (headList, oldValue:tailList) = splitAt n recursiveBuffer
          in value:headList ++ value:tailList

        where
          oneMinusOne = map (toInteger) [1, -1]

          fillBuffer :: [Integer] -> [Int] -> [Integer]
          --fillBuffer initialBuffer (first:[]) =
          --  dpEuler initialBuffer first
          fillBuffer initialBuffer [] = initialBuffer
          fillBuffer initialBuffer (first:rest) =
            dpEuler (fillBuffer initialBuffer rest) first


eulerPartitions'' :: Int -> Integer
eulerPartitions'' = last . dpEuler []
  where
    dpEuler :: [Integer] -> Int -> [Integer]
    dpEuler [] 0 = [1]
    dpEuler [] n = dpEuler (dpEuler [] (n-1)) n

    dpEuler buffer n
      | n < 0              = buffer
      | length buffer > n  = buffer
      | otherwise          =
        let
            optN = (+) 1 $ (2 * n) `div` 3 --Cuando k = n, este valor da negativo si n>=1
            posArgs = map ((-) n) $ zipWith (div) (zipWith (+) [1..optN] $ map (3*) $ map (^2) [1..optN]) $ repeat 2
            negArgs = zipWith (+) posArgs [1..optN]

            recursiveBuffer = fillBuffer buffer (posArgs ++ negArgs)

            getBufferValues = (\ buff x -> if x < 0 then 0 else buff !! x)
            recursivePos = map (getBufferValues recursiveBuffer) posArgs
            recursiveNeg = map (getBufferValues recursiveBuffer) negArgs

            sumOfRec = zipWith (+) recursivePos recursiveNeg

            plusMinus = take n $ cycle $ map (toInteger) [1, -1]
            value = sum $ zipWith (*) plusMinus sumOfRec

        in recursiveBuffer ++ [value]

      where
        fillBuffer :: [Integer] -> [Int] -> [Integer]
        fillBuffer initialBuffer [] = initialBuffer
        fillBuffer initialBuffer (first:rest) =
          dpEuler (fillBuffer initialBuffer rest) first

--Se usan mas valores bajos de dpEuler que valores altos,
--por lo que esconderlos al final de la lista no renta
eulerPartitions''' :: Int -> Integer
eulerPartitions''' = head . dpEuler []
  where
    dpEuler :: [Integer] -> Int -> [Integer]
    dpEuler [] 0 = [1]
    dpEuler [] n = dpEuler (dpEuler [] (n-1)) n

    dpEuler buffer n
      | n < 0              = buffer
      | length buffer > n  = buffer
      | otherwise          =
        let
            optN = (+) 1 $ (2 * n) `div` 3 --Cuando k = n, este valor da negativo si n>=1
            posArgs = map ((-) n) $ zipWith (div) (zipWith (+) [1..optN] $ map (3*) $ map (^2) [1..optN]) $ repeat 2
            negArgs = zipWith (+) posArgs [1..optN]

            recursiveBuffer = fillBuffer buffer (posArgs ++ negArgs)

            getBufferValues = (\ buff x -> if x < 0 then 0 else (!!) buff $ ((length buff)-1-x))
            recursivePos = map (getBufferValues recursiveBuffer) posArgs
            recursiveNeg = map (getBufferValues recursiveBuffer) negArgs

            sumOfRec = zipWith (+) recursivePos recursiveNeg

            plusMinus = take n $ cycle $ map (toInteger) [1, -1]
            value = sum $ zipWith (*) plusMinus sumOfRec

        in value:recursiveBuffer
        where
          fillBuffer :: [Integer] -> [Int] -> [Integer]
          fillBuffer initialBuffer [] = initialBuffer
          fillBuffer initialBuffer (first:rest) =
            dpEuler (fillBuffer initialBuffer rest) first


tailPartitions :: Int -> Integer
tailPartitions = head . head . tailForgetPartitions [[]] 0 0
  where
    tailForgetPartitions :: [[Integer]] -> Int -> Int -> Int -> [[Integer]]
    tailForgetPartitions buffer used 0 n = tailForgetPartitions ([1]:buffer) used 1 n
    tailForgetPartitions buffer@(first:_) used free n
      | free > n =
        if used == n
          then buffer
          else tailForgetPartitions [first] (used+1) 0 n
    tailForgetPartitions (first:rest) 0 free n = tailForgetPartitions ((1:first):rest) 0 (free+1) n
    tailForgetPartitions (first:rest) 1 free n = tailForgetPartitions ((1:first):rest) 1 (free+1) n
    tailForgetPartitions buffer@(first:rest) used free n
      | used > free =
        let value = buffer !! 1 !! (n - free)
        in tailForgetPartitions ((value:first):rest) used (free+1) n
      | otherwise   =
        let value = sum $ zipWith (!!) buffer [used-1, n-free]
        in tailForgetPartitions ((value:first):rest) used (free+1) n


tailPartitions' :: Int -> Integer
tailPartitions' n = head $ head $ tailForgetPartitions [[]] n n n
  where
    tailForgetPartitions :: [[Integer]] -> Int -> Int -> Int -> [[Integer]]
    tailForgetPartitions buffer 0 (-1) _ = buffer
    tailForgetPartitions (first:_) used (-1) n = tailForgetPartitions [[1], first] (used-1) (n-1) n
    tailForgetPartitions (first:rest) used free n
      | used > n-2    = tailForgetPartitions ((1:first):rest) used (free-1) n
    tailForgetPartitions buffer@(first:rest) used free n
      | used < free   =
        let value = buffer !! 1 !! free
        in tailForgetPartitions ((value:first):rest) used (free-1) n
      | otherwise     =
        let value = sum $ zipWith (!!) buffer [n-used-1, free]
        in tailForgetPartitions ((value:first):rest) used (free-1) n



onelinePartitions :: Int -> Integer
onelinePartitions n = head $ dpOnelinePartitions [] 0 n n
  where
    dpOnelinePartitions :: [Integer] -> Int -> Int -> Int -> [Integer]
    dpOnelinePartitions [] 0 _ n = dpOnelinePartitions (replicate (n+1) 1) 2 n n -- Arrayinit
    --Processing
    dpOnelinePartitions buffer@(first:rest) used free n
    --  | used > n    = buffer
      | used > free = buffer
      | free == n   = dpOnelinePartitions updated (used+1) n n
      | otherwise   = updated
      where
        processedSoFar = dpOnelinePartitions rest used (free-1) n
        value = first + (processedSoFar !! (used-1))
        updated = value:processedSoFar


onelinePartitions' :: Int -> Integer
onelinePartitions' n = head $ fst $ dpOnelinePartitions [] [] 0 0 n
  where
    dpOnelinePartitions :: [Integer] -> [Integer] -> Int -> Int -> Int -> ([Integer], [Integer])
    dpOnelinePartitions _ _ 0 _ n = dpOnelinePartitions (replicate (n+1) 1) [] 2 0 n
    dpOnelinePartitions headB [] used free n
      | used > n = (headB, [])
      | otherwise = dpOnelinePartitions [] (reverse headB) used free n

    dpOnelinePartitions headB (currentValue:tailB) used free n
      | free == n   = dpOnelinePartitions (value:headB) tailB (used+1) 0 n
      | used > free = dpOnelinePartitions (currentValue:headB) tailB used (free+1) n
      | otherwise   = dpOnelinePartitions (value:headB) tailB used (free+1) n
      where
        value = currentValue + (headB !! (used-1))

onelinePartitions'' :: Int -> Integer
onelinePartitions'' n = last $ dpOnelinePartitions (replicate (n+1) 1) 2 n
  where
    dpOnelinePartitions :: [Integer] -> Int -> Int -> [Integer]
    dpOnelinePartitions buffer used n
      | used > n  = buffer
      | otherwise = dpOnelinePartitions updated (used+1) n
      where
        --updated = zipWith (+) buffer (replicate used 0 ++ updated)
        (alreadyComputed, rest) = splitAt used buffer
        updated = alreadyComputed ++ zipWith (+) rest updated

onelinePartitions''' :: Int -> Integer
onelinePartitions''' n = head $ dpOnelinePartitions (replicate (n+1) 1) 2 n
  where
    dpOnelinePartitions :: [Integer] -> Int -> Int -> [Integer]
    dpOnelinePartitions buffer used n
      | used > n  = buffer
      | otherwise = dpOnelinePartitions updated (used+1) n
      where
        --updated = zipWith (+) buffer (replicate used 0 ++ updated)
        (rest, alreadyComputed) = splitAt (n+1-used) buffer
        updated = updating rest alreadyComputed used

        updating :: [Integer] -> [Integer] -> Int -> [Integer]
        updating [] initial _ = initial
        updating (first:rest) initial used =
          let buffer = updating rest initial used
          in ( first + (buffer !! (used-1)) ) : buffer

accumulatorPartitions :: Int -> Integer
accumulatorPartitions = head . accumImplementation [] 0
  where
    accumImplementation :: [Integer] -> Int -> Int -> [Integer]
    accumImplementation _ _ 0 = [1]
    accumImplementation [] 0 n = accumImplementation (replicate (n) 1) 2 n
    accumImplementation (first:[]) _ _ = [first]
    accumImplementation buffer@(first:rest) used n
    --  | used > n            = buffer
      | len == (n+2 -used)  =
        let bufferWithAccum = (first + headOfdp):dp
        in accumImplementation bufferWithAccum (used+1) n
      | len > used          =
        let value = first + (processedSoFar !! (used-1))
        in value:processedSoFar
      | otherwise           = buffer

      where
        len = length buffer
        processedSoFar@(headOfdp:dp) = accumImplementation rest used n

accumulatorPartitions' :: Int -> Integer
accumulatorPartitions' n = head $ accumImplementation [] 0 n n
  where
    accumImplementation :: [Integer] -> Int -> Int -> Int -> [Integer]
    accumImplementation _ _ _ 0 = [1]
    accumImplementation [] 0 _ n = accumImplementation (replicate (n) 1) 2 n n
    accumImplementation (first:[]) _ _ _ = [first]
    accumImplementation buffer@(first:rest) used free n
    --  | used > n    = buffer
      | free == n   =
        let headOfdp:dp = accumImplementation rest used (n+1 -used) n
            bufferWithAccum = (first + headOfdp):dp
        in accumImplementation bufferWithAccum (used+1) n n
      | used < free =
        let processedSoFar = accumImplementation rest used (free-1) n
            value = first + (processedSoFar !! (used-1))
        in value:processedSoFar
      | otherwise   = buffer


accumulatorPartitions'' :: Int -> Integer
accumulatorPartitions'' n = head $ accumImplementation [] 0 n n
  where
    accumImplementation :: [Integer] -> Int -> Int -> Int -> [Integer]
    accumImplementation _ _ _ 0 = [1]
    accumImplementation [] 0 _ n = accumImplementation (replicate (n) 1) 2 n n
    accumImplementation (first:[]) _ _ _ = [first]
    accumImplementation buffer@(first:rest) used free n
    --  | used > n    = buffer
      | free == n   =
        let headOfdp:dp = accumImplementation rest used (n+1 -used) n
            bufferWithAccum = (first + headOfdp):dp
        in if 2*used < n
          then accumImplementation bufferWithAccum (used+1) n n
          else sum bufferWithAccum:[]

      | used < free =
        let processedSoFar = accumImplementation rest used (free-1) n
            value = first + (processedSoFar !! (used-1))
        in value:processedSoFar

      | otherwise   = buffer


bufferPartitions :: Int -> Integer
bufferPartitions n = head $ purePartitions [] n
  where
    purePartitions :: [Integer] -> Int -> [Integer]
    purePartitions [] 0 = [1]
    purePartitions [] 1 = 1:purePartitions [] 0
    purePartitions [] n = purePartitions (purePartitions [] (n-1)) n
    purePartitions buffer@(_:partsNminus2AndBeyond) n =
      let reversePartitions = reverse partsNminus2AndBeyond
          accum = sum [inbetweenPartitions reversePartitions (n-x) x | x <- [0..(n-2)]]
      in (1 + accum):buffer

    inbetweenPartitions :: [Integer] -> Int -> Int -> Integer
    inbetweenPartitions buffer used free = (buffer !! free) -
      if used < free
        then sum [ inbetweenPartitions buffer x (free-x) | x <- [(used+1)..free]]
        else 0

bufferPartitions' :: Int -> Integer
bufferPartitions' = head . purePartitions
  where
    purePartitions :: Int -> [Integer]
    purePartitions 0 = [1]
    purePartitions n =
      let buffer@(_:partsNminus2AndBeyond) = purePartitions (n-1)
          reversePartitions = reverse partsNminus2AndBeyond
          accum = sum $ zipWith (inbetweenPartitions reversePartitions) [n, n-1..2] [0..n-2]
      in (1 + accum):buffer

    inbetweenPartitions :: [Integer] -> Int -> Int -> Integer
    inbetweenPartitions buffer used free = (buffer !! free) - sum minusParts
      where
        minusParts = zipWith (inbetweenPartitions buffer) [(used+1)..free] [free-used-1, free-used-2..0]

bufferPartitions'' :: Int -> Integer
bufferPartitions'' = head . purePartitions
  where
    purePartitions :: Int -> [Integer]
    purePartitions 0 = [1]
    purePartitions n = accum:pureNminus1
      where
        pureNminus1 = purePartitions (n-1)
        ibParts = [ inbetweenPartitions (drop (x-1) pureNminus1) x (n-x) | x <- [2..n] ]
--        ibParts = [ inbetweenPartitions (drop (x-1) pureNminus1) x (n-x) | x <- [n, n-1..2] ]
        accum = foldl' (+) 1 ibParts

    inbetweenPartitions :: [Integer] -> Int -> Int -> Integer
    inbetweenPartitions (thisPartition:restIB) used free = (-) thisPartition $ sum minusParts
      where
        minusParts = [ inbetweenPartitions (drop (x-1) restIB) x (free-x) | x <- [used+1..free] ]
--        minusParts = [ inbetweenPartitions (drop (x-1) restIB) x (free-x) | x <- [free, free-1..used+1] ]



pentagonalPartitions :: Int -> Integer
pentagonalPartitions = head . dpPentagonal []
  where
    dpPentagonal :: [Integer] -> Int -> [Integer]
    dpPentagonal [] 0 = [1]
    dpPentagonal [] n = dpPentagonal (dpPentagonal [] (n-1)) n
    dpPentagonal buffer n = value:buffer
        where
          pentagonalFormula = \ x -> (x+x+x-1) * x `div` 2
          posPentagonal = map (pentagonalFormula) [1..]
          negPentagonal = zipWith (+) posPentagonal [1..]

          --posLessThanN = [ posP-1 | posP <- take n posPentagonal, posP <= n]
          --negLessThanN = [ negP-1 | negP <- take n negPentagonal, negP <= n]

          --optN = floor $ sqrt $ fromIntegral n -- Considera menos casos asegurando el resultado
          --posLessThanN = [ posP-1 | posP <- take optN posPentagonal, posP <= n]
          --negLessThanN = [ negP-1 | negP <- take optN negPentagonal, negP <= n]
          --Considera solo los casos que necesita
          posLessThanN = [ posP-1 | posP <- takeWhile (<=n) posPentagonal]
          negLessThanN = [ negP-1 | negP <- takeWhile (<=n) negPentagonal]

          dpPos = map ((!!) buffer) posLessThanN
          dpNeg = map ((!!) buffer) negLessThanN

          plusMinus = cycle $ map (toInteger) [1, -1]
          onlyPos = sum $ zipWith (*) plusMinus dpPos
          value = (+) onlyPos $ sum $ zipWith (*) plusMinus dpNeg


pentagonalPartitions' :: Int -> Integer
pentagonalPartitions' = head . dpPentagonal
  where
    dpPentagonal :: Int -> [Integer]
    dpPentagonal 0 = [1]
    dpPentagonal n = value : buffer
        where
          posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
          negPentagonal = zipWith (+) posPentagonal [1..]

          posLessThanN = getLessThanN n $ map (flip (-) 1) posPentagonal
          negLessThanN = getLessThanN n $ map (negate . (-) 1) negPentagonal

          buffer = dpPentagonal (n-1)
          dpPos = map ((!!) buffer) posLessThanN
          dpNeg = map ((!!) buffer) negLessThanN

          plusMinus = cycle $ map (toInteger) [1, -1]
          onlyPos = zipWith (*) plusMinus dpPos
          onlyNeg = zipWith (*) plusMinus dpNeg

          value = sum $ onlyPos ++ onlyNeg

          getLessThanN :: Int -> [Int] -> [Int]
          getLessThanN n (first:rest)
            | first < n = first:getLessThanN n rest
            | otherwise = []

pentagonalPartitions'' :: Int -> Integer
pentagonalPartitions'' = head . dpPentagonal
  where
    dpPentagonal :: Int -> [Integer]
    dpPentagonal 0 = [1]
    dpPentagonal n = value : buffer
        where
          posPentagonal = 0 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
          negPentagonal = zipWith (+) posPentagonal [1..]

          posLessThanN = takeWhile (<n) posPentagonal
          negLessThanN = takeWhile (<n) negPentagonal

          buffer = dpPentagonal (n-1)
          dpPos = map ((!!) buffer) posLessThanN
          dpNeg = map ((!!) buffer) negLessThanN

          plusMinus = cycle $ map (toInteger) [1, -1]
          onlyPos = sum $ zipWith (*) plusMinus dpPos
          onlyNeg = sum $ zipWith (*) plusMinus dpNeg

          value = onlyPos + onlyNeg

pentagonalPartitions''' :: Int -> Integer
pentagonalPartitions''' n = head $ dpPentagonal posPentagonal negPentagonal n
  where
    sqrtN = ceiling $ sqrt $ fromIntegral n
    posPentagonal = 0 : [x+1 + i+i+i | (i, x) <- zip [1..sqrtN] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..sqrtN]

    dpPentagonal :: [Int] -> [Int] -> Int -> [Integer]
    dpPentagonal _ _ 0 = [1]
    dpPentagonal posPentagonal negPentagonal n = value : buffer
        where
          posLessThanN = takeWhile (<n) posPentagonal
          negLessThanN = takeWhile (<n) negPentagonal

          buffer = dpPentagonal posPentagonal negPentagonal (n-1)
          dpPos = map ((!!) buffer) posLessThanN
          dpNeg = map ((!!) buffer) negLessThanN

          plusMinus = cycle [id, negate]
          onlyPos = foldr1 (+) $ zipWith id plusMinus dpPos
          value = foldr (+) onlyPos $ zipWith id plusMinus dpNeg


pentagonalPartitions'''' :: Int -> Integer --O(n^(2'5))
pentagonalPartitions'''' = head . dpPentagonal pentagonal
  where
    posPentagonal = 0 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = alternate posPentagonal negPentagonal

    alternate :: [Int] -> [Int] -> [Int]
    alternate [] _ = []
    alternate _ [] = []
    alternate (x:xs) (y:ys) = x:y:alternate xs ys

    dpPentagonal :: [Int] -> Int -> [Integer]
    dpPentagonal _ 0 = [1]
    dpPentagonal pentagonal n = value : buffer
        where
          lessThanN = takeWhile (<n) pentagonal
          buffer = dpPentagonal pentagonal (n-1)
          dp = map ((!!) buffer) lessThanN --`using` parList rdeepseq

          plusMinus = cycle [id, id, negate, negate]
          value = foldr1 (+) $ zipWith id plusMinus dp

pentagonalPartitions''''' :: Int -> Integer --Alloc intensive, but O(n^2) pure, best so far
pentagonalPartitions''''' = head . dpPentagonal pentagonal
  where
    posPentagonal = 0 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal

    dpPentagonal :: [Int] -> Int -> [Integer]
    dpPentagonal _ 0 = [1]
    dpPentagonal pentagonal n =  value : buffer
        where
          lessThanN = takeWhile (<n) pentagonal
          buffer = dpPentagonal pentagonal (n-1)
          dp = indexedValues buffer lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = foldr1 (+) $ zipWith id plusMinus dp

          indexedValues :: [Integer] -> [Int] -> [Integer]
          indexedValues = recIndexedValues 0
            where
              recIndexedValues :: Int -> [Integer] -> [Int] -> [Integer]
              recIndexedValues _ [] _ = []
              recIndexedValues _ _ [] = []
              recIndexedValues counter buffer@(first:rest) indexes@(i:is)
                | i == counter = first : recIndexedValues counter buffer is
                | otherwise = recIndexedValues (succ counter) rest indexes


pentagonalPartitionsNoDP :: Int -> Integer
pentagonalPartitionsNoDP = dpPentagonal pentagonal
  where
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal

    dpPentagonal :: [Int] -> Int -> Integer
    dpPentagonal _ 0 = 1
    dpPentagonal pentagonal n = value
        where
          lessThanN = takeWhile (<n) pentagonal
          nsNeeded = map ((-) n) lessThanN

          partitions = map (dpPentagonal pentagonal) nsNeeded

          plusMinus = cycle [id, id, negate, negate]
          value = foldr1 (+) $ zipWith id plusMinus partitions


pentaVectorPartitions :: Int -> Integer -- Aprox O(n^(16/10)) porque O(n^(5/3)) es demasiado
pentaVectorPartitions = V.last . vectorPentagonal pentagonal
  where
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal

    vectorPentagonal :: [Int] -> Int -> V.Vector Integer
    vectorPentagonal _ 0 = V.singleton 1
    vectorPentagonal pentagonal n = V.snoc buffer value
        where
          buffer = vectorPentagonal pentagonal (n-1)
          lessThanN = takeWhile (>=0) $ map ((-) n) pentagonal
          dp = map ((V.!) buffer) lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp

pentaVectorPartitions' :: Int -> Integer --Mejor (supuestamente) porque opera menos, O(n^(ln(3)/ln(2)))
pentaVectorPartitions' = V.head . vectorPentagonal pentagonal
  where
    posPentagonal = 0 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal

    vectorPentagonal :: [Int] -> Int -> V.Vector Integer
    vectorPentagonal _ 0 = V.singleton 1
    vectorPentagonal pentagonal n = V.cons value buffer
        where
          buffer = vectorPentagonal pentagonal (n-1)
          lessThanN = takeWhile (<n) pentagonal
          dp = map ((V.!) buffer) lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp

pentaVectorPartitions'' :: Int -> Integer
pentaVectorPartitions'' = head . vectorPentagonal pentagonal
  where
    posPentagonal = 0 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal

    vectorPentagonal :: [Int] -> Int -> [Integer]
    vectorPentagonal _ 0 = [1]
    vectorPentagonal pentagonal n = value : buffer
        where
          buffer = vectorPentagonal pentagonal (n-1)
          lessThanN = takeWhile (<n) pentagonal
          dp = map ((V.!) (V.fromList buffer)) lessThanN -- Horrible opcion
          -- O(n) para intentar obtener (O(sqrt(n))), contraproducente

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp

pentaUpdateVectorPartitions :: Int -> Integer
pentaUpdateVectorPartitions n = V.last $ vectorPentagonal storage pentagonal n
  where
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal
    storage = V.replicate (n+1) 0

    vectorPentagonal :: V.Vector Integer -> [Int] -> Int -> V.Vector Integer
    vectorPentagonal storage _ 0 = V.update storage $ V.fromList[(0, 1)]
    vectorPentagonal storage pentagonal n = V.update buffer $ V.fromList[(n, value)]
        where
          buffer = vectorPentagonal storage pentagonal (n-1)
          lessThanN = map ((-) n) $ takeWhile (<=n) pentagonal
          dp = map ((V.!) buffer) lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp

pentaUpdateVectorPartitions' :: Int -> Integer
pentaUpdateVectorPartitions' n = V.head $ vectorPentagonal storage pentagonal n
  where
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal
    storage = V.replicate (n+1) 0

    vectorPentagonal :: V.Vector Integer -> [Int] -> Int -> V.Vector Integer
    vectorPentagonal storage _ 0 = V.update storage $ V.fromList[((V.length storage)-1, 1)]
    vectorPentagonal storage pentagonal n = V.update buffer $ V.fromList[(offset, value)]
        where
          buffer = vectorPentagonal storage pentagonal (n-1)

          offset = (V.length buffer)-1 - n
          lessThanN = map ((+) offset) $ takeWhile (<=n) pentagonal

          dp = map ((V.!) buffer) lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp

pentaUpdateVectorPartitions'' :: Int -> Integer
pentaUpdateVectorPartitions'' n = V.head $ vectorPentagonal storage pentagonal n
  where
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal
    storage = V.replicate (n+1) 0

    vectorPentagonal :: V.Vector Integer -> [Int] -> Int -> V.Vector Integer
    vectorPentagonal storage _ 0 = V.update storage $ V.fromList[((V.length storage)-1, 1)]
    vectorPentagonal storage pentagonal n = V.update buffer $ V.fromList[(offset, value)]
        where
          buffer = vectorPentagonal storage pentagonal (n-1)
          offset = (V.length buffer)-1 - n
          effBuffer = V.drop offset buffer

          lessThanN = takeWhile (<=n) pentagonal
          dp = map ((V.!) effBuffer) lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp

pentaUpdateVectorPartitions''' :: Int -> Integer
pentaUpdateVectorPartitions''' n = V.last $ vectorPentagonal storage pentagonal n
  where
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal
    storage = V.replicate (n+1) 1

    vectorPentagonal :: V.Vector Integer -> [Int] -> Int -> V.Vector Integer
    vectorPentagonal storage _ 0 = storage
    vectorPentagonal storage pentagonal n = V.modify (\ v -> MV.write v n value) buffer
        where
          buffer = vectorPentagonal storage pentagonal (n-1)
          lessThanN = map ((-) n) $ takeWhile (<=n) pentagonal
          dp = map ((V.!) buffer) lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp


pentaUpdateVectorPartitions'''' :: Int -> Integer -- A bit unstable, but hard worker
pentaUpdateVectorPartitions'''' n = runST $ do
    storage <- MV.replicate (n+1) (1 :: Integer)
    vectorPentagonal storage pentagonal plusMinus n
    MV.read storage n
  where
    sqrtN = ceiling $ sqrt $ fromIntegral n
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..n]
    pentagonal = take (sqrtN+sqrtN) $ foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal
    plusMinus = take (sqrtN+sqrtN) $ cycle [id, id, negate, negate]

    vectorPentagonal :: (PrimMonad m) =>
                        MV.MVector (PrimState m) Integer ->
                        [Int] ->
                        [Integer -> Integer] ->
                        Int ->
                        m ()
    vectorPentagonal storage _ _ 0 = return ()

    vectorPentagonal storage pentagonal plusMinus n = do
        vectorPentagonal storage pentagonal plusMinus (n-1)
        dp <- mapM (MV.read storage) lessThanN
        MV.write storage n (sum (zipWith id plusMinus dp) )

      where
        lessThanN = takeWhile (>=0) $ map ((-) n) pentagonal

pentaUpdateVectorPartitions''''' :: Int -> Integer
pentaUpdateVectorPartitions''''' n = runST $ do
    storage <- MV.replicate (n+1) (1 :: Integer)
    -- TODO with loops
    MV.read storage n

pentaUpdateVectorFromTheBottomPartitions :: Int -> Integer
pentaUpdateVectorFromTheBottomPartitions n = V.last $ vectorPentagonal pentagonal n n
  where
    posPentagonal = 1 : [x+1 + i+i+i | (i, x) <- zip [1..] posPentagonal]
    negPentagonal = zipWith (+) posPentagonal [1..]
    pentagonal = foldr (\ (x,y) xs -> x:y:xs) [] $ zip posPentagonal negPentagonal

    vectorPentagonal :: [Int] -> Int -> Int -> V.Vector Integer
    vectorPentagonal _ 0 maxN = V.singleton 1 V.++ V.replicate maxN 0
    vectorPentagonal pentagonal n maxN = V.update buffer $ V.fromList[(n, value)]
        where
          buffer = vectorPentagonal pentagonal (n-1) maxN
          lessThanN = map ((-) n) $ takeWhile (<=n) pentagonal
          dp = map ((V.!) buffer) lessThanN

          plusMinus = cycle [id, id, negate, negate]
          value = sum $ zipWith id plusMinus dp


samelinePartitions :: Int -> Integer
samelinePartitions n = runST $ do
    storage <- MV.replicate (n+1) (1 :: Integer)
    dpSamelinePartitions storage 2 0 n
    MV.read storage n
  where
    dpSamelinePartitions :: (PrimMonad m) =>
                            MV.MVector (PrimState m) Integer ->
                            Int -> Int -> Int -> m ()
    dpSamelinePartitions storage used free n
      | used > n    = return ()
      | free > n    = dpSamelinePartitions storage (used+1) 0 n
      | used > free = dpSamelinePartitions storage used used n --Shortcut
      | otherwise   = do
        addValue <- MV.read storage (free - used)
        MV.modify storage ((+) addValue) free
        dpSamelinePartitions storage used (free+1) n


samelinePartitions' :: Int -> Integer
samelinePartitions' n = runST $ do
    storage <- MV.replicate (n+1) (1 :: Integer)
    dpSamelinePartitions storage 2 2 n
    MV.unsafeRead storage n
  where
    dpSamelinePartitions :: (PrimMonad m) =>
                            MV.MVector (PrimState m) Integer ->
                            Int -> Int -> Int -> m ()
    dpSamelinePartitions storage used free n
      | free > n  = if (used+1) > n
                      then return ()
                      else dpSamelinePartitions storage (used+1) (used+1) n
      | otherwise = do
        addValue <- MV.unsafeRead storage (free - used)
        MV.unsafeModify storage ((+) addValue) free
        dpSamelinePartitions storage used (free+1) n

samelinePartitions'' :: Int -> Integer
samelinePartitions'' n = runST $ do
    storage <- MV.replicate (n+1) (1 :: Integer)
    dpSamelinePartitions storage 2 n
    MV.unsafeRead storage n
  where
    dpSamelinePartitions :: (PrimMonad m) =>
                            MV.MVector (PrimState m) Integer ->
                            Int -> Int -> m ()
    dpSamelinePartitions storage used n
      | used > n  = return ()
      | otherwise = do
        --MV.imapM_ yetToCompute ( \ index value -> MV.modify storage ((+) value) (index+used) )
        computePartitions storage (n+1 -used) used n
        dpSamelinePartitions storage (used+1) n
      where

        computePartitions :: (PrimMonad m) =>
                              MV.MVector (PrimState m) Integer ->
                              Int -> Int -> Int -> m ()

        computePartitions _ 0 _ _ = return ()
        computePartitions storage counter used n =
          let index = (n+1 - counter)
          in do
          value <- MV.unsafeRead storage (index -used)
          MV.unsafeModify storage ((+) value) index
          computePartitions storage (counter-1) used n


main :: IO ()
main = do
  -- A 45000 ya tira de swap, no jugarsela
  let n = 1500
  putStrLn $ (++) "n = " $ show n

--  print [(headM, selected, tailM) | (headM, selected:tailM) <- [splitAt x [0..10] | x <- [0..10]]]
--  putStrLn $ matrixToString $ take 5 $ dpPartitions [[]] 20 20 20

--  print $ map (bufferPartitions'') [0..n]

  let functions = init $ tail [ (\ x -> 0),
                  -- < 30000 para ejecuciones que tarden menos de 10s
                  --pentaUpdateVectorPartitions'''',
                  -- < 25000
                  --pentaVectorPartitions',
                  --pentaVectorPartitions,
                  -- < 20000
                  --pentaUpdateVectorPartitions''',
                  --pentaUpdateVectorPartitions,
                  --pentaUpdateVectorPartitions',
                  --pentaUpdateVectorPartitions'',
                  --pentaUpdateVectorFromTheBottomPartitions,
                  --pentaVectorPartitions'',
                  -- < 10000
                  --pentagonalPartitions''''',
                  -- < 8000
                  --pentagonalPartitions'''',
                  -- < 4000
                  --pentagonalPartitions''',
                  --pentagonalPartitions'',
                  --pentagonalPartitions',
                  --pentagonalPartitions,
                  -- < 3000
                  samelinePartitions',
                  samelinePartitions'',
                  samelinePartitions,
                  -- < 2500
                  --eulerPartitions'',
                  -- < 2000
                  --eulerPartitions''',
                  --eulerPartitions',
                  -- < 1700
                  --accumulatorPartitions'',
                  --accumulatorPartitions',
                  -- < 1500
                  --onelinePartitions'',
                  --onelinePartitions',
                  --onelinePartitions,
                  --onelinePartitions''',
                  -- <1300
                  --accumulatorPartitions,
                  -- <750
                  --dynamicProgPartitions',
                  --tailPartitions,
                  --tailPartitions',
                  -- < 300
                  --dynamicProgPartitions,
                  -- < 110
                  --bufferPartitions'',
                  -- < 80
                  --bufferPartitions',
                  --bufferPartitions,
                  --descendingPartitions',
                  --descendingPartitions'',
                  --descendingPartitions,
                  -- < 50
                  --hybridPartitions,
                  --eulerPartitions,
                  --pentagonalPartitionsNoDP,
                  (\ x -> 0) ]

  let readyFunctions = zipWith (map) functions

  return $! force $ readyFunctions $ cycle [[n]]


--  https://oeis.org/A000041
  let correct = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297, 385, 490, 627, 792, 1002, 1255, 1575, 1958, 2436, 3010, 3718, 4565, 5604, 6842, 8349, 10143, 12310, 14883, 17977, 21637, 26015, 31185, 37338, 44583, 53174, 63261, 75175, 89134, 105558, 124754, 147273, 173525]
  let len = length correct

  let results = readyFunctions $ cycle [[0..len-1]]
--  print results
--  print $ zipWith (flip assert) (repeat "OK") $ zipWith (==) results $ cycle [correct]

  return ()

-- DEPRECATED
--  return $! descendingPartitions n

--  print $ map (descendingPartitions) [0..len]
--  print $ zipWith (assert) (zipWith (==) correct $ map (descendingPartitions) [0..len]) [0..]

--  let readyFunctions = map (\ (f, list) -> map (f) list) . zip functions
