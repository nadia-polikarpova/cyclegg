import Data.List

-- | Maximum tail-segment sum: slow version
mts :: [Int] -> Int
mts xs = maximum (map sum (tails xs))

-- | Fast version
mts' xs = fst (tails' xs)
    where
        tails' []     = (0, 0)
        tails' (x:xs) = 
            let (tmts, tsum) = tails' xs in
            (max tmts (tsum + x), tsum + x) 