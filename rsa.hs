import System.Random

millerRabin n 0 = return True
millerRabin n s = do a <- randomRIO (2,300)
                     y <- millerRabin n (s-1)
                     return (witness a n && y)

witness a n = expModular a (n-1) n 1 == (1::Integer)

expModular b 0 m r = r
expModular b e m r
 | e `mod` 2 == 1 = expModular (b * b `mod` m) (e `div` 2) m (r * b `mod` m)
expModular b e m r = expModular (b * b `mod` m) (e `div` 2) m r

geraPrimo = do n <- randomRIO ((2^511),(2^512)-1)
               b <- millerRabin n 100
               if b then return n else geraPrimo

geraPrimoDiferente p = do q <- geraPrimo
                          if (p /= q) then return q else geraPrimoDiferente p

geraPrimos = do p <- geraPrimo
                q <- geraPrimoDiferente p
                return (p,q)

geraPrimoPequeno = do i <- randomRIO(170,1230)
                      return (crivoEratostenes !! i)

crivoEratostenes = crivoEratostenes' [2..]
crivoEratostenes' (x:xs) = x:(crivoEratostenes' $ filter (\a -> a `mod` x /= 0) xs)
