import System.Random

millerRabin n 0 = return True
millerRabin n s = do a <- randomRIO (2,300)
                     y <- millerRabin n (s-1)
                     return (witness a n && y)

witness a n = expModular a (n-1) n == (1::Integer)

expModular b e m = expModular'   b e m 1
expModular' b 0 m r = r
expModular' b e m r
 | e `mod` 2 == 1 = expModular' (b * b `mod` m) (e `div` 2) m (r * b `mod` m)
expModular' b e m r = expModular' (b * b `mod` m) (e `div` 2) m r

geraPrimo = do n <- randomRIO ((2^511),(2^512)-1)
               b <- millerRabin n 100
               if b then return n else geraPrimo

geraPrimoDiferente p = do q <- geraPrimo
                          if p /= q then return q else geraPrimoDiferente p

geraPrimos = do p <- geraPrimo
                q <- geraPrimoDiferente p
                return (p,q)

geraPrimoPequeno = do i <- randomRIO(170,1230)
                      return (crivoEratostenes !! i)

geraE p q = do e <- geraPrimoPequeno
               case extEuclid e ((p-1)*(q-1)) of
                    (1,_,_) -> return e
                    _ -> geraE p q

geraD p q e = modLinSolver e 1 ((p-1)*(q-1))

crivoEratostenes = crivoEratostenes' [2..]
crivoEratostenes' (x:xs) = x:(crivoEratostenes' $ filter (\a -> a `mod` x /= 0) xs)

extEuclid a 0 = (a,1,0)
extEuclid a b = let (d', x', y') = extEuclid b (a `mod` b) in (d', y', (x' - (a `div` b) * y'))


modLinSolver a b n = if b `mod` d == 0 then (((x'*(b `div` d)) `mod` n + (d-1)*(n `div` d)) `mod` n) else (-1)
                         where (d,x',y') = extEuclid a n

chavePublica p q e = let n = p * q in (e,n)

chavePrivada p q e = let d = geraD p q e
                         n = p * q
                     in (d,n)

criptografa e n m = expModular m e n

descriptografa d n c = expModular c d n

main = do (p,q) <- geraPrimos
          e <- geraE p q
          let (_,n) = chavePublica p q e
          let (d,_) = chavePrivada p q e
          putStrLn ("Publica " ++ show (e,n))
          putStrLn ("Privada " ++ show (d,n))
          putStrLn ("")
          let c = criptografa e n 1234567890
          print (c)
          putStrLn("")
          let m = descriptografa d n c
          print (m)
