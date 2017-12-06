import System.Random
import Data.Char
import Data.List.Split
import Math.NumberTheory.Primes.Factorisation

-- O(s) * witness Obs.: s=100
millerRabin n 0 = return True
millerRabin n s = do a <- randomRIO (2,300)
                     y <- millerRabin n (s-1)
                     return (witness a n && y)

-- O(1) * expModular
witness a n = expModular a (n-1) n == (1::Integer)

-- O(e*2^k)
expModular b e m = expModular' b e m 1
expModular' b 0 m r = r
expModular' b e m r
 | e `mod` 2 == 1 = expModular' (b * b `mod` m) (e `div` 2) m (r * b `mod` m)
expModular' b e m r = expModular' (b * b `mod` m) (e `div` 2) m r

-- O(infinito) haha! teta(n/ln(n))
geraPrimo = do n <- randomRIO ((2^15),(2^16)-1)
               b <- millerRabin n 100
               if b then return n else geraPrimo

-- O(infinito) haha! teta(n/ln(n))
geraPrimoDiferente p = do q <- geraPrimo
                          if p /= q then return q else geraPrimoDiferente p

-- geraPrimo + geraPrimoDiferente
geraPrimos = do p <- geraPrimo
                q <- geraPrimoDiferente p
                return (p,q)

-- O(1) * crivoEratostenes = O(i^2) = O(1)
geraPrimoPequeno = do i <- randomRIO(170,1230)
                      return (crivoEratostenes !! i)

-- Lazy O(1)
crivoEratostenes = crivoEratostenes' [2..]
crivoEratostenes' (x:xs) = x:(crivoEratostenes' $ filter (\a -> a `mod` x /= 0) xs)

-- O(k*2^k)
extEuclid a 0 = (a,1,0)
extEuclid a b = let (d', x', y') = extEuclid b (a `mod` b) in (d', y', (x' - (a `div` b) * y'))

-- O(1) * extEuclid
modLinSolver a b n = if b `mod` d == 0 then (((x'*(b `div` d)) `mod` n + (d-1)*(n `div` d)) `mod` n) else (-1)
                         where (d,x',y') = extEuclid a n

-- O(infinito) - probabilidade?
geraE p q = do e <- geraPrimoPequeno
               case extEuclid e ((p-1)*(q-1)) of
                    (1,_,_) -> return e
                    _ -> geraE p q

-- O(1) * modLinSolver
geraD p q e = modLinSolver e 1 ((p-1)*(q-1))

-- O(k^2)
chavePublica p q e = let n = p * q in (e,n)

-- O(k^2) + geraD
chavePrivada p q e = let d = geraD p q e
                         n = p * q
                     in (d,n)

-- O(1) * expModular
criptografa e n m = expModular m e n

-- O(1) * expModular
descriptografa d n c = expModular c d n

-- Lazy O(1)
limiteLista xs n = (filter (\x -> msgToInt x >= n) xs) /= []

-- O(m/n) ?
converteMensagem n s = map msgToInt (converteMensagem' n s 1)
converteMensagem' n ls e = if limiteLista cs n then (converteMensagem' n ls (e+1)) else cs
                                   where c = (length ls) `div` e + 1
                                         cs = (chunksOf c ls)

-- O(m/n) * intToMsg
converteInteiros xs = foldr1 (++) (map intToMsg xs)

-- O(m) -- m é o tamanho da msg
msgToInt m = msgToInt' m 0
msgToInt' [] e = 0
msgToInt' (x:xs) e = toInteger (ord x) * (256^e) + msgToInt' xs (e+1)

-- O(m) -- m é o tamanho da msg
intToMsg n = intToMsg' n 1
intToMsg' 0 e = ""
intToMsg' n e = [chr (fromEnum d)] ++ intToMsg' (n-m) (e+1) where m = n `mod` (256^e)
                                                                  d = m `div` (256^(e-1))

-- geraPrimos + geraE + chavePublica + chavePrivada + ...
-- ataca domina assintóticamente
ataque msg = do (p,q) <- geraPrimos
                e <- geraE p q
                let (_,n) = chavePublica p q e
                let (d,_) = chavePrivada p q e
                putStrLn ("")
                putStrLn ("Publica " ++ show (e,n))
                putStrLn ("Privada " ++ show (d,n))
                putStrLn ("")
                let ms = converteMensagem n msg
                putStrLn ("Inteiros para a mensagem:")
                print (ms)
                let c = map (criptografa e n) ms
                putStrLn ("\n---CRIPTOGRAFANDO---")
                putStrLn ("\nInteiros criptografados:")
                print (c)
                putStrLn("\nConvertido para texto:")
                print (converteInteiros c)
                putStrLn ("\n---DESCRIPTOGRAFANDO---")
                putStrLn("\nInteiros calculados:")
                let m = map (descriptografa d n) c
                print (m)
                putStrLn ("\nConvertido para texto:")
                print (converteInteiros m)
                putStrLn ("\n---ATAQUE---")
                putStrLn("\nAtaque com factorise descobriu:")
                print (ataca (e,n) c factorise)
                putStrLn("\nAtaque com factAlt descobriu:")
                print (ataca (e,n) c factAlt)
                putStrLn ("")

-- descriptografa + geraD + f (factorise ou factAlt) + converteInteiros
-- f domina assintóticamente
ataca (e,n) c f = converteInteiros m where
                    m = map (descriptografa d n) c
                    d = geraD p q e
                    [(p,_),(q,_)] = f n

-- O(n)
factAlt n = let divide n a = (mod n a == 0) in take 2 (map (\x -> (x,1)) (filter (divide n) crivoEratostenes))
