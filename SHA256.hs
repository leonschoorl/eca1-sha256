{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds       #-}

module SHA256 where

import Types
import Prelude hiding ((/),round)
import CLaSH.Prelude
import Text.Printf
import Data.Char

(/) = div

state0 :: Sha256State
state0 = vreverse $(v[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19::Int32])

ks :: Vec 64 Int32
ks = vreverse $(v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2::Int32])


pad :: [Int8] -> [Int8]
pad xs = xs ++ bit 7 : replicate padN 0 ++ lBytes
  where
    l = length xs
    padN = (64 - (l + 8 + 1)) `mod` 64
    l64 = (fromIntegral (l*8)) :: Unsigned 64
    lBv = toBV l64
    lBvs = [vselect  d0 d1 d8 lBv, vselect d8  d1 d8 lBv, vselect d16 d1 d8 lBv, vselect d24 d1 d8 lBv
           ,vselect d32 d1 d8 lBv, vselect d40 d1 d8 lBv, vselect d48 d1 d8 lBv, vselect d56 d1 d8 lBv]
    lBytes = map fromBV lBvs

-- little endian
i8sTo32le :: [Int8] -> Int32
i8sTo32le [x0,x1,x2,x3] = x0' + shiftL x1' 8 + shiftL x2' 16 + shiftL x3' 24
  where
    x0' = resize x0
    x1' = resize x1
    x2' = resize x2
    x3' = resize x3

i32To8sle :: Int32 -> [Int8]
i32To8sle x = [x0,x1,x2,x3]
  where
    x0 = resize $ m0 .&.  x
    x1 = resize $ m0 .&. (x `shiftR` 8)
    x2 = resize $ m0 .&. (x `shiftR` 16)
    x3 = resize $ m0 .&. (x `shiftR` 24)

-- big endian
i8sTo32be :: Vec 4 Int8 -> Int32
i8sTo32be xs = x0' + shiftL x1' 8 + shiftL x2' 16 + shiftL x3' 24
  where
    x0' = resize $ xs ! 3
    x1' = resize $ xs ! 2
    x2' = resize $ xs ! 1
    x3' = resize $ xs ! 0

i32To8sbe :: Int32 -> Vec 4 Int8
i32To8sbe x = x3 :> x2 :> x1 :> x0 :> Nil
  where
    x0 = resize $ m0 .&.  x
    x1 = resize $ m0 .&. (x `shiftR` 8)
    x2 = resize $ m0 .&. (x `shiftR` 16)
    x3 = resize $ m0 .&. (x `shiftR` 24)

i8sTo32 = i8sTo32be
i32To8s = i32To8sbe

m0 = (2^8-1)


{-
break message into 512-bit chunks
-}

makeChunks :: [Int8] -> [[Int8]]
makeChunks [] = []
makeChunks xs = take 64 xs : (makeChunks (drop 64 xs))
{-
group4 [] = []
group4 (x0:x1:x2:x3 : xs) = [x0,x1,x2,x3] : group4 xs

makeChunks32 :: [Int8] -> [[Int32]]
makeChunks32 xs = map (map i8sTo32) (map (unsafeVector d4 . group4) $ makeChunks xs)
-}
group4' [] = []
group4' (x0:x1:x2:x3 : xs) = i8sTo32 (x3 :> x2 :> x1 :> x0 :> Nil) : group4' xs

makeChunks32' :: [Int8] -> [[Int32]]
makeChunks32' xs = (map group4' $ makeChunks xs)

{-
makeChunk :: [Int8] -> Chunk
makeChunk [] = []
makeChunk [x0,x1,x2,x3, x4,x5,x6,x7, x8,x9,x10,x11] = undefined
-}

type Sha256State = Vec 8 Int32
type Chunk = Vec 16 Int32

processChunks :: Sha256State -> [Chunk] -> Sha256State
processChunks hs [] = hs
processChunks hs (c:cs) = processChunks hs' cs
  where
    hs' = vzipWith (+) hs (processChunk hs c)

{-
for each chunk
copy chunk into first 16 words of the message schedule array w[0..15]
Extend the first 16 words into the remaining 48 words of message schedule array:
for i from 16 to 63
  s0 := (w[i-15] rightrotate 7) xor (w[i-15] rightrotate 18) xor (w[i-15] rightshift 3)
  s1 := (w[i-2] rightrotate 17) xor (w[i-2] rightrotate 19) xor (w[i-2] rightshift 10)
  w[i] := w[i-16] + s0 + w[i-7] + s1
-}

    processChunk :: Sha256State -> Chunk -> Sha256State
    processChunk state xs = vfoldr (flip round) state wks
      where
        wks = vzipWith (+) ws ks
        ws = genMesgSched xs

genMesgSched :: Chunk -> Vec 64 Int32
genMesgSched xs = ws where
  ws = (vreverse wExtended) <++> xs
  wExtended = (snd $ vmapAccumL (\a x -> let a' = updateMesgSched a in (a', vhead a')) xs (vcopy d48 undefined))

updateMesgSched :: Vec 16 Int32 -> Vec 16 Int32
updateMesgSched ws = w16 +>> ws
  where
    w15 = ws ! (16-15)
    w2  = ws ! (16-2)
    s0  = (w15 `rotateR`  7)  `xor`  (w15 `rotateR` 18)  `xor`  (w15 `shiftR`  3)
    s1  = (w2  `rotateR` 17)  `xor`  (w2  `rotateR` 19)  `xor`  (w2  `shiftR` 10)
    w16 = ws ! (16-16) + s0 + ws ! (16-7) + s1
{-
Initialize working variables to current hash value:
a := h0
b := h1
c := h2
d := h3
e := h4
f := h5
g := h6
h := h7

Compression function main loop:
for i from 0 to 63
  S1 := (e rightrotate 6) xor (e rightrotate 11) xor (e rightrotate 25)
  ch := (e and f) xor ((not e) and g)
  temp1 := h + S1 + ch + k[i] + w[i]
  S0 := (a rightrotate 2) xor (a rightrotate 13) xor (a rightrotate 22)
  maj := (a and b) xor (a and c) xor (b and c)
  temp2 := S0 + maj
  h := g
  g := f
  f := e
  e := d + temp1
  d := c
  c := b
  b := a
  a := temp1 + temp2
-}
round :: Sha256State -> Int32 -> Sha256State
--round state wk = unsafeVector d8 [a',a,b,c,e',e,f,g]
round state wk = vreplace (state <<+ a') 4 e'
  where
    a = state ! 0
    b = state ! 1
    c = state ! 2
    d = state ! 3
    e = state ! 4
    f = state ! 5
    g = state ! 6
    h = state ! 7
--    [a,b,c,d,e,f,g,h] = fromVector state
    e' = d + s0
    a' = s1
    s0 = wk + h + ch e f g + e1 e
    s1 = s0 + ma a b c + e0 a
    ch e f g = (e .&. f) `xor` (complement e .&. g)
    ma a b c = (a .&. b) `xor` (a .&. c) `xor` (b .&. c)
    e0 a = (a `rotateR` 2) `xor` (a `rotateR` 13) `xor` (a `rotateR` 22)
    e1 e = (e `rotateR` 6) `xor` (e `rotateR` 11) `xor` (e `rotateR` 25)
{-
Add the compressed chunk to the current hash value:
h0 := h0 + a
h1 := h1 + b
h2 := h2 + c
h3 := h3 + d
h4 := h4 + e
h5 := h5 + f
h6 := h6 + g
h7 := h7 + h
-}
add8 (x0,x1,x2,x3,x4,x5,x6,x7) (y0,y1,y2,y3,y4,y5,y6,y7) = (x0+y0, x1+y1, x2+y2, x3+y3, x4+y4, x5+y5, x6+y6, x7+y7)
{-

Produce the final hash value (big-endian):
digest := hash := h0 append h1 append h2 append h3 append h4 append h5 append h6 append h7
-}

out :: Sha256State -> Vec 32 Int8
out xs = vconcat $ vmap i32To8s $ vreverse xs

showHex :: Vec 32 Int8 -> String
showHex = vfoldl (++) "" . vmap ((printf "%02x" ) . toInteger)

showState :: Sha256State -> String
--showState = showHex . out
showState = tail . vfoldl1 (++) . hexInt32 . vreverse

hexInt32 s = vmap (printf " %08x" . toInteger :: Int32 -> String) s

fromString :: String -> [Int8]
fromString = map (fromIntegral . ord)
{-
sha256 :: String -> [Int8]
sha256 xs = out $ processChunks state0 cs
  where
    cs = makeChunks32' $ pad $ fromString xs

sha256str = showHex . sha256
-}

msgSched :: {-State-} (Vec 16 Int32) -> () -> ({-State-} (Vec 16 Int32), Int32)
msgSched ({-State-} ws) () = ({-State-} ws', out)
  where
    out = vhead ws
    ws' = ws <<+ wj
--    j   = 16 :: Index D16
--    wj  = s1 (ws ! j-2) + (ws ! 16-7) + s0 (ws ! j-15) + ws ! j-16
    wj  = s1 (ws ! 14) + (ws ! 9) + s0 (ws ! 1) + (ws ! 0)
    s0 x = (x `rotateR`  7)  `xor`  (x `rotateR` 18)  `xor`  (x `shiftR`  3)
    s1 x = (x `rotateR` 17)  `xor`  (x `rotateR` 19)  `xor`  (x `shiftR` 10)

{-
    ws = xs <++> (unsafeVector d48 [let w15 = ws ! (i-15)
                                        w2  = ws ! (i-2)
                                        s0  = (w15 `rotateR`  7)  `xor`  (w15 `rotateR` 18)  `xor`  (w15 `shiftR`  3)
                                        s1  = (w2  `rotateR` 17)  `xor`  (w2  `rotateR` 19)  `xor`  (w2  `shiftR` 10)
                 in ws ! (i-16) + s0 + ws ! (i-7) + s1 | i <- [16..63]])
-}
{-
f xs = ws
  where
    ws = xs <++> (unsafeVector d48 [let w15 = ws ! (i-15)
                                        w2  = ws ! (i-2)
                                        s0  = (w15 `rotateR`  7)  `xor`  (w15 `rotateR` 18)  `xor`  (w15 `shiftR`  3)
                                        s1  = (w2  `rotateR` 17)  `xor`  (w2  `rotateR` 19)  `xor`  (w2  `shiftR` 10)
                 in ws ! (i-16) + s0 + ws ! (i-7) + s1 | i <- [16..63]])
-}

padState :: Sha256State -> Chunk
padState xs =  256 :> vcopy d6 0 <++> (1 `shiftL` 31) :> Nil <++> xs


hex2bin :: String -> [Int8]
hex2bin [] = []
hex2bin (x1:x2:xs) = myread ("0x" ++ [x1,x2]) : hex2bin xs
  where
    myread = fromInteger . read
{-
Block 125552
-}
bin = hex2bin ("01000000" ++ "81cd02ab7e569e8bcd9317e2fe99f2de44d49ab2b8851ba4a308000000000000" ++ "e320b6c2fffc8d750423db8b1eb942ae710e951ed797f7affc8892b0f1fc122b" ++ "c7f5d74d" ++ "f2b9441a" ++ "42a14695")

demo = showHex $ vreverse $ out $ processChunks state0 [padState $ processChunks state0 $ map (unsafeVector16) $ makeChunks32' $ pad bin]

unsafeVector16 (x0:x1:x2:x3:x4:x5:x6:x7:x8:x9:x10:x11:x12:x13:x14:x15:[]) = vreverse $ x0:>x1:>x2:>x3:>x4:>x5:>x6:>x7:>x8:>x9:>x10:>x11:>x12:>x13:>x14:>x15:>Nil

