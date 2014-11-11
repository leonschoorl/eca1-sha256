{-# LANGUAGE TemplateHaskell #-}
module SHA256 where

import Prelude hiding ((/),round)
import CLasH.HardwareTypes
import Text.Printf
import Data.Char

type Int32 = Unsigned D32
type Int8 = Unsigned D8

(/) = div

state0 :: Sha256State
state0 = $(vTH[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19::Int32])

ks :: Vector D64 Int32
ks = $(vTH[
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
    l64 = (fromIntegral (l*8)) :: Unsigned D64
    lBv = u2bv l64
    lBvs = [vselect  d0 d1 d8 lBv, vselect d8  d1 d8 lBv, vselect d16 d1 d8 lBv, vselect d24 d1 d8 lBv
           ,vselect d32 d1 d8 lBv, vselect d40 d1 d8 lBv, vselect d48 d1 d8 lBv, vselect d56 d1 d8 lBv]
    lBytes = map bv2u lBvs

-- little endian
i8sTo32le :: [Int8] -> Int32
i8sTo32le [x0,x1,x2,x3] = x0' + shiftL x1' 8 + shiftL x2' 16 + shiftL x3' 24
  where
    x0' = resizeUnsigned x0
    x1' = resizeUnsigned x1
    x2' = resizeUnsigned x2
    x3' = resizeUnsigned x3

i32To8sle :: Int32 -> [Int8]
i32To8sle x = [x0,x1,x2,x3]
  where
    x0 = resizeUnsigned $ m0 .&.  x
    x1 = resizeUnsigned $ m0 .&. (x `shiftR` 8)
    x2 = resizeUnsigned $ m0 .&. (x `shiftR` 16)
    x3 = resizeUnsigned $ m0 .&. (x `shiftR` 24)

-- big endian
i8sTo32be :: Vector D4 Int8 -> Int32
i8sTo32be xs = x0' + shiftL x1' 8 + shiftL x2' 16 + shiftL x3' 24
  where
    x0' = resizeUnsigned $ xs ! 3
    x1' = resizeUnsigned $ xs ! 2
    x2' = resizeUnsigned $ xs ! 1
    x3' = resizeUnsigned $ xs ! 0

i32To8sbe :: Int32 -> Vector D4 Int8
i32To8sbe x = x3 +> (x2 +> (x1 +> (singleton x0)))
  where
    x0 = resizeUnsigned $ m0 .&.  x
    x1 = resizeUnsigned $ m0 .&. (x `shiftR` 8)
    x2 = resizeUnsigned $ m0 .&. (x `shiftR` 16)
    x3 = resizeUnsigned $ m0 .&. (x `shiftR` 24)

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
group4' (x0:x1:x2:x3 : xs) = i8sTo32 (unsafeVector d4 [x0,x1,x2,x3]) : group4' xs

makeChunks32' :: [Int8] -> [[Int32]]
makeChunks32' xs = (map group4' $ makeChunks xs)

{-
makeChunk :: [Int8] -> Chunk
makeChunk [] = []
makeChunk [x0,x1,x2,x3, x4,x5,x6,x7, x8,x9,x10,x11] = undefined
-}

type Sha256State = Vector D8 Int32
type Chunk = Vector D16 Int32

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
    processChunk state xs = vfoldl round state wks
      where
        wks = vzipWith (+) ws ks
        ws = xs <++> (unsafeVector d48 [let w15 = ws ! (i-15)
                                            w2  = ws ! (i-2)
                                            s0  = (w15 `rotateR`  7)  `xor`  (w15 `rotateR` 18)  `xor`  (w15 `shiftR`  3)
                                            s1  = (w2  `rotateR` 17)  `xor`  (w2  `rotateR` 19)  `xor`  (w2  `shiftR` 10)
                     in ws ! (i-16) + s0 + ws ! (i-7) + s1 | i <- [16..63]])


{-
Initialize working variables txo current hash value:
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
round state wk = vreplace (a' +>> state) 4 e'
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

out :: Sha256State -> Vector D32 Int8
out xs = vconcat $ vmap i32To8s xs

showHex :: Vector D32 Int8 -> String
showHex = vfoldl (++) "" . vmap ((printf "%02x" ) . toInteger)

{-
showState :: Sha256State -> String
showState = showHex . out
-}

fromString :: String -> [Int8]
fromString = map (fromIntegral . ord)
{-
sha256 :: String -> [Int8]
sha256 xs = out $ processChunks state0 cs
  where
    cs = makeChunks32' $ pad $ fromString xs

sha256str = showHex . sha256
-}

msgSched :: State (Vector D16 Int32) -> () -> (State (Vector D16 Int32), Int32)
msgSched (State ws) () = (State ws', out)
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

f xs = ws
  where
    ws = xs <++> (unsafeVector d48 [let w15 = ws ! (i-15)
                                        w2  = ws ! (i-2)
                                        s0  = (w15 `rotateR`  7)  `xor`  (w15 `rotateR` 18)  `xor`  (w15 `shiftR`  3)
                                        s1  = (w2  `rotateR` 17)  `xor`  (w2  `rotateR` 19)  `xor`  (w2  `shiftR` 10)
                 in ws ! (i-16) + s0 + ws ! (i-7) + s1 | i <- [16..63]])


padState :: Sha256State -> Chunk
padState xs = xs <++> ((1 `shiftL` 31) +> vcopyn (d6) 0) <++> singleton 256

hex2bin :: String -> [Int8]
hex2bin [] = []
hex2bin (x1:x2:xs) = read ("0x" ++ [x1,x2]) : hex2bin xs

{-
Block 125552
-}
bin = hex2bin ("01000000" ++ "81cd02ab7e569e8bcd9317e2fe99f2de44d49ab2b8851ba4a308000000000000" ++ "e320b6c2fffc8d750423db8b1eb942ae710e951ed797f7affc8892b0f1fc122b" ++ "c7f5d74d" ++ "f2b9441a" ++ "42a14695")

demo = showHex $ out $ processChunks state0 [padState $ processChunks state0 $ map (unsafeVector d16) $ makeChunks32' $ pad bin]

