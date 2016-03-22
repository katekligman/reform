{-
Reform, a decompiler for Z-machine story files.
Copyright 2004 Ben Rudiak-Gould.

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You can read the GNU General Public License at this URL:
     http://www.gnu.org/copyleft/gpl.html
-}


module Reform_util (
	makeLookupTable, tableLookup,
	onFst, sortFst, uniq, uniqBy, group,
	showDecHex
) where


import List (sortBy)
import Numeric (showHex)


makeLookupTable :: (Ord a) => [(a,b)] -> LookupTable a b
tableLookup     :: (Ord a) => a -> LookupTable a b -> Maybe b

uniq   :: (Eq a) => [a] -> [a]
uniqBy :: (a -> a -> Bool) -> [a] -> [a]


data LookupTable a b =
  LookupTableBranch (LookupTable a b) a b (LookupTable a b) | LookupTableLeaf

makeLookupTable = makeLookupTable' . uniqFst . sortFst

makeLookupTable' [] = LookupTableLeaf
makeLookupTable' x =
  let (left,((p,q):right)) = splitAt (length x `div` 2) x
  in  LookupTableBranch (makeLookupTable' left) p q (makeLookupTable' right)

tableLookup x LookupTableLeaf = Nothing
tableLookup x (LookupTableBranch left x' y right) =
  case x `compare` x' of
    EQ -> Just y
    LT -> tableLookup x left
    GT -> tableLookup x right


uniq = uniqBy (==)

uniqBy eq (x:xs) = x : uniqBy eq (dropWhile (eq x) xs)
uniqBy eq []     = []

uniqFst :: (Eq a) => [(a,b)] -> [(a,b)]
uniqFst = uniqBy (\(a,_) (b,_) -> a == b)

group :: (Ord a) => [(a,b)] -> [(a,[b])]
group = group' . sortFst
group' ((a,b):xs) = (a, b : map snd p) : group' q
  where (p,q) = break ((a /=) . fst) xs
group' [] = []

sortFst :: (Ord a) => [(a,b)] -> [(a,b)]
sortFst = sortBy (\(a,_) (b,_) -> a `compare` b)


showDecHex :: Int -> String
showDecHex n =
  shows n (" (0x" ++ showHex n ")")


onFst f (x,y) = (f x,y)
