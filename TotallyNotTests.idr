module TotalyNotTests

import Data.List

import Perm

yes1 : [] ~~ []
yes1 = PNil

yes2 : [1] ~~ [1]
yes2 = PRest PNil

yes3 : [1, 2] ~~ [2, 1]
yes3 = PSwap

yes4 : [1, 2, 3] ~~ [2, 1, 3]
yes4 = PSwap

yes5 : [1, 2, 3] ~~ [1, 3, 2]
yes5 = PRest PSwap

yes6 : [0, 1, 2, 3] ~~ [0, 1, 3, 2]
yes6 = PRest (PRest PSwap)

yes7 : [0, 1, 2, 3] ~~ [1, 0, 3, 2]
yes7 = PTrans PSwap (PRest (PRest PSwap))

yes8 : [0, 1, 2, 3] ~~ [1, 3, 0, 2]
yes8 = let sub = yes7 in PTrans sub (PRest PSwap)

no1 : [] ~~ [1] -> Void
no1 (PTrans p1 p2) = case nilPerm (permSym p1) of Refl => no1 p2

no2 : [2] ~~ [3] -> Void
no2 (PTrans p1 p2) = case permSingleton p2 of Refl => no2 p1

no3 : [1, 2] ~~ [1, 3] -> Void
no3 p = let twoIn12 = There Here
            twoIn13 = permPreservesElem p twoIn12
        in case twoIn13 of
                There (There later) => absurd later
