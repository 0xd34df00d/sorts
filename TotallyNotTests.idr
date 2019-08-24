module TotalyNotTests

import Perm

yes1 : Perm [] []
yes1 = PNil

yes2 : Perm [1] [1]
yes2 = PRest PNil

yes3 : Perm [1, 2] [2, 1]
yes3 = PSwap

yes4 : Perm [1, 2, 3] [2, 1, 3]
yes4 = PSwap

yes5 : Perm [1, 2, 3] [1, 3, 2]
yes5 = PRest PSwap

yes6 : Perm [0, 1, 2, 3] [0, 1, 3, 2]
yes6 = PRest (PRest PSwap)

yes7 : Perm [0, 1, 2, 3] [1, 0, 3, 2]
yes7 = PTrans PSwap (PRest (PRest PSwap))

yes8 : Perm [0, 1, 2, 3] [1, 3, 0, 2]
yes8 = let sub = yes7 in PTrans sub (PRest PSwap)

no1 : Perm [] [1] -> Void
no1 (PTrans p1 p2) = case nilPerm (permSym p1) of Refl => no1 p2
