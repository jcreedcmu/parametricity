module Opetope2 where

data List (A : Set) : Set where
 nil : List A
 cons : A → List A → List A

concat : {A : Set} → List A → List A
concat = {!!}

flat : {A : Set} → List (List A) → List A
flat = {!!}

map : {A B : Set} → (A → B) → List A → List B
map = {!!}

-- a pretree (or higher pretree)
data T : Set where
 leaf : T

 -- a node of an n-dimensional pretree says with an (n-1)-dimensional
 -- pretree `t` what the first expansion step looks like, and then with a
 -- list of n-dimensional subpretrees `ts` specifies the remaining
 -- subpretrees. Some compatibility conditions are required to filter
 -- out the legimate trees. These are hard to encode intrinsically,
 -- so we represent them extrinsically.
 node : (t : T) (ts : List T) → T


-- Addresses within a tree, i.e. locations of nodes
data Addr : T → Set
-- Addresses within a list of trees, i.e. locations of nodes in one of the trees
data Addrs : List T → Set

data Addr where
 here : (t : T) (ts : List T) → Addr (node t ts)
 desc : (t : T) (ts : List T) → Addrs ts → Addr (node t ts)

data Addrs where
 hd : (t : T) (ts : List T) → Addr t → Addrs (cons t ts)
 tl : (t : T) (ts : List T) → Addrs ts → Addrs (cons t ts)

-- Given a tree and an address, get returns what node shape that
-- address is pointing to.
get : (t : T) (a : Addr t) → T
gets : (ts : List T) (a : Addrs ts) → T

get (node t x) (here .t .x) = t
get (node t x) (desc .t .x a) = gets x a
gets (cons x xs) (hd .x .xs a) = get x a
gets (cons x xs) (tl .x .xs a) = gets xs a

data Check : T → T → Set where


allAddrs : (t : T) → List (Addr t)
allAddrs leaf = nil
allAddrs (node t ts) =
  cons (here t ts) {!!}
