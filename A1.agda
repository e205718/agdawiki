module A1 where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

and : Bool → Bool → Bool
and true true = true
and true false = false
and false _ = false

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat


plus : Nat → Nat → Nat
plus zero m = m
plus (suc n) m = suc (plus n m)

double : Nat → Nat
double zero = zero
double (suc m) = suc (suc (plus m m)) 

double' : Nat → Nat
double' zero = zero
double' (suc m) = plus (suc m) (suc m)


