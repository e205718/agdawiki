module A2anser where

open import Data.Bool
open import Data.Nat

-- :: は右結合
infixr 40 _::_

-------------------------------------------------------------------------
-- 第1回の復習・課題の解説

{-
data Bool : Set where
true : Bool
 false : Bool

-- not : 否定。真偽値が逆転する。

not : Bool -> Bool
not false = true
not true = false

-- or。二つの引数が両方偽のときは偽。それ以外は真。
-- _記号_ という風に定義すると、a 記号 b のように中置記法で書ける。

_∨_ : Bool -> Bool -> Bool
false ∨ false = false
b1 ∨ b2 = true

-- and。二つの引数が両方真のときのみ真。

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ b2 = false

{-
一つ目の引数を見て、true だったらもう一つの引数をそのまま返し、
false だったら二つ目の引数に関わらず false を返す、としても良い。

_∧_ : Bool → Bool → Bool
true ∧ a = a
false ∧ _ = false
-}

-- if 文。条件部が真なら then 部分、偽なら else 部分を返す。

if_then_else_ : Bool -> Bool -> Bool -> Bool
if true then b2 else b3 = b2
if false then b2 else b3 = b3
-}
{-
data Nat : Set where
zero : Nat
 suc : Nat -> Nat

-- 足し算。第一引数で場合分けしている。

plus : Nat -> Nat -> Nat
plus zero n = n
plus (suc m) n = suc (plus m n)
-}

test : ℕ
test = 3

-- Fin n : 0 から n - 1 までの自然数を集めた n 元集合

data Fin : ℕ → Set where
 z : {n : ℕ} → Fin (suc n)
 s : {n : ℕ} → Fin n → Fin (suc n)

-- z も s も Fin (suc n) の形をしているので、Fin 0 型の要素はない
-- z（0 に相当） は Fin 1, Fin 2, ... に入っている

test0 : Fin 1
test0 = z {0}

test1a : Fin 2
test1a = z

test1b : Fin 2
test1b = s z

test5 : Fin 5
test5 = s (s (s (s z)))

f : Fin 0 -> Fin 1
f x = z

-- Vec A n : 要素が A 型で、長さが n のリスト

data Vec (A : Set) : ℕ → Set where
 [] : Vec A 0
 _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

test6 : Vec ℕ 2
test6 = 3 :: 5 :: []

-- append : 二つのリストをくっつける
-- 二つのリストに含まれる要素は同じ型 A をもつ
-- 長さ n のリストと長さ m のリストをくっつけたら Vec A (n + m) 型のリストになる

append : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
append [] l2 = l2 -- l1 が空なら l2 をそのまま返す
append (x :: l1) l2 = x :: append l1 l2 -- l1 の先頭が x だったら、l1 の残りについて再帰したものの先頭に x を入れる


test7 : Vec ℕ 4
test7 = append test6 test6

-- contain0 : 長さ n の自然数のリストの中に 0 が含まれるかを判定する

contain0 : {n : ℕ} → Vec ℕ n → Bool
contain0 [] = false -- リストが空なら false
contain0 (zero :: l) = true -- 先頭要素が zero なら true
contain0 (suc x :: l) = contain0 l -- 先頭要素が suc x ならリストの残りを調べる

test8 : Bool
test8 = contain0 test6

test9 : Bool
test9 = contain0 (3 :: 5 :: 0 :: 2 :: [])

-- eq : 二つの自然数が等しいかを判定

eq : Nat -> Nat -> Bool
eq zero zero = true
eq zero (suc x) = false
eq (suc x) zero = false
eq (suc x) (suc y) = eq x y　

-- contain : 自然数 i がリストに含まれるかを判定

contain : {n : Nat} -> (Vec Nat n) -> Nat -> Bool
contain [] i = false
contain (first :: rest) i = if_then_else (eq first i) true (contain rest i)

-- sum : 自然数のリストを受け取り、要素の和を返す

sum : {n : Nat} -> (Vec Nat n) -> Nat
sum [] = zero
sum (first :: rest) = plus first (sum rest)