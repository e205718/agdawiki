module A6 where

open import Data.Nat 
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

--recはrecursor（再帰）を意味している。
--C型のものを再起計算したい
--nは回数、結果はCを表している
recN : {C : Set} → C → (Nat → C → C) → (Nat → C)
recN z s zero = z
recN z s (suc n) = s n (recN z s n)

recN1 : {C : Set} → C → (ℕ → C → C) → (ℕ → C)
recN1 z s zero = z
recN1 z s (suc n) = s n (recN1 z s n)
--recN n (f) m → n に f をmかい再帰する

add : Nat → Nat → Nat
add m n = recN m (λ x c → suc c) n

--add1 : ℕ → ℕ → ℕ
--add1 m n = recN1 m (λ x c → suc c) n

mul : Nat → Nat → Nat
-- 4 * 2 = ( 0*n + n ) * m 
mul m n = recN zero (λ m c → add n c) m 

--mul1 : ℕ → ℕ → ℕ
--mul1 m n = recN1 zero (λ m c → add1 n c) m 

fac : Nat → Nat -- 5! = 1*2*3*4*5
fac n = recN (suc zero) (λ x c → mul c (suc x)) n -- cは前の結果 xは今何周目か
-- induction principle（数学的帰納法）
-- C は自然数を受け取る述語
-- C zero が成り立つ 
-- → C n が成り立つことを仮定すると C (succ n) も成り立つ
-- → 任意の n について C n が成り立つ

indN : {C : Nat → Set} → C zero → ((n : Nat) → C n → C (suc n)) → ((n : Nat) → C n)
indN z s zero = z
-- C (suc n)が欲しい、C (suc n)は sから作ることができる。
-- C-c,C-eすると s : (n₁ : Nat) → C n₁ → C (suc n₁)
indN z s (suc n) = s n (indN z s n)

open import Data.Nat
open import Data.Bool

--ペアを作ってみよう方は自由
data _×_ (A B : Set) : Set where
  <_,_> : A → B → A × B

pair1 : ℕ × Bool
pair1 = < 3 , true >

-- ペアの elimination rule 
-- A をもらい、B をもらったら C を返す関数があったら、
-- A と B のペアをもらって C を返す関数ができる
-- C を A あるいは B に置き換えると、上の elimination rule と同じこと
-- なので、generalized elimination ともいう
recP : {A B C : Set} → (A → B → C) → (A × B → C)
--引数の1つ目はAとBを受け取ってCを返すと言う関数。つまりfと言う関数がその機能を持つとしてみれば良い
-- fとペアを引数にとって、Cを返す。Cは、f : A → B → C より、ｆにa b を与えてあげれば良い
recP f < a , b > = f a b

--マンハッタン距離を表してみる
--マンハッタン距離はwiki参照
--簡単に言うと碁盤の目を考えた時のx + y のこと

manhattan : ℕ × ℕ → ℕ
--manhattan < x , y > = x + y
--manhattan < x , y > = recP (λ x y → x + y) < x , y >
--上でも行けるけど、より網羅的？
manhattan pair = recP (λ x y → x + y) pair

--doubleを再帰なしで書く

--double : Nat → Nat
--double zero = zero
--double (suc n) = recN zero (λ m c → suc (suc c)) n
--これも式として成り立つけど、double 2とか売ったら double (suc 1)のことで、doubule 1の結果を返してしまう。


double1 : ℕ → ℕ
double1 zero = zero
double1 n = recN1 zero (λ m c → suc (suc c)) n

--iterator  反復処理に焦点を当てたデータ構造の抽象化 (for とか)
--induction principleは帰納原理(帰納法とか)
--True False Sumのitertorとinduction principleを定義する。

data True : Set where
  tt : True
recT : {C : Set} → C → True → C 
recT c tt = c

indT : {C : True → Set} → C tt → ((t : True) → C t)
indT c tt = c

data False : Set where

recF : {C : Set} → False → C
recF ()

--何してもFalseにしかならないよって意味？
indF : {C : False → Set} → (f : False) → C f
indF ()

data Sum (A B : Set) : Set where
  inl : (a : A) → Sum A B --in Left ,in Right?
  inr : (b : B) → Sum A B


recS : {A B C : Set} → (A → C) → (B → C) → (Sum A B → C)
--立式できればC-c,C-c ,e でできる。
-- f gが成り立つならば、SUMにも同じことが言えるでしょって言う意味
recS f g (inl a) = f a
recS f g (inr b) = g b

--indS : {A B : Set} {C : Sum A B → Set} → C {!!} → C {!!} → C {!!}
--全部Sum A Bを入れろと。まあそうよね、sumは２通りで作れるから頑張る

--inl a と inr b が成り立つようなCならば、全てのパターンマッチをこなしているので、任意のｓに対しても成り立つと言う証明
indS : {A B : Set} {C : Sum A B → Set} → ((a : A) → C (inl a)) → ((b : B) → C (inr b))
          → ((s : Sum A B) → C s)

indS f g (inl a) = f a
indS f g (inr b) = g b


