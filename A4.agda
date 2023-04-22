module A4 where 

open import Data.Bool hiding (_≤_)
open import Data.Nat 
open import Data.Fin hiding (_+_ ; _≤_) --le で≤
open import Data.Vec
open import Relation.Binary.PropositionalEquality --congもあるらしい


-- 項はただの数字か、数字の和からなるか、だとする。
data Term : Set where --Termとは項のこと
    Num : ℕ → Term
    Add : Term → Term → Term

t1 : Term
t1 = Num 3

t2 : Term
t2 = Add (Num 3) (Num 2)

t3 : Term
t3 = Add (Num 2) (Add (Num 1) (Num 3))

size : Term → ℕ --termの長さを調べる関数
size (Num x) = 1
size (Add t4 t5) = 1 + size t4 + size t5

--項の深さを調べる関数を定義する。
--深さとは、（）等で表され、 (A ∧ B) ∨ C は２の深さ、
--((A ∧ B) ∨ C) ∧ D は３の深さで、最も深いのは(A ∧ B) ∨ Cとなる。

depth : Term → ℕ
depth (Num x) = 1
depth (Add t4 t5) = suc (depth t4 ⊔ depth t5) -- ⊔オーダー理論の上限という意味。
--つまりあてはまる要素のなかで最大のものを返すという事。

-- 補題を示す
-- 常にsizeのほうがdepthを上回る、という補題

lemma1 : {a b c : ℕ} -> a ≤ c -> b ≤ c -> a ⊔ b ≤ c
lemma1 z≤n z≤n = z≤n
lemma1 z≤n (s≤s h2) = s≤s h2
lemma1 (s≤s h1) z≤n = s≤s h1
lemma1 (s≤s h1) (s≤s h2) = s≤s (lemma1 h1 h2)

lemma2 : (a b c : ℕ) -> a ≤ b -> a ≤ b + c
lemma2 .0 b c z≤n = z≤n
lemma2 .(suc a) .(suc b) c (s≤s {a} {b} h) = s≤s (lemma2 a b c h)

{-# TERMINATING #-}  
--lemma3の再帰が停止性がないとエラーが出る。Terminating annotationで回避
--厳密には、停止性があるよって強制してるだけらしい。各値の大小関係を明示することで解決するかも。

lemma3 : (a b c : ℕ) -> a ≤ c -> a ≤ b + c
lemma3 .0 b c z≤n = z≤n
lemma3 .(suc a) b .(suc c) (s≤s {a} {c} h) = lemma3 (suc a) b (suc c) (s≤s h)

depth≤size : (t : Term) → (depth t ≤ size t)
depth≤size (Num x) = s≤s z≤n
depth≤size (Add t t₁) = 
    s≤s (lemma1 (lemma2 (depth t) (size t) (size t₁) (depth≤size t))
             (lemma3 (depth t₁) (size t) (size t₁) (depth≤size t₁)))