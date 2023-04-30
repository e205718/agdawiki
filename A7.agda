module A7 where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
-- どうしてopenなのかは不明
-- どんどん≡でつなげていきたいときに、そういう証明をさせてくれる。
open import Data.Nat.Properties
--isCommutativeSemiringのレコードを読み込んだことになっている。
open import Algebra.Structures
-- IsCommutativeSemiringの型定義を読み込んだ。

private module M = IsCommutativeSemiring

-- なぜかこれで上手くいく。

assoc = M.+-assoc

--これでassocが使えるようになる。
--いつでもこのやり方で良いのかはまだ分からない。
-- C-c C-o Mとやると、モジュールMの中身が確認できるので便利。
------------------------------------------------------------------------------


--sum n = 1 + 2 + ... + n 
--1からｎまでの和を取る物を帰納法で証明
-- 2 (sum n)  = n(n+1)
--recを使うものと使わない物の２通り試してみる。
recN : {C : Set} → C → (ℕ → C → C) → (ℕ → C)
recN z s zero = z 
recN z s (suc n) = s n (recN z s n)

--recNなし
sum : ℕ → ℕ 
sum zero = zero
sum (suc n) = suc n + sum n


--recNあり
sum2 : ℕ → ℕ
sum2 zero = zero
sum2 n = recN zero (λ m c → c + (suc m)) n 

test1 : ℕ
test1 = sum (suc (suc zero))

--C zeroが成り立って、Cnが成り立つと仮定したとき、C suc nが成り立つなら任意のC nが成り立つ
--帰納法
--indN : {C : ℕ → Set} → C zero → (C n) → C (suc n) → C n
indN : {C : ℕ → Set} → C zero → ((n : ℕ) → C n → C (suc n)) → ((n : ℕ) → C n) 
indN z s zero = z
indN z s (suc n) = s n (indN z s n)

-- lemma1 実際に証明してみる。
-- まずはindNを使わずに書いてみる。
-- いきなりやらずに、まずは手で証明しよう！重要。
-- 方針。以下のように変形していけると考える。
-- 2 * (sum (suc n))
-- = 2 * (suc n + sum n) 
-- = 2 * (suc n) + 2 * sum n
-- = 2 * (suc n) + n * (n + 1)
-- = 2 * (n + 1) + n * (n + 1)
-- = (2 + n) * (n + 1) 
-- = (2 + n) * (1 + n)
-- = (1 + n) * (2 + n)
-- = suc n * (1 + suc n)
-- = suc n * (suc n + 1)

--indNなし
lemma1 : (n : ℕ) → 2 * (sum n) ≡ n * (n + 1)
lemma1 zero = refl --zeroは和積の定義内で証明されるのでreflを返せる
-- ≡をどんどんつなげて書く書き方。transを何回やっても良いが、こちらのほうが楽？
lemma1 (suc n) = 
    --≡をつなげていくかきかたで証明する。
    begin
    2 * (sum (suc n)) 
    ≡⟨ refl ⟩ -- 次式にするために使った証明を書いてい
    -- sumの定義内で証明されているため、refl
    --\<,\>で<>ができる、≡との間に空派がない
    2 * ((suc n) + sum n) 
    ≡⟨ proj₁ (M.distrib isCommutativeSemiring) 2 (suc n) (sum n) ⟩     
    --分配法則を適用したい。分配法則の証明を取らないといけない
    --今回はisCommutativeSemiringのdistrib(分配法則)を使用
    2 * (suc n) + 2 * (sum n)
    -- sum n = n * (n + 1) / 2であり、右側が欲しい。congで取る 
    ≡⟨ cong (_+_ (2 * suc n)) (lemma1 n) ⟩    
    2 * (suc n) + n * (n + 1) 
    ≡⟨ cong (λ x →  2 * x + n * (n + 1)) {suc n} {n + 1} (M.+-comm isCommutativeSemiring 1 n) ⟩
    --  {suc n} {n + 1}はimplicitに何がλ xのxであるかをいってやっている。
    2 * (n + 1) + n * (n + 1)
    ≡⟨ sym (M.distribʳ isCommutativeSemiring (n + 1) 2 n) ⟩ --ʳ \^r
    -- ただのdistribは、定義を見ると、ペアを返すらしい。右バージョンと左バージョンがあるので、上ではproj₁を用いた。
    -- distribʳは始めから右バージョンらしいので、このままつかう。
    (2 + n) * (n + 1)
    ≡⟨ cong (λ x → (2 + n) * x) {n + 1} {1 + n}
           (M.+-comm isCommutativeSemiring n 1) ⟩
    (2 + n) * (1 + n)
    ≡⟨ (M.*-comm isCommutativeSemiring (2 + n) (1 + n)) ⟩
    (1 + n) * (2 + n)
    ≡⟨ refl ⟩
    suc n * (1 + suc n)
    ≡⟨ cong (_*_ (suc n)) (M.+-comm isCommutativeSemiring 1 (suc n)) ⟩
    suc n * (suc n + 1)
    ∎ -- \qed



lemma2 : (n : ℕ) → 2 * (sum n) ≡ n * (n + 1)
lemma2 = indN refl
 (λ n IH → 
    begin
    2 * sum (suc n) 
    ≡⟨ refl ⟩
    2 * ((suc n) + sum n)
    ≡⟨ proj₁ (M.distrib isCommutativeSemiring) 2 (suc n) (sum n) ⟩
    2 * (suc n) + 2 * (sum n)
    ≡⟨ cong (_+_ (2 * suc n)) IH ⟩
    2 * suc n + n * (n + 1)
    ≡⟨ cong (λ x → 2 * x + n * (n + 1)) {suc n} {n + 1} (M.+-comm isCommutativeSemiring 1 n) ⟩
    2 * (n + 1) + n * (n + 1) 
    ≡⟨ sym (M.distribʳ isCommutativeSemiring (n + 1) 2 n) ⟩
    (2 + n) * (n + 1) 
    ≡⟨ cong (λ x → (2 + n) * x) {n + 1} {1 + n} (M.+-comm isCommutativeSemiring n 1) ⟩
    (2 + n) * (1 + n) 
    ≡⟨ M.*-comm isCommutativeSemiring (2 + n) (1 + n) ⟩
    (1 + n) * (2 + n) 
    ≡⟨ refl ⟩
    suc n * (1 + suc n) 
    ≡⟨ cong (_*_ (suc n)) (M.+-comm isCommutativeSemiring 1 (suc n)) ⟩
    (suc n * (suc n + 1))  
    ∎)

--かなり文法に厳しい。
--等式が成り立っているか、<>の前後のインデントが正確であるか、かなり厳しい。
--基本的には、次式のために何の証明が必要かを考えるだけなので楽かもしれない。
