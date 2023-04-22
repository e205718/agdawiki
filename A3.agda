module A3 where 

open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_) -- hidingすることで、NatとFinの＋が競合しなくて済む。
open import Data.Vec


n3 : ℕ
n3 = 3

n5 : ℕ
n5 = 2 + 3

fin1-0 : Fin 1 
fin1-0 = zero

fin2-0 : Fin 2
fin2-0 = zero

fin2-1 : Fin 2 
fin2-1 = suc zero

fin5-4 : Fin 5
fin5-4 = suc (suc (suc (suc zero)))

v1 : Vec ℕ 2
v1 = 2 ∷ 4 ∷ [] --Unicodeの:: ∷

v2 : Vec ℕ 3
v2 = 3 ∷ 5 ∷ 6 ∷ []

v3 : Vec ℕ 5
v3 = v1 ++ v2 --リストの結合は++で表す。

--上のように、あらかじめリストの長さが分かっているといいことが多い。
--長さが分かっているリストに対して、任意番目の数を取得する関数を作る。
--Finはインデックス（要素番号）ともとれる。

lookupV : {A : Set }{n : ℕ} → Vec A n → Fin n → A
--lookupV [] n =  からからはなにも取れないので、困る。あり得ないという場合は()を書くことができる。
lookupV [] ()
lookupV (x ∷ list1) zero = x
lookupV (x ∷ list1) (suc n) = lookupV list1 n

t1 : ℕ
t1 = lookupV v2 (suc zero)

------
--長さがはみ出てると、エラーが出るので、実装基準を満たしている
--t2 : ℕ
--t2 = lookupV v2 (suc(suc (suc zero)))

-- あるものがSet型をもつということは、そいつが型であるということ
-- 型のファミリー
-- data Vec (A : Set) : N → Set 
-- Aという型とNをもらってきたら、新しい型を作る


data _eq_ {A : Set} (x : A ) : A → Set where
    refl : x eq x 
-- data _eq_ {A : Set} : A → A → Set where...と書くと、式の中でxが使えない
-- data _eq_ {A : Set} (x : A) → A → Set where...と書くと、スコープの関係でおこられる。

t3 : 5 eq (2 + 3)
t3 = refl


cong : {A B : Set} {x y : A} (f : A → B) → x eq y → (f x) eq (f y)
--cong = ? C-c,C-,で自動的に決まっているところ（暗黙）は示されるが、fは示されない
--つまりfを引数として渡す必要がある。
-- x eq y を引数として渡すが、これはreflなものでなければいけないので、reflを渡す。
-- pでパターンマッチすると、(cong f p = ?)、pはreflになった
--このように進めていくのも良い。
cong f refl = refl

unitPlus : (n : ℕ) → (0 + n) eq n
unitPlus n = refl

unitPlus2 : (n : ℕ) → (n + 0) eq n
unitPlus2 zero = refl
unitPlus2 (suc n) = cong suc (unitPlus2 n)
--unitPlus2 (suc n) = cong suc (unitPlus2 n) は 最初のsuc nから、最後の再起ではnを呼び出している
--つまり、unitPlus2への引数が1ずつ減りながら再帰している。いつかzeroになり、reflを満たす。

symPlus : (n m : ℕ) → n eq m → m eq n
-- symPlus m n p = ?で場合分け
symPlus n .n refl = refl

assocPlus : (l m n : ℕ) → ((l + m) + n) eq (l + (m + n))　
assocPlus zero m n = refl　-- assocPlus l m n を lで場合分け、C-c,C-,でチェっくするとrefl
assocPlus (suc l) m n = cong suc (assocPlus l m n)

transPlus : {A : Set} (l m n : A) → l eq m → m eq n → l eq n
transPlus l .l .l refl refl = refl -- transPlus l m n p1 p2 を　p1とp2で場合分け。