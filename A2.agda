module A2 where

open import Data.Nat
open import Data.Bool

infixr 40 _::_ --リストを使用するための物。右結合で優先順位が４０であるという意味らしい

test : ℕ
test = 3 --数字がintみたいな扱いを受けている。標準ライブラリのおかげ。

-- Fin n : 0 から n - 1 までの自然数を集めた n 元集合
--moduleと競合するかもしれないからzero → z suc → sとしておく
data Fin : ℕ → Set where
    z : {n : ℕ} → Fin (suc n)
    s : {n : ℕ} → Fin n → Fin (suc n)

--z s どちらも Fin (suc n)になるので、Fin 0はどうやっても存在できない。
test0 : Fin 1
test0 = z{0}

test1a : Fin 2
test1a = z

test1b : Fin 2
test1b = s z

test5 : Fin 5
test5 = s (s (s (s z)))
--sは一つまえのFinを取るようにしているから、sの連続みたいになる。
f : Fin 0 → Fin 1
f x = z 
--Vex A nで要素がAのnが長さの配列を作りたい。

data Vec (A : Set) : ℕ → Set where
    [] : Vec A 0
    _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
-- :: が　pythonでいう　,をあらわしている
-- [3,5,] ,の後は絶対[]が来る
test6 : Vec ℕ 2
test6 = 3 :: 5 :: []

--appendを作る。
append : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
-- append list1 list2 で　C-c.C-cでlist1を場合分け
append [] list2 = list2 
--append (x :: list1) list2 = x :: append list1 list2
--?0 : Vec A (suc n + m)　とあり、sucが入っているため、Vecの_::_の最後を使用する。
--_で書くと、Aがたを示されるので、
append (x :: list1) list2 = x :: append list1 list2 

test7 : Vec ℕ 4
test7 = append test6 test6

--指定リストに０があるかを見てみる。
contain0 : {n : ℕ} → Vec ℕ n → Bool
contain0 [] = false
--contain0 (x :: list1) = {!  !}でなぜxで場合分けをする？
--先頭の要素が０かどうかを判別することで、trueを返す。0出ない場合は残りの要素を再帰的に調べていく。
contain0 (zero :: list1) = true
contain0 (suc x :: list1) = contain0 list1

test8 : Bool
test8 = contain0 test6 --C-c,C-nでFalse

test9 : Bool
test9 = contain0 (3 :: 5 :: 0 :: 2 :: [])

list0 : Vec ℕ 3
list0 = 3 :: 2 :: 0 :: []

test10 : Bool
test10 = contain0 list0


--eq ２つの値が等しいか判別する
eq : ℕ → ℕ → Bool
eq zero zero = true
eq zero (suc b) = false
eq (suc a) zero = false
--再帰的に数を減らしていってどちらかが0になったタイミングで場合分けすることができる。
eq (suc a) (suc b) = eq a b


--任意の数iが含まれるかどうかを調べる
contain : {n : ℕ} → (Vec ℕ n) → ℕ → Bool
contain [] i = false
contain (x :: list1) i = if_then_else_ (eq x i) true (contain list1 i)

--sum : 自然数のリストを受け取り、要素の和を返す。
sum : {n : ℕ} → Vec ℕ n → ℕ
sum [] = zero
--これも先頭のものだけを摘まみだしていって、０になるまで再帰していく。
sum (x :: list1) = x + (sum list1)

