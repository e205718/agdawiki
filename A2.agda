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