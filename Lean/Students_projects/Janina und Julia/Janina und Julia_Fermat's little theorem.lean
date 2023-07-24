-- Fermat's little theorem
-- Janina Planeta, Julia Renner

import data.nat.choose.sum
import data.nat.prime

open_locale big_operators
open finset

theorem fermat (p : ℕ) (h: p ≠ 0) [hp : nat.prime p] (a : ℕ):
(a^p - a) % p = 0
:=
begin
    induction a with d hd,
    -- base clause
    -- rewrite 0^p to 0
    rw zero_pow',
    -- check the equation
    refl,
    -- use h: p ≠ 0
    apply h,
    -- induction step
    -- rewrite succ(d) to d+1
    rw nat.succ_eq_add_one,
    -- rewrite the binomial thereom
    rw add_pow, 
    -- simplify
    simp,
    -- since p is a prime number, there are no divisors of p in the denominator of the binomial coefficient.    Therefor, the binomial coefficient is modulo p equal to zero for 1 <= k <= p-1. 
    have aux: (∑ (x : ℕ) in range (p + 1), d ^ x * p.choose x = d^p + 1) := sorry,
    rw aux,
    simp,
    -- use the induction hypothesis
    rw hd,  
end