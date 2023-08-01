import tactic
import data.nat.prime
import data.nat.basic
open finset
open multiset

--- Die Definition hab ich irgendwo geklaut
def is_prime (p : ℕ) := 2 ≤ p ∧ ∀ d ∣ p, d = 1 ∨ d = p


lemma exists_prime_factor {n : nat} (h : 2 ≤ n)(g: ¬ is_prime n) :
  ∃ p q : nat, p*q=n ∧ 2≤p ∧ 2≤q ∧ p<n ∧ q<n:=
begin
    sorry,
end

lemma prime_is_fact (p : ℕ)(h₁: prime p) : ∃ (s : multiset ℕ), s.prod=p ∧ ∀ x ∈ s, is_prime x :=
begin
    sorry,
end

lemma prod_solution (a b: multiset ℕ)(p=a.prod)(q=b.prod):p*q=(a+b).prod:=
begin
    sorry,
end

theorem prime_fact' (n : ℕ)(h₁ : n ≥ 2) : ∃ (s : multiset ℕ), s.prod=n ∧ ∀ x ∈ s, prime x :=
begin
    sorry,
end





