-- import algebra.big_operators.basic
import data.nat.interval
import data.nat.basic
import number_theory.cyclotomic.basic

-- open_locale big_operators
open finset
open nat

def test (n : nat) : Type := fin n 

#check fin 3

class my_ring := mk_my_ring ::
(dom : Type)
(sum : dom → dom → dom)
(prod : dom → dom → dom)
(zero : dom)
(one : dom)
-- + axioms of a ring

-- def sum_of_squares {A : my_ring} (n : nat) : (nat → A.dom ) → A.dom 
-- --:= sorry
-- | λ f, A.zero
-- | λ f, A.sum (sum_of_squares n f) (A.prod (f succ n) (f succ n))

def sum_of_squares {A : my_ring} (n: nat) (f : range n → A.dom) : A.dom 
:= sorry
-- | if n = 0 then A.zero else A.sum (sum_of_squares (n-1) f) (A.prod f(n) f(n)) 


-- we want a recursive definition here:
-- if n = 0, then ∀ f, (sum_of_squares 0 f) = A.zero
-- if n = succ k, then ∀ f, (sum_of_squares (succ k) f) = A.sum (sum_of_squares k f) (A.prod (f k) (f k))

def sub2 : ℕ → ℕ
| 0     := 0
| 1     := 0
| (a+2) := a

#eval sub2 9

#check @sum_of_squares
#check sum_of_squares 42 

def semireal (A : my_ring) : Prop 
:= ∀ n : nat, ∀ f : ℕ → A.dom, A.sum (sum_of_squares n f) A.one ≠ A.zero

def real_alg (A : my_ring) : Prop 
:= ∀ (n : nat), ∀ (f: ℕ → A.dom), (sum_of_squares n f = A.zero) → (∀ i : range n, f i = A.zero)

def real_implies_semireal {A : my_ring} : (real_alg A → semireal A) 
:= sorry

-- Real numbers as an instance of the class my_ring
instance R_temp : my_ring 
:= sorry


def R_temp_is_real_alg : real_alg  R_temp
:= sorry --use that 1 > 0 in real numbers...

def R_is_semireal : semireal R_temp 
:= real_implies_semireal R_temp_is_real_alg 

meta def foo : ℕ → ℕ
| n := if n = 100 then 0 else foo (n + 1) + 1

#check foo 3
#eval foo 99

def numbers : ℕ → list ℕ
| 0 := []
| (n+1) := n :: numbers n

#eval numbers 3
#eval numbers 4

-- meta def finite_sum_of_squares {A : my_ring} (f : nat → A.dom) : nat → A.dom 
-- | n := if n = 0 then A.zero else A.sum (finite_sum_of_squares n) (A.prod (f n) (f n))

-- #check finite_sum_of_squares 42

-- def sum_of_sqres {A : my_ring} (f : nat → A.dom) : nat → A.dom
-- := λ k, finite_sum_of_squares f k

def numbers_again : ℕ → list ℕ
| 0 := []
| (n+1) := (numbers_again n).append([n])

#check numbers_again 3
#eval numbers_again 3
#eval numbers_again 4
#check list ℕ 

-- def list_of_n_terms_in_a_ring {A : my_ring} {n : nat} : list ℕ → A.dom 
-- := 
-- begin
-- have l : list ℕ := numbers_again n,

-- end


-- def sum_terms_in_list {A : my_ring} : (list ℕ → A.dom) → A.dom :=
-- begin
-- intro f,
-- -- have n := 

-- end

-- def n_elts_in_A {A : my_ring} (n : nat) : list ℕ → A.dom := 
-- begin
-- have l := numbers_again n,
-- sorry
-- end

#check numbers_again 3
-- are terms of type list ℕ inductive?

def sum_sq {A : my_ring} (f : nat → A.dom) : nat → A.dom
| 0 := A.zero
| (n+1) := A.sum (sum_sq n) (A.prod (f n) (f n))

#check @sum_sq
#check sum_sq
#check sum_sq 2

def semireal_again (A : my_ring) : Prop 
:= ∀ f : ℕ → A.dom, ∀ n : nat, A.sum (sum_sq f n) A.one ≠ A.zero

def real_again (A : my_ring) : Prop 
:= ∀ (n : nat), ∀ (f: ℕ → A.dom), (sum_sq f n = A.zero) → (∀ i : range n, f i = A.zero)

def real_again_implies_semireal_again {A : my_ring} {one_not_zero : (A.one ≠ A.zero)} : (real_again A → semireal_again A) 
:= 
begin
intro h,
unfold real_again at h,
unfold semireal_again,
intro f,
intro n,
intro P,
have g : ℕ → A.dom := λ i, f i, --à modifier
have h1 := h (n+1) g,
have P1 : sum_sq g (n + 1)= my_ring.zero := sorry, --should come from P and correct def of g
have h2 := h1 P1,
have Q : g (n+1) = A.one := sorry, --should come from correct def of g
have h3 : g(n+1) = A.zero := sorry, -- g(n+1) is just h2 n ...
have h4 : A.zero = A.one := 
  begin
  rw ← Q,
  rw ← h3,
  end,
  apply one_not_zero,
  symmetry,
  exact h4,
end

inductive my_fin (n : nat)
| cons (i : fin n) : my_fin 

#check my_fin
#check my_fin 3
#check @my_fin.cons 3

inductive family (n : nat)
| cons (f : my_fin n) : family

#check family 
#check family 3

def sum_n_sq {A : my_ring} (n : nat) : my_fin n  → A.dom
| my_fin := sorry

def list_in_ring {A : my_ring} : list A.dom := sorry

#check @list_in_ring

def sum_list_squares {A : my_ring} : list A.dom → A.dom
  | [] := A.zero
  | (a :: l) := A.sum ( A.prod a a) (sum_list_squares l)

#check @sum_list_squares
#check sum_list_squares

def l {A : my_ring }: list A.dom := sorry
#check sum_list_squares l

def semireal_yet_again (A : my_ring) : Prop 
:= ∀ f : list A.dom, A.sum (sum_list_squares f) A.one ≠ A.zero

def real_yet_again (A : my_ring) : Prop 
:= ∀ (f: list A.dom), (sum_list_squares f = A.zero) → (∀ i < f.length, list.nth f i = A.zero)

def real_yet_again_implies_semireal_yet_again {A : my_ring} {one_not_zero : (A.one ≠ A.zero)} : (real_again A → semireal_again A) 
:= sorry

def L : list nat := (numbers_again 3)

#eval L
#eval L.length

-- ∀ i < L.length, list.nth L i

#eval list.nth L 2
#check 1 < L.length 

/-- `sum f n` is `f(0)+f(1)+...+f(n-1)` -/
def my_sum {M : Type} [add_monoid M] (f : ℕ → M) : ℕ → M
| 0 := 0
| (n + 1) := (f n) + (my_sum n)

def idN : ℕ → ℕ := λ n, n

#check my_sum
#check @my_sum
#check @my_sum ℕ
#check @my_sum ℕ idN 42

def sum_squares {F : Type} [semiring F] : list F →  F
| [] := 0
| (a :: L) := a * a + sum_squares L

#eval sum_squares ([1/2,1] : list ℚ)
