import data.nat.pow
import tactic
universes u

--------- Definitions

inductive N : Type 
  | z : N
  | s : N → N

open N

inductive Tree (A : Type u) : Type u
  | nil : Tree
  | cons : A → Tree → Tree → Tree 

open Tree

def is_bigger : N → N → bool
  | z z := false
  | z (s a) := false
  | (s a) z := true
  | (s a) (s b) := is_bigger a b

example : is_bigger (s (s (s z))) (s (s (s (s z)))) = false :=
begin
reflexivity,
end

def plus : N → N → N
  | z a := a
  | (s b) a := s (plus b a)

def mult : N → N → N
   | z a := z
   | (s b) a := plus a (mult b a)

def power : N → N → N
   | a z := (s z)
   | a (s b) := mult a (power a b)

def bigger : N → N → N
   | a b := if (is_bigger a b) then a else b

--------- Induction on natural numbers

#check @N.rec
#check @Tree.rec

def naive_prop_1 : (is_bigger 
                      z 
                      (plus (s z) z)
                      ) = false := 
begin
reflexivity,
end

def naive_prop_2 : ∀ (n : N), (is_bigger n (plus (s z) n)) = false 
                    → (is_bigger (s n) (plus (s z) (s n))) = false := 
begin
intros n a1,
simp at *,
unfold plus at *,
unfold is_bigger,
assumption,
end

def naive_prop : ∀ (n : N), (is_bigger n (plus (s z) n)) = false :=
begin
apply N.rec,
apply naive_prop_1,
apply naive_prop_2,
end

--------- Tactics on the tree

def count_nodes {A : Type u} : (Tree A) → ℕ 
  | nil := 0
  | (cons c a b) := (count_nodes a) + (count_nodes b)

def height {A : Type u} : (Tree A) → ℕ
  | nil := 0
  | (cons c a b) := if (height a) ≥ (height b) then (height a) + 1 else (height b) + 1

lemma pow_two_is_double : ∀ (a : ℕ), 2^(a + 1) = (2^a) + (2^a) := by intro;induction a;repeat {ring_nf}.

def upper_bound_of_nodes : ∀ {A : Type u} (t : Tree A),
                (pow 2 (height t)) - 1 >= (count_nodes t) :=
begin
intros,
induction t with t t' t'',
repeat {unfold height count_nodes, simp},
split_ifs,
all_goals {rw pow_two_is_double},
  have a : 2 ^ (height t') ≥ 2 ^ (height t''),
  apply nat.pow_le_pow_of_le_right,
  repeat {omega},
  
  have a : 2 ^ (height t') < 2 ^ (height t''),
  apply nat.pow_lt_pow_of_lt_right,
  repeat {omega},
end
