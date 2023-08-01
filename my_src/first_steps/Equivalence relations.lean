import data.int.basic
import data.setoid.basic
import data.nat.basic 
import data.real.basic

-- import analysis.inner_product_space.basic
-- import analysis.inner_product_space.calculus

def reflexive_rel {X : Type} (r : X → X → Prop) := ∀ x, r x x

def is_even ( n : ℤ ) : Prop := ∃ k : ℤ, n = 2 * k

#check is_even
#check is_even 2
-- #check is_even 3

#print is_even 

example : is_even 2 := by {unfold is_even, use 1, rw mul_one}
-- lemma two_is_even : is_even 2 := by {use 1, simp}

def diff_is_even (n m : ℤ) : Prop := is_even (n - m)
#check diff_is_even 2 (-1)

example : reflexive_rel diff_is_even :=
begin
  unfold reflexive_rel,
  unfold diff_is_even,
  unfold is_even,
  intro x,
  use 0,
  ring,
end

#print diff_is_even 

example : reflexive diff_is_even :=
begin
  unfold reflexive,
  unfold diff_is_even,
  unfold is_even,
  sorry,
end

example : equivalence diff_is_even :=
begin
  unfold equivalence,
  split,
  sorry,
end

-- infix ` ≡ `:50 := diff_is_even

-- def r ( a b : ℤ ) : Prop := a ≡ b

--Next we just rename diff_is_even to r
def r ( a b : ℤ ) : Prop := diff_is_even a b

def my_reflexive {X : Type} (E : X → X → Prop) : Prop := ∀ x, E x x

#check @my_reflexive
#check my_reflexive r
#print my_reflexive

-- variables (X : Type)
-- def my_reflexive (E : X → X → Prop) : Prop := ∀ x, E x x

-- #check my_reflexive
-- #print my_reflexive

#check @reflexive
#check reflexive r
#check @equivalence
#check @mk_equivalence

-- We use the 'equivalence' function from mathlib. It uses the functions 'reflexive', 'symmetric' and 'transitive', also in mathlib.

/- 
equivalence is a function which, to a relation r associates a proof of the fact that r is reflexive, symmetric and transitive. So a term of type equivalence r is a proof of the fact that r is an equivalence relation.
 -/

-- #print equivalence
-- #print mk_equivalence

theorem r_is_equiv_rel : equivalence r := 
  begin
    unfold equivalence,
    -- split,
    repeat { any_goals {split} },
    {
      unfold reflexive r,
      intro x,
      unfold diff_is_even, 
      unfold is_even,
      use 0,
      rw mul_zero,
      rw sub_self,
    },
    {
      unfold symmetric,
      intros x y,
      unfold r,
      unfold diff_is_even,
      unfold is_even,
      intro h,
      cases h with k h_k,
      use -k,
      simp,
      apply eq_neg_of_eq_neg,
      rw ← mul_neg_one,
      simp,
      symmetry,
      exact h_k,
    },
    {
      unfold transitive r diff_is_even is_even,
      intros x y z,
      intro h_xy,
      cases h_xy with k h_xy,
      intro h_yz,
      cases h_yz with l h_yz,
      use k+l,
      have h : x-z= 2*k + 2*l :=
        begin
          have h : (x-y) + (y-z) = x-z := by simp,
          rw ← h,
          rw h_xy,
          rw h_yz,
        end,
      rw h,
      rw mul_add,
    },
  end

/- 
Let us prove the theorem differently, using separate lemmas to prove that r is reflexive, symmetric and transitive. First we define a term reflexive_r of type reflexive r. The latter is a term of type Prop, so reflexive_r is a proof of the proposition reflexive r, i.e. a proof of the fact that r is reflexive (by definition of the term reflexive r in mathlib).
 -/

lemma reflexive_r : reflexive r := 
  begin
    unfold reflexive,
    unfold r,
    unfold diff_is_even,
    unfold is_even,
    intro x,
    simp,
    use 0,
    simp,
  end

-- #print reflexive_r 
-- #print r_is_equiv_rel 

lemma symmetric_r : symmetric r := 
  begin
    unfold symmetric,
    intros x y,
    unfold r,
    unfold diff_is_even,
    unfold is_even,
    intro h,
    cases h with k h_k,
    use -k,
    simp,
    apply eq_neg_of_eq_neg,
    rw ← mul_neg_one,
    simp,
    symmetry,
    exact h_k,
  end

lemma transitive_r : transitive r := 
  begin
    unfold transitive r diff_is_even is_even,
    intros x y z,
    intro h_xy,
    cases h_xy with k h_xy,
    intro h_yz,
    cases h_yz with l h_yz,
    use k+l,
    have h : x-z= 2*k + 2*l :=
      begin
        have h : (x-y) + (y-z) = x-z := by simp,
        rw ← h,
        rw h_xy,
        rw h_yz,
      end,
    rw h,
    rw mul_add,
  end

theorem r_is_equiv_rel_alt : equivalence r := 
mk_equivalence r reflexive_r symmetric_r transitive_r 

-- Or, going back to the definition of the mk_equivalence function:

theorem r_is_equiv_rel_yet_another_proof : equivalence r :=
⟨reflexive_r, symmetric_r, transitive_r⟩

-- Note: the syntax ⟨reflexive_r, symmetric_r, transitive_r⟩ does not seem to work in tactic mode, at least not directly. 

theorem r_is_equiv_rel_alt_tactic_mode : equivalence r := 
begin
--unfold equivalence,
exact mk_equivalence r reflexive_r symmetric_r transitive_r,
end

variables {X Y : Type}


class my_group {A : Type} := 
(op : A → A → A)   
(sym : A→A)
(e : A)
(e_neutral_left : ∀ x:A, op e x = x)
(sym_op : ∀ x:A, op (sym x) x = e)
(op_assoc : ∀ x y z:A, op (op x y) z = op x (op y z))

#check my_group

class my_group2 (A : Type) := 
(op : A → A → A)   
(sym : A→A)
(e : A)
(e_neutral_left : ∀ x:A, op e x = x)
(sym_op : ∀ x:A, op (sym x) x = e)
(op_assoc : ∀ x y z:A, op (op x y) z = op x (op y z))

#check my_group2

class my_group3 := 
(A : Type)
(op : A → A → A)   
(sym : A→A)
(e : A)
(e_neutral_left : ∀ x:A, op e x = x)
(sym_op : ∀ x:A, op (sym x) x = e)
(op_assoc : ∀ x y z:A, op (op x y) z = op x (op y z))

class my_group4 := mk_my_group4 ::
(A : Type)
(op : A → A → A)   
(sym : A→A)
(e : A)
(e_neutral_left : ∀ x:A, op e x = x)
(sym_op : ∀ x:A, op (sym x) x = e)
(op_assoc : ∀ x y z:A, op (op x y) z = op x (op y z))

#check my_group3
#check my_group4

class vector_space := (E : Type)
#check vector_space

def dim (V : vector_space) : nat := sorry
#check dim

-- constants n : nat
-- #check n

-- def has_dim_n (E : vector_space) : Prop := (dim E = n)
-- #check has_dim_n

def has_dim (E : vector_space) (n : nat) : Prop := (dim E = n)
#check has_dim

infix ` has_dimension `:50 := has_dim

instance Rn : vector_space := sorry
#check Rn

-- #check has_dim_n Rn

-- theorem Rn_has_dim_n : has_dim_n Rn := 
--   begin
--   unfold has_dim_n,
--   sorry,
--   end
-- #check Rn_has_dim_n
 
constant m : nat

 theorem dim_Rn_equals_n : -- Rn has_dimension m :=
 has_dim Rn m :=
  begin
  unfold has_dim,
  sorry,
  end

#check dim _ = m

def vector_space.has_dim (E : vector_space) (n : nat) := (dim E = n)
#check Rn.has_dim

#check Rn.has_dim m

theorem dim_Rn_is_n : Rn.has_dim m :=
  begin
  show dim Rn = m, -- the 'unfold' tactic does not work...
  sorry,
  end

example : Rn.has_dim m :=
  begin
  show dim Rn = m,
  sorry,
  end

def associative_law {S : Type} (op : S → S → S) := 
∀ s1 s2 s3, op (op s1 s2) s3 = op s1 (op s2 s3)

#check @associative_law

#check associative_law nat.add

-- What is the difference between a class and a structure?
-- structure semiGroup := mk_SemiGroup ::

class Semigroup := mk_Semigroup ::
(dom : Type)
(binop : dom -> dom -> dom)
(binopA : associative_law binop)
--(binopA : ∀ s1 s2 s3, binop (binop s1 s2) s3 = binop s1 (binop s2 s3)) 

-- This second def of a class is not quoite the same: 
-- here we are considering the all possible structures of semigroup on
-- a **given** domain...
-- class Semigroup {dom : Type} := mk_Semigroup ::
-- (binop : dom -> dom -> dom)
-- (binopA : associative_law binop)

#check Semigroup
-- With the second def, we would get that Semigroup is a term of type Type, not Type 1...

structure my_semigroup := mk_my_semigroup ::
(dom : Type)
(binop : dom -> dom -> dom)
(binopA : associative_law binop)

#check my_semigroup

#print Semigroup
#print my_semigroup

#check nat.add_assoc

-- def nat_semigroup : Semigroup := 

instance nat_semigroup : Semigroup :=
Semigroup.mk_Semigroup nat nat.add nat.add_assoc

-- with the second definition of the class semiGroupSemigroup, 
-- we would type
-- mk_Semigroup nat.add nat.add_assoc

#check nat_semigroup
#print nat_semigroup

#check nat_semigroup.dom

-- One cannot instantiate structures in Lean?
-- instance nat_my_semigroup : my_semigroup :=
-- my_semigroup.mk_my_semigroup nat nat.add nat.add_assoc

def nat_my_semigroup : my_semigroup :=
my_semigroup.mk_my_semigroup nat nat.add nat.add_assoc

#check nat_my_semigroup
#print nat_my_semigroup

-- instance int_semigroup : semiGroup := 
-- semiGroup.mk_SemiGroup int int.add int.add_assoc

lemma neutral_is_unique (M : Semigroup) (e1 e2 : M.dom) (h : ∀ s, (M.binop e1 s = s) ∧ (M.binop s e2 = s)) : e1 = e2 := 
  begin
  have h1 : (M.binop e1 e2 = e2) :=
    begin
    specialize h e2,
    exact h.1,
    end,
  specialize h e1,
  cases h,
  rw ← h_right,
  symmetry,
  rw h1,
  end

-- variables {M : Semigroup}

lemma neutral_is_unique2 {M : Semigroup} (e1 e2 : M.dom) (h : ∀ s, (M.binop e1 s = s) ∧ (M.binop s e2 = s)) : e1 = e2 := 
  begin
   
  have h1 : (M.binop e1 e2 = e2) :=
    begin
    specialize h e2,
    exact h.1,
    end,
  specialize h e1,
  cases h,
  rw ← h_right,
  symmetry,
  rw h1,
  end

lemma neutral_is_unique3 (e1 e2 : Semigroup.dom) (h : ∀ s, (Semigroup.binop e1 s = s) ∧ (Semigroup.binop s e2 = s)) : e1 = e2 := 
  begin
  have h1 : (Semigroup.binop e1 e2 = e2) :=
    begin
    specialize h e2,
    exact h.1,
    end,
  specialize h e1,
  cases h,
  rw ← h_right,
  symmetry,
  rw h1,
  end

#check neutral_is_unique
#check @neutral_is_unique

#check neutral_is_unique2
#check @neutral_is_unique2

#check neutral_is_unique3
#check @neutral_is_unique3

#print neutral_is_unique
#print neutral_is_unique2
#print neutral_is_unique3

lemma my_neutral_is_unique (M : my_semigroup) (e1 e2 : M.dom) (h : ∀ s, (M.binop e1 s = s) ∧ (M.binop s e2 = s)) : e1 = e2 := 
  begin
  have h1 : (M.binop e1 e2 = e2) :=
    begin
    specialize h e2,
    exact h.1,
    end,
  specialize h e1,
  cases h,
  rw ← h_right,
  symmetry,
  rw h1,
  end

lemma my_neutral_is_unique2 {M : my_semigroup} (e1 e2 : M.dom) (h : ∀ s, (M.binop e1 s = s) ∧ (M.binop s e2 = s)) : e1 = e2 := 
  begin
  have h1 : (M.binop e1 e2 = e2) :=
    begin
    specialize h e2,
    exact h.1,
    end,
  specialize h e1,
  cases h,
  rw ← h_right,
  symmetry,
  rw h1,
  end

-- The third version does not work
-- lemma my_neutral_is_unique3 (e1 e2 : my_semigroup.dom) (h : ∀ s, (my_semigroup.binop e1 s = s) ∧ (my_semigroup.binop s e2 = s)) : e1 = e2 := 
--   begin
--   have h1 : (my_semigroup.binop e1 e2 = e2) :=
--     begin
--     specialize h e2,
--     exact h.1,
--     end,
--   specialize h e1,
--   cases h,
--   rw ← h_right,
--   symmetry,
--   rw h1,
--   end


-- In the first one, we instantiated a class; 
-- in the second one, we defined a structure (?)
-- The difference is that things like Semigroup.dom 
-- is replaced by M.dom (which is easier to read, I think)

#check neutral_is_unique
#check my_neutral_is_unique

-- Here, the second #check is a bit annoying
#check neutral_is_unique2
#check my_neutral_is_unique2

#check @neutral_is_unique2
#check @my_neutral_is_unique2

noncomputable theorem nat_semigroup2 : Semigroup := 
Semigroup.mk_Semigroup nat nat.add nat.add_assoc
  
#check nat_semigroup
#check nat_semigroup2
#check nat_semigroup.dom
#check nat_semigroup.binop
#check nat_semigroup.binopA

#check nat_my_semigroup.dom


#print nat_semigroup

#print nat_semigroup2
-- #print nat_semigroup.dom -- why does this not return ℕ?

-- class Monoid extends semiGroup := 
-- mk_monoid :: (e : dom) (neutral : ∀ s, binop e s = s)

structure Monoid extends Semigroup := 
mk_monoid :: (e : dom) (neutral : ∀ s, binop e s = s)

namespace playground
-- BEGIN
structure prod (A : Type) (B : Type) := 
-- mk ::
(pr1 : A) (pr2 : B)

def N2 := prod ℕ ℕ 

def  π : N2 → ℕ := λ n, n.1 + n.2

def x : N2 := prod.mk 1 2

#eval x.1
#eval x.2
#eval π x

#check prod
#check prod.mk
-- END
end playground

def my_example {P Q : Type} {p : P} {h : P → Q} : Q 
:= h p

-- begin
-- exact h p,
-- end

#check @my_example
#print my_example

def my_example2 {P Q R : Type} {p : P} {hpq : P → Q} {hqr : Q → R} : R
:= hqr ( hpq p )

-- :=
-- begin
-- exact hqr (hpq p),
-- end

-- :=
-- begin
-- apply hqr,
-- apply hpq,
-- exact p,
-- end

#print my_example2

#check fin 


def two_is_even : Prop := ∃ k, 2 = 2 * k

#check two_is_even
#print two_is_even

def proof_that_two_is_even : two_is_even := 
begin
-- The typical Lean proof would be:
use 1,
refl,
-- Another possibility is:
-- existsi 1,
-- exact eq.refl (2*1),
end

#check proof_that_two_is_even
#print proof_that_two_is_even

#check id (eq.refl (2*1))

def another_proof_that_two_is_even : two_is_even := 
exists.intro 1 (eq.refl (2 * 1))

#print another_proof_that_two_is_even

#check proof_that_two_is_even = another_proof_that_two_is_even

def sanity_check : proof_that_two_is_even = another_proof_that_two_is_even := 
begin
refl,
end

#print sanity_check

def is_even (n : ℕ) : Prop := ∃ k, 2 * k = n

#check is_even
#check is_even 2
#print is_even

def div_by_four ( n : ℕ ) : Prop := ∃ k, 4*k = n

theorem div_by_four_implies_is_even (n : ℕ) (h : div_by_four n) : is_even n
:=
  begin
  cases h with l hl,
  -- unfold is_even,
  use 2*l,
  -- rw ← mul_assoc,
  rw ← mul_assoc,
  exact hl,
  end

example : 2*2=4 := by refl

#check div_by_four_implies_is_even
#check div_by_four_implies_is_even 4
#check div_by_four_implies_is_even 5

#print div_by_four_implies_is_even

#check 2*2
#eval 2*2

theorem mul_of_four_is_even : ∀ l : ℕ, is_even (4 * l) :=
  -- div_by_four_implies_is_even 16 sixteen_div_by_four
  begin
  intro l,
  -- unfold is_even,
  apply div_by_four_implies_is_even,
  -- unfold div_by_four,
  use l,
  end

#check mul_of_four_is_even 
#check mul_of_four_is_even 3
#print mul_of_four_is_even 

#eval string.append "Hello, " "world!"

#check string.append 
#eval string.append "Hello, " "world!"

#check "Hello, ".append "world!"
#eval "Hello, ".append "world!"
  
def my_sentence : string := "Hello, world!"
#check my_sentence
#print my_sentence

theorem I_check : ("Hello, ".append "world!" = my_sentence) := by {refl}

#check I_check
#print I_check

def test : "Hello, ".append "world!" = "Hello, world!" := by {refl}

#check test
#print test

def I_complete (x : string) : string := (x.append "world!")

#check I_complete
#check I_complete "x"

theorem I_check_again : (I_complete "Hello, " = my_sentence) := eq.refl "Hello, world!"

theorem we_check : ("Hello, ".append "world!" = "Hello, world!") := eq.refl my_sentence

example : "Hello, ".append "world!" = my_sentence := by {refl}

#check "Hello, ".append "world!" = "Hello, world!"
#check "Hello, ".append "world!" = "Hello, world"

#check 1 ≠ 2

class R3 := mk_R3 ::
( x : ℝ )
( y : ℝ )
( z : ℝ )

def v : R3 := ⟨ 1, 2, -3 ⟩ 

#check R3
#check v
#print v

example (n : ℕ) (h : n >0) : (↑n > 0) :=
begin
  -- push_cast,
  -- exact h,
  exact_mod_cast h,
end

example (n : ℕ) (h : ↑n >0) : (n > 0) :=
begin
  exact h,
  -- push_cast at h,
  -- exact h,
end

lemma nat_nonneg_real_mul_nonneg (n : ℕ) (a : ℝ) : a ≥ 0 → ↑n * a ≥ 0 :=
begin
  intro p,
  apply mul_nonneg,
  apply_mod_cast nat.zero_le,
  exact p,
end

