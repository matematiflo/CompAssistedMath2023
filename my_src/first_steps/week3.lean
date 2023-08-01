import tactic.linarith
import data.real.basic
import analysis.special_functions.trigonometric.arctan_deriv

attribute [pp_nodot] nat.succ

/- ## **More logic**

The `exfalso` (quod libet) tactic. The LEM. The `by_cases` tactic. 

And there's more in my notes...

> **Exercise:** Formalise and prove the statements `( P ∨ ¬P ) ∧ ( ¬¬P ) → P` and `P ∨ ¬P`.
-/

example { P: Prop } ( H : P ∨ ¬P ) ( f : ¬¬P ) : P := 
begin
  cases H with p np,
  exact p,
  exfalso,
  exact f np,
end

example { P: Prop } : P ∨ ¬P :=
begin
  by_cases P,
  left,
  exact h,
  right,
  exact h,
end

example {P : Prop} : false → P :=
begin
  intro h,
  cases h -- cases works on an inductive type, by going through the possible constructors
end


example ( A B : Prop ) : A ∧ ¬A → B
:=
begin
intro h,
cases h with a not_A,
exfalso,
-- apply not_A,
-- exact a,
exact not_A a,
end

example ( A B : Prop ) : A ∧ ¬A → B
:=
begin
intro h,
cases h with a na,
have h1 : ¬ A ∨ B,
by { left, exact na },
rw ← or_false B,
cases h1 with nna b,
right,
exact nna a,
left,
exact b,
end

example ( B : Prop ) : false → B
:=
begin
contrapose,
intro h,
exact not_false,
end

example ( B : Prop ) : B ↔ (B ∨ false)
:=
begin
split,
intro b,
left,
exact b,
intro h,
cases h with b f,
exact b,
have h : false → B,
by { contrapose, intro h, exact not_false },
exact h f,
end

example ( A B : Prop ) : A ∧ ¬A → B
:=
begin
intro h,
cases h with a na,
rw ← or_false B, 
right,
exact na a,
end

-- modus ponens
example ( P Q : Prop ) : P ∧ ( P → Q ) → Q
:=
begin
intro h,
cases h with hp hpq,
exact hpq hp,
end

-- syllogisme disjonctif? revoir aussi le modus tollens...
example ( P Q : Prop ) : P ∧ ( ¬ P ∨ Q ) → Q
:=
begin
intro h,
cases h,
cases h_right,
rw ← or_false Q, 
right,
exact h_right h_left,
exact h_right,
end

example ( P Q : Prop ) : ( P → Q ) ↔ ( ¬P ∨ Q )
:=
begin
split,
intro hpq,
by_cases P,
right,
exact hpq h,
left,
exact h,
intro nP_or_Q,
intro p,
rw ← or_false Q, 
cases nP_or_Q,
right,
exact nP_or_Q p,
left,
exact nP_or_Q,
end

-- I bet this is what exfalso does?
-- The point is that the contrapose tactic is an equivalence, of which one implication uses the LEM (see NNG Prop and Adv. Prop Worlds)
example ( A B : Prop) : ¬A → ( A → B)
:=
begin
intro H,
intro a,
-- have h : false → B,
-- by { contrapose, intro h, exact not_false },
-- exact h (H a),
exfalso,
exact H a,
end

-- without the LEM, one can only show that 
example ( A B : Prop) : ¬A → ( A → B ∨ false)
:=
begin
intro H,
intro a,
right,
exact H a,
end

example ( A B : Prop) : ¬A → ( A → B)
:=
begin
intro H,
intro a,
have h : B ∨ false,
by { right, exact H a },
cases h,
exact h,
have h1 : false → B,
by { contrapose, intro h, exact not_false },
exact h1 h,
end

example ( P : Prop ) : ¬¬P ↔ P
:=
begin
split,
intro nnp,
by_cases P,
exact h,
-- have F : false,
-- exact nnp h,
exfalso,
exact nnp h,
-- intro nnp,
-- by_cases P,
-- exact h,
-- have h1 : false → P,
-- by { contrapose, intro hp, exact not_false },
-- apply h1,
-- apply nnp,
-- exact h,
intro p,
intro h,
exact h p,
end

example ( P : Prop ) : (¬¬P → P) ↔ ( P ∨ ¬P )
:=
begin
split,
intro h,
by_cases h2 : ¬P, --bof...
right,
exact h2,
left,
exact h h2,
intro lem,
intro nnp,
cases lem with lem1 lem2,
exact lem1,
exfalso,
exact nnp lem2,
end

example ( P : Prop ) : ¬¬P → P
:=
begin
intro h,
by_cases h1 : P,
exact h1,
exfalso,
apply h,
exact h1,
end

example ( P : Prop ) : ¬¬P ↔ P
:=
begin
split,
intro h,
by_cases h1 : P,
exact h1,
exfalso,
apply h,
exact h1,
intro p,
intro np,
exact np p,
end

example ( A B : Prop ) : ¬A → ( A →B ) 
:=
begin
intro h,
intro a,
exfalso,
exact h a,
end

example ( P Q : Prop ) : ( ( ¬Q → ¬P ) → ( P → Q ) )
:=
begin
intro h,
intro p,
by_cases q : Q,
exact q,
have h1 : ¬P, by {exact h q},
have h3 : P → Q, by {intro p1, exfalso, exact h1 p1},
exact h3 p,
end

example ( P : Prop ) :  P ∨ false → P
:=
begin
intro h,
cases h with p F,
exact p,
exfalso,
exact F,
end











/- The next bit should go into the part about inductive types, because of the use of `∃`. -/

-- #check @eq.symm
-- #check @eq.trans

#check @eq.subst

namespace injectivity

variables {X Y Z : Type}

-- good exercise: define comp

def comp (f : X → Y) (g : Y → Z) : X → Z  := λ (x : X), g (f x)

def id {X : Type} : X → X := λ x, x

#check @comp 
#check @id

def is_injective (f : X → Y) : Prop := ∀ x1 x2, f x1 = f x2 → x1 = x2

def has_left_inv (f : X → Y) : Prop := ∃ g : Y → X, ∀ x : X, g (f x) = x  

#check @is_injective

def has_left_inv_implies_is_injective (f : X → Y) : has_left_inv f → is_injective f :=
begin
  unfold has_left_inv,
  intro h,
  cases h with g h,
  unfold is_injective,
  intros x1 x2 hf,
  rw ← h x1,
  rw hf,
  exact h x2,
end

def left_inv_implies_is_injective (f :X →Y) (g : Y → X) : (∀ x : X, g (f x) = x) → is_injective f :=
begin
  intro left_inv,
  -- unfold is_injective,
  intros x1 x2 h,
  have h1 : g (f x1) = g (f x2) := eq.subst h (eq.refl (g (f x1))),
  have h2 : g (f x1) = x2 := eq.subst (left_inv x2) h1,
  exact eq.subst (left_inv x1) h2,
end

def left_inv_implies_is_injective_bis (f :X →Y) (g : Y → X) : (∀ x : X, g (f x) = x) → is_injective f :=
begin
  intro left_inv,
  -- unfold is_injective,
  assume x1 x2 h,
  rw [← left_inv x1, ← left_inv x2], -- various rewrites at once
  rw h,
end

#print left_inv_implies_is_injective
#print left_inv_implies_is_injective_bis

end injectivity

def test { X : Type } [h : add_semigroup X] ( x y z : X ) : x + (y +z) = (x +y) +z :=
begin
  symmetry,
  apply add_assoc,
end

#check @test

def test { X : add_semigroup } { x y z : X } : x + (y +z) = (x +y) +z :=
begin
  symmetry,
  apply add_assoc,
end

open nat

def strong_induction_pple {P : ℕ → Prop} (p0 : P 0) (ih : (∀ (k : ℕ), (∀ j ≤ k,  P j) → P (k + 1))) : ∀ (n : ℕ), P n :=
begin
  have stronger_conclusion : (∀ (n : ℕ), ∀ j ≤ n, P j) := 
  begin
    intro n,
    induction n with k hk,
    {
      intro j,
      intro h,
      have hj : j = 0 := by linarith,
      -- begin
      --   -- apply le_antisymm,
      --   -- exact h,
      --   -- exact nat.zero_le j,
      --   linarith,
      -- end,
      rw hj,
      exact p0,
    },
    {
      intro j,
      intro hj,
      rw le_iff_lt_or_eq at hj,
      cases hj,
      {
        have hj1 := le_of_lt_succ hj,
        exact hk j hj1,
      },      
      rw hj,
      have h2 := ih k,
      apply h2,
      exact hk,
    },
  end,
  intro n,
  -- apply st_ccl n,
  -- -- exact le_refl n,
  -- linarith,
  have H1 := stronger_conclusion n,
  have H2 : n ≤ n := le_refl n,
  exact H1 n H2,
end


example {P : Prop} : false → P :=
begin
  intro h,
  cases h -- cases works on an inductive type, by going through the possible constructors
end

def is_injective {S T : Type} (f : S → T) : Prop := ∀ s s' : S, f s = f s' → s = s'

def has_left_inverse {S T : Type} (f : S → T) : Prop := ∃ (g : T → S), g ∘ f = id 

lemma is_injective_of_has_left_inverse {S T : Type} (f : S → T) : has_left_inverse f → is_injective f := 
begin
  intro hf,
  rw [has_left_inverse] at hf,
  rw [is_injective],
  intros s s' hss',
  cases hf with g hg,
  have h : (g ∘ f) s = (g ∘ f) s' := by {simp, rw hss'},
  rw [hg] at h,
  exact h,
end

lemma is_injective_of_has_left_inverse2 {S T : Type} (f : S → T) (hf : has_left_inverse f) : is_injective f := 
begin
  rw [has_left_inverse] at hf,
  rw [is_injective],
  intros s s' hss',
  cases hf with g hg,
  have h : (g ∘ f) s = (g ∘ f) s' := by {simp, rw hss'},
  rw [hg] at h,
  exact h,
end

#print is_injective_of_has_left_inverse
#print is_injective_of_has_left_inverse2

def my_f : ℤ → ℤ := λ n, n + 1

theorem my_f_is_injective {S : Type} : is_injective my_f := 
begin
  have h : has_left_inverse my_f := 
  begin
    rw [has_left_inverse],
    let my_g : ℤ → ℤ := λ n, n - 1,
    use my_g,
    ext n,
    simp, --should be changed
    rw [my_f],
    simp,
    have hgn : my_g (n + 1) = (n + 1) - 1 := by {refl},
    rw [hgn],
    simp, -- or ring
  --   have h1 : ∀ k : ℤ, my_g (my_f k) = k :=
  --   begin
  --     intro k,
  --     sorry,
  --   end,
  -- exact h1 n,
  end,
  -- apply is_injective_of_has_left_inverse my_f,
  -- apply is_injective_of_has_left_inverse _,
  apply is_injective_of_has_left_inverse,
  exact h,
end

def calc_test (a b c : ℕ) (H1 : a = b + 1) (H2 : b = c) : a = c + 1 :=
begin
  calc a = b + 1 : H1
  ...    = c + 1 : _,
  { rw H2 }
end

#print calc_test

example : (0 < 3) ∧ (1 < 5) := 
begin
split,
{ exact zero_lt_one_add 2,
},
{ apply lt_add_of_pos_left 1,
  exact zero_lt_one_add 3,
}

end


lemma neg_eq_neg_one_pos (x : ℝ) : -x = (-1) * x := begin
    exact neg_eq_neg_one_mul x,
end

lemma squares_are_nonneg2 (x : ℝ) : (x^2 ≥ 0) :=
begin
  exact sq_nonneg x,
end

lemma squares_are_nonneg {F : Type} [linear_ordered_field F] : (∀ x : F, x^2 ≥ 0) := 
begin
  intro x,
  -- have aux := le_total 0 x,
  -- cases aux with aux1 aux2,
  cases le_total 0 x with aux1 aux2,
  { have hx : x * x = x^2:= by ring,
    -- rw ← hx,
    apply eq.subst hx,
    apply mul_nonneg,
    exact aux1,
    exact aux1,
  },
  { have hx : x^2 = (-x)*(-x) := by ring,
    rw hx,
    rw [← neg_nonneg] at aux2,
    exact mul_nonneg aux2 aux2,
  },
end

theorem neg_eq_mul_min {F : Type} [linear_ordered_field F] (x : F) : (x = -1 * -x) :=
begin
    simp,
end

#check (1 + 2 : ℝ)
#eval (1 + 2 : ℝ)

#eval (3/4 + 1/3 : ℚ)