import data.real.basic

/- Tactics and proofs basics -/

-- First tactic: `refl`. Also a chance to see `by`, and term mode.

example (a : ℝ) : a = a :=
by {refl}
-- begin
--   refl,
-- end

-- The rewrite tactic.

#check mul_comm
#check mul_assoc

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  -- rw mul_assoc b a c,
  rw mul_assoc b a c,
end

-- `rw`in a hypothesis; rw in reverse direction; `exact`

example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
begin
  rw hyp' at hyp,
  rw mul_comm d a at hyp,
  rw ← two_mul (a*d) at hyp,
  rw ← mul_assoc 2 a d at hyp,
  exact hyp,
end

-- `calc` notation

example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
begin
  calc c = d*a + b : by { exact hyp } --rw also works
  ... = d*a + a*d  : by { rw hyp' }
  ... = a*d + a*d  : by { rw mul_comm d a}
  ... = 2*(a*d)    : by { rw two_mul }
  ... = 2*a*d      : by { rw mul_assoc },
end

-- `have` notation 

example {a b c : ℝ} (hab : a ≤ b) : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  have key : (c + b) - (c + a) = b - a,
  { ring, }, 
  rw key,
  rw sub_nonneg,
  exact hab,
end

/- Implication -/

-- Tactic `apply` for using an implication.

#check mul_nonneg

example (a b c  : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  rw ← sub_nonneg,
  have key : b*c - a*c = (b - a)*c,
  { ring },
  rw key,
  apply mul_nonneg,
  { rw sub_nonneg,
    exact hab },
  { exact hc },
end

-- Tactic `intros` for proving an implication.

#check le_add_of_nonneg_left

example (a b : ℝ): 0 ≤ a → b ≤ a + b :=
begin
  intros ha,
  exact le_add_of_nonneg_left ha,
end

/- Conjunction -/

-- Tactic `cases` to use a conjunction.

example {a b : ℝ} : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b :=
begin
  intros hyp,
  cases hyp with ha hb,
  exact add_nonneg ha hb,
end

-- Tactic `split` to prove a conjunction.

example {a b : ℝ} (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  intros ha hb,
  apply H,
  split,
  exact ha,
  exact hb,
end

-- To learn: various compression tactics. Recursive versions of these (needs anonymous constructor notation). Syntax to directly access constructors. How to talk about iff.

/- Universal quantifier -/

-- Use one with `exact`; prove one with `intros`.

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) :=
begin
  intros x₁ x₂ h,
  have step₁ :  f x₁ ≤ f x₂,
    -- apply hf, exact h,
    exact hf x₁ x₂ h,
    apply hg, exact step₁,
    -- exact hg (f x₁) (f x₂) step₁,
end

-- To learn: how to compress this, how to write it as a proof term.

/- Disjunction -/

-- Tactics `left` and `right` to prove one.
example (P Q : Prop) : P → P ∨ Q :=
begin
  intro h,
  left,
  exact h,
end

-- Tactic `cases` to use one. 
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
  intro h,
  cases h with hP hQ,
  right,
  exact hP,
  left,
  exact hQ,
end

/- Existence quantifier -/

-- Tactic `cases` to use one.

example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 :=
begin
  -- cases h with k₀ hk₀,  
  rcases h with ⟨k₀, hk₀⟩,
  rw hk₀,
  exact nat.succ_pos k₀,
end

-- Tactic `use` to prove one.

example : ∃ n : ℕ, 8 = 2*n :=
begin
  use 4,
  refl,
end