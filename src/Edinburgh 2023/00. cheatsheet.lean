import data.real.basic

open function (surjective)

-- Lean reference manual: https://leanprover.github.io/reference/
-- Mathlib documentation: https://leanprover-community.github.io/mathlib_docs/

------------------------------------------------------------------------------------------------------
--                                             Notation                                             --
------------------------------------------------------------------------------------------------------

-- Whenever you see a symbol you are not sure how to type, hover over it for a second and instructions
-- on how to type it will appear.

/-
  `λ`
    Introduce the arguments of a function.

    This is the proof term equivalent to the `intros` (or `rintros`) tactic.
-/
def add_one_example : ℕ → ℕ := λ n, n + 1

example (P Q : Prop) : P → (P → Q) → Q := λ hp hpq, hpq hp

/-
  `by`, `begin` and `end`
    These keywords are used to enter tactic mode wherever a proof term is expected. Use `by` when one 
    tactic is enough to prove the goal. Use a `begin` - `end` block for longer proofs.

    Inside a `begin` - `end` block, all tactics must end with a comma (`,`). You can group tactics
    using `{` and `}`.
-/
example (a : ℕ) : a = a := by refl

example (a b c : ℕ) (hab : a = b) (hbc : b = c) : a = c :=
begin
  rw hab,
  rw hbc,
end

/-
  `have`
    Introduces an intermediate goal that becomes an available assumption once proved.

  `suffices`
    Similar to `have`, but first must prove how assuming the intermediate goal is enough to prove the 
    final goal.

  Use `{` and `}` to focus on the first goal, if there are more than one goals.
  If you don't name your intermediate goal, it will automatically be named `this`.
-/
example {a b c : ℝ} (hab : a ≤ b) : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  have key : (c + b) - (c + a) = b - a,
  { ring, }, 
  rw key,
  rw sub_nonneg,
  exact hab,
end
-- Taken from Tutorials project

-- Note the difference between this example and the previous one.
example {a b c : ℝ} (hab : a ≤ b) : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  suffices key : (c + b) - (c + a) = b - a,
  { rw key,
    rw sub_nonneg,
    exact hab, },
  ring,
end

/-
  `calc`
    Write down a step by step chain of equalities or inequalities, justifying each step.
    
    Be careful about where you need `,` and where you don't! Also, you must write `...` on the left-
    hand side after the first step.

    The justification of each line after `:` expects a proof term, so make sure to write `by` if you 
    need to use a tactic.
-/
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b :=
begin
  calc b = 0 + b : by rw zero_add         -- no `,` after intermediate steps;
     ... ≤ a + b : add_le_add_right ha b, -- `,` at the end because this is the end of a tactic
end                                       -- where we see the entire `calc` block as a tactic.
-- Taken from Tutorials project

/-
  `_`
    The underscored caracter is used to create a 'hole'. This takes the place of a proof term. When
    a hole appears, Lean tries to find something that could fill it. In most cases, if it can't fill
    it, Lean will create a new goal for us, with the expected type of the whole.

    This can be useful when we are unsure what type Lean is expecting somewhere, or to defer proof
    obligations until later in the proof. 
-/
#check mul_le_mul_of_nonneg_left

example (a b c d : ℝ) (hbc : b ≤ c) (hca : a^2 * c ≤ d) : a^2 * b ≤ d :=
begin
  calc a^2 * b ≤ a^2 * c : mul_le_mul_of_nonneg_left hbc _ -- for this lemma to apply, we need `a^2 ≥ 0`
           ... ≤ d       : hca,
  -- Since Lean couldn't fill the whole two lines above, we need to do it ourselves now.
  exact sq_nonneg _, -- in this case, Lean is able to infer that this hole must have the value `a`
end

/-
  `{}` and `@`
    Definitions (of lemmas, functions, etc.) can have arguments given implicitly, when the context
    is enough to infer what they must be. Whenever you want Lean to guess an argument automatically
    you put it inside `{}` in your definition, instead of `()`.

    If you are calling a lemma or function that was defined with implicit arguments but you wish to
    provide those arguments explicitly, you can prepend its name with `@` to require all arguments
    explicitly. If this gives two many arguments, remember you can use `_` to ask Lean to guess
    individual ones.
-/
lemma nat_nonneg_example {a : ℕ} : 0 ≤ a := nat.zero_le a

example (a : ℕ) : 0 ≤ a := nat_nonneg_example -- we did not have to provide `a` as an argument

example (a : ℕ) : 0 ≤ a := @nat_nonneg_example a -- using `@` forces us to provide all arguments

------------------------------------------------------------------------------------------------------
--                                          Common tactics                                          --
------------------------------------------------------------------------------------------------------

-- Reference for core tactics: https://leanprover.github.io/reference/tactics.html

/-
  `rw`
    Rewrites the first instance of the left-hand side of an equality (`=`) or equivalence (`↔`) in the
    goal with the right-hand side. Use `←` to instead rewrite the right-hand side with the left-hand 
    side.

  see also: `rwa`, `nth_rewrite`, `nth_rewrite_lhs`, `nth_rewrite_rhs`.
-/
example (a b c : ℕ) (h : a = b) : a + c = b + c :=
begin 
  rw h,
end

example (a b : ℕ) (h : 0 = a) : a + b = b :=
begin
  rw ← h,
  rw zero_add,
end

-- Perform several rewrites in sequence using []
example (a b c d : ℕ) (hab : a = b) (hbc : b = c) : a + d = c + d :=
begin
  rw [hab, hbc], -- same as `rw hab, rw hbc,`
end

/-
  `simp`
    Attempts to simplify the goal using a large family of results. Pass the simplifier results in the
    current context using `[` and `]`. Use `simp only [...]` if you don't want the simplifier to use its own 
    results.
-/
example (a b : ℕ) (hab : a = b) : a + 0 = b :=
begin
  simp [hab], -- simp knows about `add_zero`
end

/-
  `unfold`:
    Expands a definition of your choice.
-/
def seq_limit : (ℕ → ℝ) → ℝ → Prop :=
λ (u : ℕ → ℝ) (l : ℝ), ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε)
-- Taken from Tutorials project

example (x : ℝ) : seq_limit (λ n, x) x :=
begin
  unfold seq_limit, -- this line helps the person writing the proof, Lean does not need it
  intros ε εpos,
  use 0,
  intros n nnonneg,
  simp [le_of_lt εpos],
end

/-
  `ring`
    Simplify algebraic expressions in a commutative ring

  `linarith`
    Deals with linear inequalities using all results in the context. You can pass it extra results 
    using `[` and `]`.
-/
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

example (a b : ℝ) : 2*a*b ≤ a^2 + b^2 :=
begin
  have : (a - b) * (a - b) ≥ 0 := mul_self_nonneg _,
  linarith,
end

/- 
  Applying tactics at a hypothesis
    Tactics such as `rw`, `simp` and `unfold`, whose aim is to change the way an expression looks, 
    can be applied to hypothesis in the current context, not just the goal. This is done with `at`. 
-/
example (a b : ℝ) (hab : a + 0 = b) (hb : b = 0) : a = 0 :=
begin
  rw add_zero at hab,
  rw [hab, hb],
end


------------------------------------------------------------------------------------------------------
--                                       Logical connectives                                        --
------------------------------------------------------------------------------------------------------

/- `→` and `∀`
    Because of how Lean's type theory works, these are just functions.

    TO PROVE:
      1. Introduce the assumptions using `intros` tactic.
      2. Produce an element of the goal type (e.g. using `exact`).

    TO USE:
      - Anywhere where a proof term is expected (e.g. after `exact`, `rw`, etc.), apply as a function 
        to suitable arguments.
      - If the conclusion of `h` matches the goal, use `apply h` to instead prove the antecedent. If
        `h` is a chained implication, several goals will be created.
      - Use `specialize` to pass arguments to a function in an assumption.
-/
lemma example_1 (P Q : Prop) (hq : Q) : P → Q :=
begin
  intros hp,
  exact hq,
end
-- As a proof term: `λ hp, hq`

-- In fact, we've been using `→` and `∀` implicitly all the time. Check out the type of the lemma we
-- just proved.
#check example_1

example (Q : Prop) (hq : Q) : ∀ P : Prop, P → Q :=
begin
  intros P hp,
  exact hq,
end
-- As a proof term: `λ P hp, hq`

example (P Q : Prop) (hp : P) : (P → Q) → Q :=
begin
  intros hpq,
  exact hpq hp,
end
-- As a proof term: `λ hpq, hpq hp`

example (a b c  : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  rw ← sub_nonneg,
  have key : b*c - a*c = (b - a)*c,
  { ring },
  rw key,
  apply mul_nonneg, -- `0 ≤ a → 0 ≤ b → 0 ≤ a * v`
  { rw sub_nonneg,
    exact hab },
  { exact hc },
end

example (u : ℕ → ℝ) (l : ℝ) (h : seq_limit u l) : ∃ (N : ℕ) (b : ℝ), ∀ n ≥ N, u n ≤ b :=
begin
  specialize h 1 one_pos, -- `specialize` helps unfold the meaning of definitions in the relevant case
  cases h with N hN,
  use [N, (l + 1)],
  intros n hn,
  specialize hN n hn,
  rw abs_le at hN,
  linarith, 
end

/- `∧`, `∃` and `↔`
    These are all inductive types with a single constructor (more on this later), so they have many
    similarities.

    TO PROVE:
      - Use `split` to separate into two goals (most useful for `∧` and `↔`).
      - Produce a proof term using the anonymous constructor `⟨⟩`.
      - Use the `use` tactic to produce the first thing needed (see examples).

    TO USE:
      - Use `cases` to separate into two hypotheses.
      - Introduce using `rintros` and an anonymous constructor `⟨⟩`.
      - For `∧` only: use `.left` and `.right` (or, `.1` and `.2`).
      - For `↔` only: use `.mp` and `.mpr` (or, `.1` and `.2`).
-/
example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intros hpq,
  cases hpq with hp hq,
  split,
  { exact hq, },
  { exact hp, },
end

-- More succinctly
example (P Q : Prop) : P ∧ Q → Q ∧ P := 
begin
  intro h,
  exact ⟨h.right, h.left⟩,
end

-- Also more succinctly
example (P Q : Prop) : P ∧ Q → Q ∧ P := 
begin
  rintros ⟨hp, hq⟩,
  exact ⟨hq, hp⟩,
end
-- As a proof term: `λ ⟨hp, hq⟩, ⟨hq, hp⟩`

-- Same proof, different theorem (this is the magic of the anonymous constructor)
example (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := 
begin
  rintros ⟨hp, hq⟩,
  exact ⟨hq, hp⟩,
end

example : (∃ x : ℝ, x^2 = 2) → ∃ x : ℝ, x ≥ 0 ∧ x^2 = 2 :=
begin
  rintros ⟨x, hx⟩,
  use [|x|, abs_nonneg _], -- `use` recursively provides the first arugment for `∃` and for `∧`
  rwa sq_abs,
end

/- 
  TIP: the anonymous constructor can take more than two arguments, in which case it associates to the 
  right. See also `rcases`.
-/
example (P Q R : Prop): (P ∧ Q ∧ R) → (Q ∧ R ∧ P) :=
begin
  rintros ⟨hp, hq, hr⟩,
  exact ⟨hq, hr, hp⟩,
end

/-
  `∨`
    This is an inductive type with two different constructors: left and right

    TO PROVE
      - Use `left` or `right` to change the goal for the left- or right-hand side of the disjunction.
      - If you insist on using a proof term, you can use `or.inl` and `or.inr`.

    TO USE
      - Use `cases` to split into each of the cases.
-/
example (P Q : Prop) (hp : P) : P ∨ Q :=
begin
  left,
  exact hp,
end
-- As a proof term: `or.inl hp`

example (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
  intros h,
  cases h with hp hq,
  { right, exact hp, },
  { left, exact hq, },
end

/-
  `¬`
    Negation in Lean is defined as `¬ P = P → false`. Hence, we can use the same tactics as for `→`.
    In addition to this, there are a number of useful tactics that help us deal with negation:

    `push_neg`: pushes a negation past all the quantifiers in the goal.
      (It doesn't unfold definitions on its own, so if you want it to push past quantifiers implicit 
      in a definition you should first use `unfold`.)

    `contrapose`: transforms a goal of the form `P → Q` to `¬ Q → ¬ P`.

    `contrapose!`: same as `contrapose`, but automatically does `push_neg` afterwards.

    `by_contradiction`: sets up a proof by contradiction. If the goal is `P`, it adds `¬ P` as a 
      hypothesis and changes the goal to `false`.

    `by_contra'`: same as `by_contradiction` but applies `push_neg` to the new hypothesis `¬ P`.

    `by_cases`: given a proposition `P`, it splits the proof into two cases, one assuming `P` and one 
      assuming `¬ P`.

    `exfalso`: changes the goal to `false` (this is valid because anything follows from `false`). 
      Use this when there is a contradiction in your currect assumptions.
-/
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example : ¬ even_fun (λ x, 2*x) :=
begin
  unfold even_fun, -- Here unfolding is important because push_neg won't do it.
  push_neg,
  use 42,
  linarith,
end
-- Taken from Tutorials project

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  contrapose,
  exact h,
end

example (P : Prop) : P ∨ ¬ P :=
begin
  by_contradiction h,
  push_neg at h,
  exact h.left h.right,
end

example (P : Prop) : P ∨ ¬ P :=
begin
  by_cases P,
  { left, exact h },
  { right, exact h },
end

example (n : ℤ) (h_even : even n) (h_not_even : ¬ even n) : 0 = 1 :=
begin
  exfalso,
  exact h_not_even h_even,
end

/-
  BONUS: Axiom of choice 
    Sometimes we will need to use the axiom of choice. This can be done with the `choose` tactic.
    It needs an assumption that is (roughly) of the form `∀ a : A, ∃ b : B, P a b`, where
    `P : A → B → Prop` is some predicate. Given this, it produces a function `f : A → B` and a proof 
    that `∀ a : A, P a (f a)`.
-/
-- Here we use the axiom of choice to show that every surjective function has a section.
example (A B : Type) (f : A → B) (hf : surjective f) : ∃ g : B → A, f ∘ g = id :=
begin
  unfold surjective at hf,
  choose g hg using hf,
  use g,
  apply funext, -- see `funext` below
  intro x,
  exact hg x,
end

#check funext -- see also `ext` and `ext1` tactics