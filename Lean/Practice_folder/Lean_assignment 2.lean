
/- # Strong induction principle -/

import tactic.linarith

attribute [pp_nodot] nat.succ

open nat

/- On the model of the function `induction_pple` that we created in [forall.lean](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/Practice_folder/forall.lean), the goal of this assignment is to define a function `strong_induction_pple` that encapsulates the so-called [*strong* (or *complete*) induction principle](https://en.wikipedia.org/wiki/Mathematical_induction#Complete_(strong)_induction).

As we shall see, this strong induction principle is proved by ordinary induction, so it is in fact not a stronger result. -/

/- ## Preliminaries

Let us first recall the function `induction_pple`. In this formalisation, the term `P : ℕ → Prop` is a function from `ℕ` to `Prop`, meaning that we have, for all `n : ℕ`, a mathematical statement `P n`, depending on `n`. -/

def induction_pple {P : ℕ → Prop} (p0 : P 0) (ih : ∀ (k : ℕ), P k → P (k + 1)) : ∀ (n : ℕ), P n :=
begin
  intro n,
  induction n with k hk,
  exact p0,
  exact ih k hk,
end

/- For the strong induction, the function will look like this. -/

def strong_induction_pple {P : ℕ → Prop} (p0 : P 0) (ih : (∀ (k : ℕ), (∀ j ≤ k,  P j) → P (k + 1))) : ∀ (n : ℕ), P n := sorry

/- It means a function that takes the following two arguments:

1. A proof `p0` of the proposition `P 0`,
2. A proof of the fact that, for all `k : ℕ`, if `P j` is proved for all `j ≤ k` then `P (k + 1)` is proved,

and returns a proof of all the `P n`. This means, for all `n : ℕ`, a proof of `P n`.

The proof/defintion of this is by induction, but in fact we prove a stronger result, namely that, for all `n : ℕ`, we have a proof of the statement `∀ j ≤ n, P j`, which is indeed stronger than just `P n`. -/

def strong_induction_pple_with_stronger_conclusion {P : ℕ → Prop} (p0 : P 0) (ih : (∀ (k : ℕ), (∀ j ≤ k,  P j) → P (k + 1))) : (∀ (n : ℕ), ∀ j ≤ n, P j) := sorry

/- If we have this function, then the proof of `strong_induction_pple` goes as follows. -/

def strong_induction_pple_short_proof {P : ℕ → Prop} (p0 : P 0) (ih : (∀ (k : ℕ), (∀ j ≤ k,  P j) → P (k + 1))) : ∀ (n : ℕ), P n :=
begin
  intro n,
  apply strong_induction_pple_with_stronger_conclusion _ _ n, -- note the use of `_` for implicit arguments here
  exact le_refl n,
  exact p0,
  exact ih,
end

/- So, what is left to prove is the `strong_induction_pple_with_stronger_conclusion` and this is the assignement. -/

/- ## The assignment

In the code below, I start the process for you, and you are asked to fill in the `sorry`'s. Beware that I changed the name of the function to `strong_induction_pple_with_stronger_ccl`, to avoid conflicts with the one defined earlier in this file. -/

def strong_induction_pple_with_stronger_ccl {P : ℕ → Prop} (p0 : P 0) (ih : (∀ (k : ℕ), (∀ j ≤ k,  P j) → P (k + 1))) : (∀ (n : ℕ), ∀ j ≤ n, P j) :=
begin
  intro n,
  induction n with k hk,
  {
    intro j,
    intro h,
    have hj : j = 0 := by linarith, -- see the solution file for a more detailed proof
    rw hj,
    sorry,
  },
  { 
    intro j,
    intro hj,
    rw le_iff_lt_or_eq at hj,
    cases hj with hj1 hj2,
    {
      sorry,
    },
    {
      rw hj2,
      sorry,
    },
  },
end

/- --- -/
