
/- # Solutions to Exercises from Week 2

## Exercise 3 of [week2.md](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/week2.md)

> Formalise the equivalence `( P → Q ) ↔ ( ¬Q → ¬P )` and use the `split` tactic and the functions `MT` and `contra` defined above to write a proof of it.

Below are the pre-requisites for this exercise. The solution appears right afterwards. -/

import tactic.ring
import tactic.zify
import tactic.qify
import tactic.polyrith

def MT { P Q : Prop } ( hPQ : P → Q ) ( nq : ¬Q ) : ¬P :=
begin
  -- show P → false,
  intro p,
  apply nq,
  apply hPQ,
  exact p,
end

def contra { P Q : Prop } ( H : ¬Q →  ¬P ) : P → Q :=
begin
  intro p,
  by_contradiction,
  exact (H h) p,
end

def equiv_with_contraposition { P Q : Prop } : ( P → Q ) ↔ ( ¬Q → ¬P ) :=
begin
  split,
  { exact MT,
  },
  { intro H,
    exact contra H,
  },
end

/- ## Exercise 1 of [forall.lean](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/Practice_folder/forall.md)

A proof that squares are positive in `ℤ` (using `mathlib` but not using the function `sq_nonneg`). -/

example : ∀ (n : ℤ), n^2 ≥ 0 :=
begin
  intro n,
  by_cases n ≥ 0,
  { rw sq,
    apply mul_nonneg h,
    exact h,
  },
  { simp at h,
    rw ← neg_sq,
    rw sq,
    apply mul_nonneg,
    repeat
      { rw right.nonneg_neg_iff,
        apply le_of_lt,
        exact h
      },
  },
end

/- ## Exercise 2 of [forall.lean](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/Practice_folder/forall.md) -/

def S : ℕ → ℚ
| 0 :=  0
| (n+1) := (n + 1) + S n

def induction_pple {P : ℕ → Prop} (p0 : P 0) (ih : ∀ (k : ℕ), P k → P (k + 1)) : ∀ (n : ℕ), P n :=
begin
  intro n,
  induction n with k hk,
  exact p0,
  exact ih k hk,
end

def Sum_of_nat : ∀ n : ℕ, S n = n * (n + 1) / 2 :=
begin
  apply induction_pple,
  { simp,
    refl,
  },
  { intro k,
    intro p,
    rw S,
    rw p,
    simp,
    ring,
  },
end

def T : ℕ → ℕ 
| 0 :=  0
| (n+1) := (n + 1) + T n

def Sum_of_nat_again : ∀ n : ℕ, (T n : ℚ) = n * (n + 1) / 2 :=
begin
  apply induction_pple,
  { simp,
    refl,
  },
  { intro k,
    intro p,
    rw T,
    push_cast, -- used to push the `↑` down on every possible term
    rw p,
    ring,
  },
end

/-
---
-/