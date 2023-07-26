
/- # Solution of Assignment #1 -/

import tactic.linarith

attribute [pp_nodot] nat.succ

open nat

/- ## The assignment 

The assignment was to complete three empty spots in the proof of the "strong induction principle with stronger conclusion" given below. -/

def strong_induction_pple_with_stronger_ccl {P : ℕ → Prop} (p0 : P 0) (ih : (∀ (k : ℕ), (∀ j ≤ k,  P j) → P (k + 1))) : (∀ (n : ℕ), ∀ j ≤ n, P j) :=
begin
  intro n,
  induction n with k hk,
  { intro j,
    intro h,
    have hj : j = 0 :=
    begin
      -- have hj1 : 0 ≤ j := zero_le j,
      -- exact le_antisymm h hj1,
      exact le_antisymm h (zero_le j),
    end,
    rw hj,
    exact p0, -- sol 1 line 1
  },
  { intro j,
    intro hj,
    rw le_iff_lt_or_eq at hj,
    cases hj with hj1 hj2,
    { apply hk j, -- sol2 line 1
      apply le_of_lt_succ, -- sol 2 line 2
      exact hj1, -- sol 2 line 3
    },
    { rw hj2,
      apply ih, -- sol 3 line 1
      exact hk, -- sol 3 line 2
    },
  },
end

/- And from this we can indeed deduce a proof of the strong induction principle, or more accurately of a `strong_induction_pple_short_proof` function, that we can use to perform stronmg induction (see example below). -/

def strong_induction_pple_short_proof {P : ℕ → Prop} (p0 : P 0) (ih : (∀ (k : ℕ), (∀ j ≤ k,  P j) → P (k + 1))) : ∀ (n : ℕ), P n :=
begin
  intro n,
  apply strong_induction_pple_with_stronger_ccl _ _ n, -- note the use of `_` for implicit arguments here (we use them because we know *something* goes there)
  exact le_refl n,
  exact p0,
  exact ih,
end

/- --- -/
