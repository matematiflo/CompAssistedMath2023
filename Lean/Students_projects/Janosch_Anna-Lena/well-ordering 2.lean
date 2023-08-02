import data.set.basic
import tactic

lemma well_ordering_0n (n : ℕ) (S : set (fin (n + 1))) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l :=
  begin
    induction n with a ha,
    {
      use 0,
      {
        sorry,
      },
      {
        intro l,
        apply le_of_eq (subsingleton.elim _ _),       -- by library_search
        exact set.subsingleton_coe_of_subsingleton,   -- by library_search
        -- exact subsingleton.le ⟨0, id sorry⟩ l,      -- by library_search (alternative)
      },
    },
    simp at *,
    have hS : S = {a.succ + 1} ∨ S ≠ {a.succ + 1} := sorry,
    cases hS with hSn1 hSany,
    {
      finish,
    },
    {
      -- have T : S ∩ fin(a + 1) := sorry,
      sorry,
    },
    /-
    simp at *,
    fconstructor, -- brute force Lean tactics
    {
      fconstructor,
      {
        exact a,
      },
      {
        rw nat.succ_add,
        apply nat.lt_succ_of_le,
        apply nat.le_succ,
      },
    },
    {

    },
    -/
  end

theorem well_ordering (S : set ℕ) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l :=
  begin
    have n : S := sorry,
    -- proof

    -- apply well_ordering_0n _ _,
    sorry,
  end
