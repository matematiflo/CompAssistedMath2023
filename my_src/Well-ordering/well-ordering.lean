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

example (n : ℕ) (S : set ℕ) (hS1 : ∀ m ∈ S, m ≤ n) (hS2 : ∃ a : ℕ, a ∈ S) : 
∃ k : ℕ, (k ∈ S) ∧ (∀ l ∈ S, k ≤ l) :=
begin
  revert S,
  induction n with n ih,
  {
    intros S hS1 hS2,
    cases hS2 with a ha,
    have ha2 := hS1 a ha,
    simp at ha2,
    use a,
    split,
    exact ha,
    rw ha2,
    simp,
  },
  {
    intros S hS1 hS2,
    have h : (∀ a : ℕ, a ∈ S → a = n + 1) ∨ ¬ (∀ a : ℕ, a ∈ S → a = n + 1) := by tauto,
    cases h with h1 h2,
    {
      use n + 1,
      cases hS2 with a ha1,
      have ha2 : a = n + 1 := by {exact h1 a ha1},
      split,
      {
        rw set.mem_def,
        rw set.mem_def at ha1,
        -- exact eq.subst ha2 ha1,
        rw ha2 at ha1,
        exact ha1,
      },
      {
        intro l,
        intro hl,
        have aux : l = (n+1) := by {exact h1 l hl},
        rw aux,
      },
    },
    {
      push_neg at h2,
      cases hS2 with m hm,
      rcases h2 with ⟨a, ha1, ha2⟩,
      have aux : a ≤ n+1 := hS1 a ha1,
      let T := { x ∈ S | x ≤ n },
      have aux2 : a ≤ n := sorry,
      have hT : (∃ t : ℕ, t ∈ T),
      {
        use a,
        split,
        exact ha1,
        exact aux2,
      },
      have hT1 : ∀ t ∈ T, t ≤ n := sorry,
      have hT2 := ih T hT1 hT,
      rcases hT2 with ⟨r, hr1, hr2⟩,
      use r,
      split,
      {
        sorry,
      },
      {
        sorry,
      },
    },
  },
end