import data.set.basic
--import init.data.nat.lemmas
import tactic

lemma well_ordering_0n (n : ℕ) (S : set (finset.range (n + 1))) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l :=
  begin
    induction n with a ha,
    {
      use 0,
      {
        exact finset.self_mem_range_succ 0,
      },
      {
        dsimp at *,
        sorry,
      },
      {
        intro l,
        exact dec_trivial,
      },
    },
    simp at *,
    sorry,
  end

theorem well_ordering (S : set ℕ) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l :=
  begin
    have n : S := sorry,
    -- proof

    --exact well_ordering_0n _ _,
    sorry,
  end
