import data.set.basic
import tactic

lemma well_ordering_0n (n : ℕ) (S : set ℕ) (hS1 : ∀ m ∈ S, m ≤ n) (hS2 : ∃ a : ℕ, a ∈ S) : (∃ k : ℕ, (k ∈ S) ∧ (∀ l ∈ S, k ≤ l)) := 
  begin
    induction n with n hn,
    {
      cases hS2 with a ha,
      have ha2 := hS1 a ha,
      simp at ha2,
      use a,
      split,
      {
        exact ha,
      },
      {
        rw ha2,
        simp,
      },
    },
    {
      have hS3 : S = {n.succ} ∨ S ≠ {n.succ} := by finish,
      cases hS3 with S1 S2,
      {
        use n.succ,
        rw S1,
        simp,
      },
      {
        cases hS2 with a ha,
        have h := hS1 a ha,
        apply hn,
        intros m hm,
        have hp := hS1 m hm,
        have hS4 : n.succ ∈ S ∨ ¬ n.succ ∈ S := by finish,
        cases hS4,
        swap,  
        {
          --this is obvious because n.succ ∉ S, so m ≤ n, but we don't know how to do it in Lean
          sorry,
        },
        {
          --that goal doesn't make so much sense, because n.succ ∈ S, so m > n for m = n.succ, that's why we thought the following could help
          have han : a < n := sorry, -- but we still couldn't figure it out.
          sorry,
        },
      },
    }

  end

theorem well_ordering (S : set ℕ) (hS : ∃ n : ℕ, n ∈ S) : (∃ k : ℕ, (k ∈ S) ∧ (∀ l ∈ S, k ≤ l)) := 
begin
  cases hS with n hn,
  apply well_ordering_0n _ _ _,
  use n, exact hn,
  exact n,
  intros m hm,
  --we have the same problem as above, the goal itself doesn't make sense, we'd first need to reduce the set to having n as supremum
  sorry,

end
