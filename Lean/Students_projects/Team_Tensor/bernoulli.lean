import data.nat.basic
import data.real.basic

lemma nat_mul_nonneg_real_nonneg (n : ℕ) (a : ℝ) : a ≥ 0 → ↑n * a ≥ 0 :=
begin
  intro p,
  have h : n ≥ 0 := by {exact nat.zero_le n},
  apply mul_nonneg,
  exact_mod_cast h,
  exact p,
end

lemma bernoulli_inequality (x : ℝ) (p : -1 ≤ x) (n : ℕ) : 1 + x * n ≤ (1 + x)^n :=
begin
  induction n with d hd,
  simp,

  have h1 : (1 + x) ^ nat.succ d = (1 + x) ^ d * (1 + x) :=
  begin
    rw nat.succ_eq_add_one,
    rw pow_add,
    ring,
  end,

  have h2 : (1 + x * d) * (1 + x) ≤ (1 + x) ^ d * (1 + x) :=
  begin
    apply mul_le_mul_of_nonneg_right,
    exact hd,
    have j := add_le_add_right p 1,
    simp at j,
    rw add_comm at j,
    exact j,
  end,

  have h3 : (1 + x * d) * (1 + x) = 1 + (d + 1) * x + d * x ^ 2 := by ring,

  have h4 : 1 + ↑(d + 1) * x ≤ 1 + ↑(d + 1) * x + d * x ^ 2 :=
  begin
    have j : 0 ≤ x ^ 2 := by {exact pow_two_nonneg x},
    have u : 0 ≤ ↑d * x ^ 2 := by {exact nat_mul_nonneg_real_nonneg d (x ^ 2) j},
    exact le_add_of_nonneg_right u,
  end,

  rw ← h1 at h2,
  rw h3 at h2,
  norm_cast at h2,
  have h5 : 1 + ↑(d + 1) * x ≤ (1 + x) ^ nat.succ d := by {exact le_trans h4 h2},
  rw ← nat.succ_eq_add_one at h5,
  rw mul_comm at h5,
  exact h5,
end