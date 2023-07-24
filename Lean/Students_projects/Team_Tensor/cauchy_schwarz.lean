import analysis.inner_product_space.basic

namespace cauchy_schwarz

variables {A B : Type*} [is_R_or_C A] [normed_add_comm_group B] [module A B] [d : inner_product_space.core A B]
local notation `norm_sq` := @inner_product_space.core.norm_sq A B _ _ _ _

include d

lemma zero_le_norm_sq (e : B) : 0 ≤ norm_sq e :=
begin
  rw inner_product_space.core.norm_sq,
  exact inner_product_space.core.inner_self_nonneg,
end

lemma help_eq (a b : B) : norm_sq (d.inner a b • a - d.inner a a • b) = 
    norm_sq a * (norm_sq a * norm_sq b - norm (d.inner a b) ^ 2) :=
begin
  rw ← @is_R_or_C.of_real_inj A,
  rw inner_product_space.core.coe_norm_sq_eq_inner_self,
  rw inner_product_space.core.inner_sub_sub_self,
  repeat {rw inner_product_space.core.inner_smul_right},
  repeat {rw inner_product_space.core.inner_smul_left},
  repeat {rw ← mul_assoc},
  rw is_R_or_C.mul_conj,
  rw mul_right_comm,
  rw mul_assoc,
  rw is_R_or_C.mul_conj,
  rw mul_comm,
  rw sub_self,
  rw zero_sub,
  rw add_comm,
  rw ← sub_eq_add_neg,
  rw inner_product_space.core.conj_symm,
  rw mul_right_comm,
  rw mul_comm,
  rw mul_comm (inner a b) (inner a a),
  rw mul_assoc,
  rw ← mul_sub,
  rw ← inner_product_space.core.coe_norm_sq_eq_inner_self a,
  rw ← inner_product_space.core.coe_norm_sq_eq_inner_self b,
  rw mul_comm (inner a b) (inner b a),
  rw ← inner_product_space.core.conj_symm,
  rw is_R_or_C.conj_mul,
  rw is_R_or_C.norm_sq_eq_def' (inner a b),
  push_cast,
end


lemma cauchy_schwarz_inequality (x y : B) :
norm (d.inner x y) ≤ norm x * norm y :=
begin
  by_cases C : x = 0,
  rw C,
  simp,
  exact inner_product_space.core.inner_zero_left y,
  have h1 : 0 ≤ norm_sq (d.inner x y • x - d.inner x x • y) / norm_sq x :=
  begin
    have j : 0 ≤ norm_sq (d.inner x y • x - d.inner x x • y) := by {exact zero_le_norm_sq (d.inner x y • x - d.inner x x • y)},
    have i : 0 ≤ norm_sq x := by {exact zero_le_norm_sq x},
    exact div_nonneg j i,
  end,
  have h2 : norm_sq (d.inner x y • x - d.inner x x • y) / norm_sq x = norm_sq x * norm_sq y - norm (inner x y) ^ 2 :=
  begin
    rw help_eq,
    rw mul_div_right_comm,
    rw div_self,
    simp,
    intro r,
    rw inner_product_space.core.norm_sq_eq_zero at r,
    exact C r,
  end,
  rw h2 at h1,
  apply le_of_pow_le_pow 2,
  exact mul_nonneg (norm_nonneg x) (norm_nonneg y),
  simp,
  rw mul_pow,
  have h3 : 0 + norm (d.inner x y) ^ 2 ≤ norm_sq x * norm_sq y - norm (inner x y) ^ 2 + norm (inner x y) ^ 2 := by {apply add_le_add_right h1 (norm (inner x y) ^ 2)},
  simp at h3,
  repeat {rw inner_product_space.core.norm_sq at h3},
  repeat {rw inner_product_space.core.inner_self_eq_norm_mul_norm at h3},
  rw pow_two (norm x),
  rw pow_two (norm y),
  push_cast,
  -- exact_mod_cast h3,
  sorry,
end

end cauchy_schwarz