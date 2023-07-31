import algebra.field.basic
import data.list.big_operators.lemmas
import data.list.perm
import data.list.basic
import data.real.basic

def sum_of_squares {F: Type}[field F] : list F  →  F
| [] := 0
| (a :: L) := a * a + sum_of_squares L

def sum_of_squares_eq_zero (F: Type)[field F][decidable_eq F]: Prop :=
  ∀ L : list F, sum_of_squares L = 0 → (∀ x : F, x ∈ L → x = 0)

def sum_of_sq_ne_minus_one (F: Type)[field F][decidable_eq F] : Prop :=
  ∀ L : list F, sum_of_squares L ≠ -1

theorem list_sum_squares_permutation {F: Type}[field F]
(L1 L2 : list F) (h : L1 ~ L2) :
sum_of_squares L1 = sum_of_squares L2
:=
begin
  apply list.perm_induction_on h,
  {
    refl,
  },
  {
    intros x l1 l2 h1 h2,
    rw sum_of_squares,
    rw sum_of_squares,
    simp,
    rw h2,
  },
  {
    intros x y l1 l2 h1 h2,
    repeat{rw sum_of_squares}, -- repeat 4 times
    rw ← add_assoc,
    rw ← add_assoc,
    rw add_comm (y*y) (x*x),
    simp,
    rw h2,
  },
  {
    intros l1 l2 l3 h1 h2 h3 h4,
    rw h3,
    exact h4,
  },
end

theorem sum_of_sq_has_one_eq_minus_one {F: Type}[field F][decidable_eq F] (L : list F)(x : F)
(h1: (x : F) ∈ L ∧ x = 1 )
(h2: sum_of_squares L = 0) : 
(sum_of_squares(L.erase(x)) = -1) :=
begin
  have h3 : sum_of_squares(L) = sum_of_squares(x::L.erase(x)),
  begin
    apply list_sum_squares_permutation,
    have H : x ∈ L ∧ L.erase(x) ~ L.erase(x) :=
    begin
      split,
      exact h1.left,
      exact list.perm.refl (list.erase L x),
    end,
    have aux := list.cons_perm_iff_perm_erase.2 H,
    symmetry,
    exact aux,
  end,
  have someh : sum_of_squares(L) = x*x + sum_of_squares(L.erase(x)) := by 
  {
    rw ← sum_of_squares,
    apply h3,
  },
  rw h2 at someh,
  rw h1.2 at someh,
  ring_nf at someh,
  have h : (sum_of_squares(L.erase(1)) + 1 - 1 = -1),
  rw ← someh,
  ring,
  rw ← h,
  rw h1.right,
  ring,
end

theorem sum_of_sq_eq_minus_one {F: Type}[field F][decidable_eq F] (L : list F)
(h1 : sum_of_squares L = 0 )
(h2 : ∃ x : F, x ∈ L ∧ x ≠ 0) :
∃ L' : list F, sum_of_squares L' = -1
:=
begin
  rcases h2 with ⟨x, hx1, hx2⟩,
  have hs : sum_of_squares((L.map (λ v : F , v * x⁻¹)).erase(1)) = -1 :=
  begin
    apply sum_of_sq_has_one_eq_minus_one,
    split,
    have hl_contains_one: (1 : F) ∈ L.map (λ v : F , v * x⁻¹) := begin
      rw list.mem_map,
      use x,
      split, {exact hx1}, {exact mul_inv_cancel hx2,},
    end,
    exact hl_contains_one,
    refl,
    have hdiv: (
    ∀ c : F, 
    ∀ V : list F, 
    (sum_of_squares V) * c^2 = sum_of_squares (V.map (λ v : F , v * c))) := by {
      intros c V,
      induction V with a L2 ih,
      {
        simp,
        rw sum_of_squares,
        ring,
      },
      {
        rw sum_of_squares,
        rw list.map,
        rw sum_of_squares,
        rw ← ih,
        ring_nf,
      },
    },
    have hdiv2 := hdiv (x⁻¹) L,
    rw h1 at hdiv2,
    simp at hdiv2,
    rw hdiv2,
  end,
  use (L.map (λ v : F , v * x⁻¹)).erase(1),
  exact hs,
end

theorem theory_of_everything (F : Type) [field F] [decidable_eq F]:
sum_of_sq_ne_minus_one F ↔ sum_of_squares_eq_zero F :=
begin
  split,
  {
    contrapose,
    assume h,
    rw sum_of_squares_eq_zero at h,
    push_neg at h,
    cases h with L1 hL1,
    rw sum_of_sq_ne_minus_one,
    push_neg,
    have aux1 := hL1.1,
    have aux2 := hL1.2,
    cases aux2 with x hx,
    have hx1 := hx.1,
    have hx2 := hx.2,
    apply sum_of_sq_eq_minus_one L1,
    apply aux1,
    use x,
    apply hx,
  },
  {
    contrapose,
    assume h,
    rw sum_of_squares_eq_zero,
    rw sum_of_sq_ne_minus_one at h,
    push_neg at h,
    push_neg,
    cases h with L1 hL1,
    use (1::L1),
    split,
    {
      rw sum_of_squares,
      rw hL1,
      ring,
    },
    {
      use 1,
      split,
      {
        simp,
      },
      {
        simp,
      }
    }
  },
end
