import number_theory.cyclotomic.basic
import data.list.big_operators.lemmas
import data.list.perm

def sum_of_squares {F : Type} [semiring F] : list F →  F
| [] := 0
| (a :: L) := a * a + sum_of_squares L

#eval sum_of_squares ([1/2,1] : list ℚ)

theorem sum_of_sq_eq_minus_one {F : Type} [field F] (L : list F)
(h1 : sum_of_squares L = 0 )
(h2 : ∃ x : F, x ∈ L ∧ x ≠ 0) :
∃ L' : list F, sum_of_squares L' = -1
:=
begin
  -- cases h2 with x hx,
  -- cases hx with hx1 hx2,
  rcases h2 with ⟨x, hx1, hx2⟩, -- this is a recursive version of `cases`, hence the name `rcases`
  let L1 := L.map (λ v : F , v / x),
  have hs : sum_of_squares L1 = -1 := 
  begin
    sorry,
  end,
  use L1, -- this is what you do when your goal starts with a `∃`, you tell Lean using which witness you will prove the goal
  exact hs,
end

example {F : Type} [field F] (L : list F) : (1 : F) ∈ (1 :: L) 
:= 
begin
  exact list.mem_cons_self 1 L,
end

example {F : Type} [field F] (L : list F) (x : F) (hx : x ∈ L ∧ x ≠ 0) :
(1 : F) ∈ (list.map (λ v : F , v / x) L) := 
begin
-- rw list.mem_map,
apply list.mem_map.2,
-- apply list.mem_map.mpr,
-- refine list.mem_map.mpr _,
-- 
-- apply Exists.intro x, -- here, one does not need to specify the type because `x : F` is alreaady declared
use x,
split,
exact hx.1,
exact div_self hx.2,
end

def test : ∃ x : ℝ, x > 0 := 
begin
apply Exists.intro (1 : ℝ), -- here apply Exists.intro 1 does *not* work, Lean wants to know the type
-- use 1,
exact zero_lt_one,
end

def test2 : ∃ (x : ℝ), x > 0 :=
Exists.intro 1 zero_lt_one

#print test
#print test2

theorem list_sum_permutation {F : Type} [add_comm_monoid F]
(L1 L2 : list F) : 
(L1 ~ L2) → list.sum L1 = list.sum L2 
:=
begin
  intro h,
  apply list.perm_induction_on h,
  {
    refl,
  },
  { 
    intros x l1 l2 h1 h2,
    simp,
    rw h2,
  },
  {
    intros x y l1 l2 h1 h2,
    simp,
    rw ← add_assoc,
    rw ← add_assoc,
    rw add_comm x y,
    rw h2,
  },
  { 
    intros l1 l2 l3 h1 h2 h3 h4,
    rw h3,
    exact h4,
  },
end

theorem my_test.perm_induction_on {α : Type}
{P : list α → list α → Prop} {l₁ l₂ : list α} (p : l₁ ~ l₂)
(h₁ : P [] [])
(h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x::l₁) (x::l₂))
(h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y::x::l₁) (x::y::l₂))
(h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) :
P l₁ l₂ := 
begin
  have P_refl : ∀ l, P l l :=
  begin
    intro l,
    induction l with a L ih,
    {
      exact h₁,
    },
    {
      exact h₂ a L L (list.perm.refl L) ih,
    },
  end,
  apply list.perm.rec_on,
  {
    exact p,
  },
  {
    exact h₁,
  },
  {
    intro x,
    intros L1 L2 h1 h2,
    exact h₂ x L1 L2 h1 h2,
  },
  { 
    intros x y L,
    exact h₃ x y L L (list.perm.refl L) (P_refl L),
    },
  {
    intros L1 L2 L3 h1 h2 hP1 hP2,
    exact h₄ L1 L2 L3 h1 h2 hP1 hP2,
  },
end

theorem list_sum_squares_permutation {F : Type} [semiring F]
(L1 L2 : list F) : 
(L1 ~ L2) → sum_of_squares L1 = sum_of_squares L2 
:=
begin
  intro h,
  apply list.perm_induction_on h,
  {
    refl,
  },
  { 
    intros x l1 l2 h1 h2,
    simp [sum_of_squares],
    rw h2,
  },
  {
    intros x y l1 l2 h1 h2,
    simp [sum_of_squares],
    rw ← add_assoc,
    rw ← add_assoc,
    rw add_comm (x * x) (y * y),
    rw h2,
  },
  { 
    intros l1 l2 l3 h1 h2 h3 h4,
    rw h3,
    exact h4,
  },
end

theorem list_squares_permutation {F : Type} [semiring F]
(L1 L2 : list F) : 
(L1 ~ L2) → L1.map (λ x, x^2) ~ L2.map (λ x, x^2) 
:=
begin
  intro h,
  apply list.perm_induction_on h,
  {
    simp,
  },
  {
    intros a l1 l2 h1 h2,
    simp,
    exact h2,
  },
  {
    intros a b l1 l2 h1 h2,
    simp,
    exact list.perm.swap' (a ^ 2) (b ^ 2) h2,
  },
  {
    intros l1 l2 l3 h1 h2 h3 h4,
    exact list.perm.trans h3 h4,
  },
end

theorem list_map_permutation {F : Type} 
(L1 L2 : list F) (f : F → F) : 
(L1 ~ L2) → L1.map (λ x, f x) ~ L2.map (λ x, f x) 
:=
begin
  intro h,
  apply list.perm_induction_on h,
  {
    simp,
  },
  {
    intros a l1 l2 h1 h2,
    simp,
    exact h2,
  },
  {
    intros a b l1 l2 h1 h2,
    simp,
    exact list.perm.swap' (f a) (f b) h2,
  },
  {
    intros l1 l2 l3 h1 h2 h3 h4,
    exact list.perm.trans h3 h4,
  },
end

theorem sum_of_sq_has_one_eq_minus_one (L : list ℝ)(x : ℝ)
(h1: (x : ℝ) ∈ L ∧ x = 1 )
(h2: sum_of_squares L = 0) : sum_of_squares L = -1 :=
begin
  have h3 : sum_of_squares(L) = sum_of_squares(x::L.erase(x)),
  begin
    apply list_sum_squares_permutation,
    have hx : x ∈ L := sorry,
    have stupid : L.erase(x) ~ L.erase(x) := sorry,
    have H : x ∈ L ∧ L.erase(x) ~ L.erase(x) := 
    begin 
      split,
      exact hx,
      exact stupid,
    end,
    have aux := list.cons_perm_iff_perm_erase.2 H,
    symmetry,
    exact aux,
  end,
  sorry,
end
