import data.int.basic
import data.setoid.basic

def even (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k

def even_diff (n m : ℤ) : Prop := even (n - m)

infix ` ≡ `:50 := even_diff

def r ( a b : ℤ ) : Prop := a ≡ b

-- theorem r_is_equiv_rel : equivalence r := 
--   begin
--     unfold equivalence,
--     split,
--     {
--       unfold reflexive,
--       unfold r,
--       intro x,
--       unfold even_diff,
--       unfold even,
--       use 0,
--       simp,
--     },
--     split,
--     {
--       unfold symmetric,
--       unfold r, 
--       unfold even_diff,
--       unfold even,
--       intros x y,
--       intro h,
--       cases h with m,
--       use -m,
--       simp,
--       sorry, 
--     },
--     {
--       sorry,
--     },
--   end


lemma reflexive_r : reflexive r := 
  begin
    unfold reflexive,
    unfold r,
    unfold even_diff,
    unfold even,
    intro x,
    simp,
    use 0,
    simp,
  end

lemma symmetric_r : symmetric r := 
  begin
    unfold symmetric,
    intros x y,
    unfold r,
    unfold even_diff,
    unfold even,
    intro h,
    cases h with k h_k,
    use -k,
    simp,
    apply eq_neg_of_eq_neg,
    rw ← mul_neg_one,
    simp,
    symmetry,
    exact h_k,
  end
  
lemma transitive_r : transitive r := 
  begin
    unfold transitive r even_diff even,
    intros x y z,
    intro h_xy,
    cases h_xy with k h_xy,
    intro h_yz,
    cases h_yz with l h_yz,
    use k+l,
    have h : x-z= 2*k + 2*l :=
      begin
        have h : (x-y) + (y-z) = x-z := by simp,
        rw ← h,
        rw h_xy,
        rw h_yz,
      end,
    rw h,
    rw mul_add,
  end

theorem r_is_equiv_rel_alt : equivalence r := 
mk_equivalence r reflexive_r symmetric_r transitive_r 





