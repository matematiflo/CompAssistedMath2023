/- Mathematical structures and stuff, starting with equivalence relations -/

inductive my_eq {α : Sort u} (a : α) : α → Prop
| refl [] : my_eq a

#check @my_eq 
#check my_eq 1 2
#check my_eq 1

example : my_eq 1 1 := my_eq.refl 1
  -- begin
  -- exact my_eq.refl 1,
  -- end

example : my_eq 2 (1+1) := my_eq.refl 2
example : my_eq 2 (1+1) := my_eq.refl (1+1)

#check @eq
#check eq 1 1
#check eq 1 2

#print eq

#check nat

inductive my_eq2 {α : Type} (a : α) : α → Prop
| test [] : my_eq2 a

#check @my_eq2
#check my_eq2 1 
#check my_eq2 1 1
#check my_eq2 "Hello"

theorem one_is_equal_to_one : my_eq 1 1 := my_eq.refl 1

#check one_is_equal_to_one

theorem my_eq2_is_reflexive_thm {α : Type} {a : α} : my_eq2 a a := 
my_eq2.test a
-- my_eq2.test a
  -- begin
  -- exact my_eq2.test a,
  -- end

#check @my_eq2_is_reflexive_thm
#print my_eq2_is_reflexive_thm

#check ( ∀ α : Type, ∀ a : α, my_eq2 a a )

def my_eq2_is_reflexive : Prop := ( ∀ {α : Type}, ∀ a : α, my_eq2 a a ) 

-- theorem my_eq2_is_reflexive : ( ∀ {α : Type}, ∀ a : α, my_eq2 a a ) := sorry

#check my_eq2_is_reflexive
#print my_eq2_is_reflexive

theorem a_proof_that_my_eq2_is_reflexive : my_eq2_is_reflexive :=
  --id (λ (α : Type) (a : α), my_eq2.test a)
  begin
  -- unfold my_eq2_is_reflexive,
  intro α,
  intro a,
  exact my_eq2.test a,
  end

#check @a_proof_that_my_eq2_is_reflexive
#print a_proof_that_my_eq2_is_reflexive


universe u

inductive my_eq3 {α : Type} : α → α → Prop
| refl (a : α) : my_eq3 a a

#check @my_eq3
#check my_eq3 1 
#check my_eq3 1 1

#print my_eq3
#print eq

theorem one_is_still_equal_to_one : my_eq3 1 1 := my_eq3.refl 1

#check one_is_still_equal_to_one
#print one_is_still_equal_to_one

example : my_eq3 2 (1+1) := my_eq3.refl 2
example : my_eq3 2 (1+1) := my_eq3.refl (1+1)
example {α : Type} (a b : α) : my_eq3 a b → my_eq3 b a := 
begin
  intro ha,
  induction ha with c,
  exact my_eq3.refl c,
end

example : 1 + 1 = 2 := eq.refl 2

lemma lean_eq.symm {α : Sort u} {a b : α} (h : a = b) : b = a :=
begin
 apply eq.subst h,
 exact eq.refl a,
end

lemma lean_eq.symm2 {α : Sort u} {a b : α} (h : a = b) : b = a :=
begin
 induction h,
 exact eq.refl a,
end

lemma lean_eq.trans {α : Sort u} {a b c : α} (h1 : a = b) (h2 : b = c): a = c :=
begin
 induction h1,
 exact h2,
end 
