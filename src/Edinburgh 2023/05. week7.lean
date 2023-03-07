/- A word on class inference -/

-- Examples from:
-- Mathematics in Lean
--   (https://leanprover-community.github.io/mathematics_in_lean/06_Abstract_Algebra.html)

import data.real.basic

-- We can define a custom type class group₂ and a related function

class group₂ (α : Type*) :=
(mul: α → α → α)
(one: α)
(inv: α → α)
(mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_one: ∀ x : α, mul x one = x)
(one_mul: ∀ x : α, mul x one = x)
(mul_left_inv : ∀ x : α, mul (inv x) x = one)

#check @group₂.mul

def my_square {α : Type*} [group₂ α] (x : α) := group₂.mul x x

#check @my_square

-- Let's think about the type of equivalences of a type α

section
variables (α β γ : Type*)
variables (f : α ≃ β) (g : β ≃ γ)

#check equiv α β
#check (f.to_fun : α → β)
#check (f.inv_fun : β → α)
#check (f.right_inv: ∀ x : β, f (f.inv_fun x) = x)
#check (f.left_inv: ∀ x : α, f.inv_fun (f x) = x)

#check (equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).to_fun x = g.to_fun (f.to_fun x) := rfl

example (x : α) : (f.trans g) x = g (f x) := rfl

example : (f.trans g : α → γ) = g ∘ f := rfl

end

-- Here we show that the equivalences of α are an instance of group₂

instance {α : Type*} : group₂ (equiv.perm α) :=
{ mul          := λ f g, equiv.trans g f,
  one          := equiv.refl α,
  inv          := equiv.symm,
  mul_assoc    := λ f g h, (equiv.trans_assoc _ _ _).symm,
  one_mul      := equiv.trans_refl,
  mul_one      := equiv.refl_trans,
  mul_left_inv := equiv.self_trans_symm }

-- Now class inference can be performed

section
variables {β : Type*} (f g : equiv.perm β)

example : group₂.mul f g = g.trans f := rfl

example : my_square f = f.trans f := rfl

end

-- By registering instances of `has_mul` etc, we can use notation

instance has_mul_group₂ {α : Type*} [group₂ α] : has_mul α := ⟨group₂.mul⟩

instance has_one_group₂ {α : Type*} [group₂ α] : has_one α := ⟨group₂.one⟩

instance has_inv_group₂ {α : Type*} [group₂ α] : has_inv α := ⟨group₂.inv⟩

section
variables {α : Type*} (f g : equiv.perm α)

#check f * 1 * g⁻¹

def foo: f * 1 * g⁻¹ = g.symm.trans ((equiv.refl α).trans f) := rfl

end