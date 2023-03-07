/- Inductive types and structures -/

-- Examples taken from:
-- Theorem proving in Lean
--   (https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html)
-- Mathematics in Lean
--   (https://leanprover-community.github.io/mathematics_in_lean/06_Abstract_Algebra.html)

/- 

General syntax for an inductive type:

inductive foo : Sort u
| constructor₁ : ... → foo
| constructor₂ : ... → foo
...
| constructorₙ : ... → foo

-/

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

inductive my_unit : Type
| star : my_unit

universes u v 

inductive my_prod (α : Type u) (β : Type v)
| mk : α → β → my_prod

inductive my_sum (α : Type u) (β : Type v)
| inl : α → my_sum
| inr : β → my_sum

-- The types of propositional logic

inductive my_false : Prop

inductive my_true : Prop
| intro : my_true

inductive my_and (a b : Prop) : Prop
| intro : a → b → my_and

inductive my_or (a b : Prop) : Prop
| intro_left  : a → my_or
| intro_right : b → my_or

inductive my_Exists {α : Type*} (q : α → Prop) : Prop
| intro : ∀ (a : α), q a → my_Exists

-- The natural numbers

inductive my_nat : Type
| zero : my_nat
| succ : my_nat → my_nat

#check @my_nat.rec_on
-- my_nat.rec_on :
--  Π {motive : my_nat → Sort u_1} (n : my_nat),
--    motive my_nat.zero → (Π (ᾰ : my_nat), motive ᾰ → motive ᾰ.succ) → motive n

-- The type of lists

inductive my_list (α : Type*)
| nil {} : my_list
| cons : α → my_list → my_list

section
open my_list

def my_length1 {α : Type*} : my_list α → ℕ
| nil          := by sorry
| (cons hd tl) := by sorry

def my_length2 {α : Type*} : my_list α → ℕ :=
begin
  intro ls,
  cases ls with hd tl,
  { sorry, },
  sorry,
end

end

-- Structures

structure point (α : Type u) : Type u :=
mk :: (x : α) (y : α)

#check point
#check @point.rec_on
#check point.mk
#check point.x
#check point.y

#print prefix point

#check { point . x := 10, y := 20 }  -- point ℕ
#check { point . y := 20, x := 10 }
#check ({x := 10, y := 20} : point nat)

example : point nat :=
{ y := 20, x := 10 }

namespace point

variable {α : Type u}

def add : point α → point α → point α := by sorry 

end point

#check @point.add

-- Structure inheritance

inductive color
| red | green | blue

structure color_point (α : Type*) extends point α :=
mk :: (c : color)

#print prefix color_point
#check color_point.mk
#check color_point.to_point
#check color_point.c


-- Type classes

class my_semigroup (G : Type u) : Type u :=
(mul : G → G → G)
(mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c))

-- Here `class` is equivalent to `@[class] structure`.

instance nat_semigroup : my_semigroup ℕ :=
⟨nat.mul, 
  by sorry⟩

namespace my_semigroup 

#check mul
#check mul_assoc

instance prod_semigroup {G : Type u} {H : Type v} [my_semigroup G] [my_semigroup H] :
  my_semigroup (G × H) :=
⟨λ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩, ⟨mul g₁ g₂, mul h₁ h₂⟩,
  by sorry⟩

end my_semigroup

notation a ` ⋆ ` b := my_semigroup.mul a b

#reduce (1, 2) ⋆ (2, 3)
#reduce (1, 2, 3, 4) ⋆ (4, 3, 5, 1)

class my_monoid (M : Type u) extends my_semigroup M : Type u :=
(one : M)
(one_mul : ∀ a : M, (one ⋆ a) = a)
(mul_one : ∀ a : M, (a ⋆ one) = a)

notation `𝟙` := my_monoid.one

instance prod_monoid {M : Type u} {N : Type v} [my_monoid M] [my_monoid N] :
  my_monoid (M × N) :=
by sorry

/- Now go to https://leanprover-community.github.io/mathlib-overview.html and have a look at how your
  favourite piece of mathematics is treated. You will most likely need to backtrack through a few
  definitions before you find something concrete.

  Also, you can search here: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Mathlib.20semantic.20search.
-/