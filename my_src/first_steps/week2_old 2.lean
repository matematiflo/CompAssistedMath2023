/- # **Functions**

**Author:** Florent Schaffhauser, Uni-Heidelberg, Summer Semester 2023

Our goal in this file is to keep exploring basic definitions and tactics in Lean. It is a direct follow-up to the previous [*Introduction to Lean*](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/week1.lean).

The main objective today is to learn about functions:

* How to define basic functions in Lean
* How to *curry* and *uncurry* functions 
* How to define *dependent types* and how to use them

As a matter of fact, we have already seen an important example of a function, in the [*modus ponens* file](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/Practice_folder/modus_ponens.lean), where we also learned about the following tactics:

* `exact`
* `apply` 
* `intro`
* `cases`

In what follows, we will encounter new tactics:

* `unfold`
* `rewrite` (also abbreviated `rw`)
* `use`
* `ring` (whose library we will need to import, see below)

Recall that in [week1.lean](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/week1.lean), we also learned about the `reflexivity` tactic, usually abbreaviated to `refl`.

We start by importing the `tactic.ring` library, which will be used in this file. The `import` command must be used at the beginning of the .lean file. 

As a consequence of this import, the basic `goals accomplished` message of Lean gets upgraded to the fancy `goals accomplished 🎉` version :-) Check it out in the file below! -/

-- import tactic.ring

/- ## **Defining a function**

There are several ways to define a function in Lean, all of them useful depending on the context.

The basic type-theoretical aspect behind what we are about to see is that, if `X` and `Y` are types, then we can construct terms of type `X → Y`, which is the type of functions from `X` to `Y` (the symbol `→` is called a *constructor*).

We have already seen several types, for instance `ℕ` (the type of natural numbers), `ℤ` (the type of integers), but also `Prop`, `char`, `string` or `list ℕ`. A `#check` command on any one of those will reveal that these types are all terms of type `Type` (note the capitalized `T` in `Type` here), which is the type with which we will be working most of the time. Indeed, if `X` and `Y` are terms of type `Type`, then the type `X → Y` is also a term of type `Type`, as we shall see in the examples below. -/

/- ### First definition of a function

The basic syntax presented below should be thought of as a precise version of the intuitive notation `f₁(n) := - 2 * n + 5`, which means that `f₁(n)` is *defined* to be equal `- 2 * n + 5`. This is certainly meaningful if we specify that `n` is a term for which the expression `- 2 * n + 5` makes sense, for instance `n : ℤ`, in which case `- 2 * n + 5` is also a term of type `ℤ`. So this will define a term `f₁ : ℤ → ℤ`, ¡.e. a function from `ℤ` to `ℤ`. 

The notation f₁ obtained via `f\1`.

Of course we could also want to define `f₁` as a function `ℕ → ℤ` (i.e. a sequence of integers), in which case we need to be more careful with the syntax. Here is a definition of such a function `f₁` that is fully precise, in which `n` is a term of type `ℕ` and `f₁(n)` (also denoted simply by `f₁ n`, without a need for parentheses) is a term of type `ℤ`. -/

def f₁ (n : ℕ) : ℤ := - 2 * n + 5 

#check f₁
#check f₁ 5
#eval f₁ 5

/- Note that, if you print `f₁`, you will see that Lean introduces a symbol `↑`, which is a *coercion*. meaning that the natural number `n : ℕ` is *coerced* (forcely converted) into an integer `n : ℤ`, for which the term `- 2 * n + 5` makes sense. -/

-- #print f₁

/- If we declare `f₁` to be a function from `ℤ` to `ℤ` instead, then we do not need to indicate the type of `f₁ n` in the definition, because for `n` of type `ℤ`, the term `- 2 * n + 5` is automatically recognised as being of type `ℤ`. -/

def f (n : ℤ) := - 2 * n + 5 

#check f
#check f 5
#eval f 5

/- ### Second definition of a function 

Next, we define the same function one more time, but in a slightly different way, emphasising in the declaration that `f₂` is a term of type `ℕ → ℤ`. This makes the first part of the defintion perhaps slightly more readable but then, after the `:=` sign, we have to introduce the term `n` using the `λ` notation, which gives its name to [`λ`-calculus](https://en.wikipedia.org/wiki/Lambda_calculus#Origin_of_the_λ_symbol).

In the definition of `f₂`, I indicated the coercion symbol `↑` explicitly, but it is not necessary (the symbol `↑` is obtained by typing in `\u`, as in *up*). -/

def f₂ : ℕ → ℤ := λ n, -2 * ↑n + 5

#check f₂
#check f₂ 5
#eval f₂ 5

/- Using the command `#print` reveals that `f₁` and `f₂` are indeed the same function, and this is something we can actually prove. Since this is true *by definition*, we can prove it using the `refl` tactic. -/

-- #print f₂

def f1_and_f2_are_the_same_function : f₁ = f₂ := by { refl }

/- Note that `refl` can also be used to prove basic results such as the fact that the value of `f₁ 5` is equal to `-5`. Since we have no need of a name for this result, we simply declare it as an `example`, which is similar to `def` but without having to give a name to what we are defining (this implies that we cannot perform a `#check` or a `#print` afterwards). -/

example : f₁ 5 = -5 := by { refl }

/- ### Third definition of a function 

In this third option, we do not specify the type of `f₃` before the definition, so we have to be more detailed about the type of both `n` and `- 2 * n + 5` after the `:=` symbol. It is still the exact same function as `f₁` and `f₂`, though. -/

def f₃ := λ (n : ℕ), (-2 * n + 5 : ℤ)

example : f₂ = f₃ := by { refl }

/- ## **Functions of several variables** 

Explain the currying process... talk about prod... -/

def u (k : ℕ) (n : ℕ) : ℕ := k^n

#print u

variable (k : ℕ) 

#check u k

#eval u 2 4

/- Generating proofs with functions -/

def MP {P Q : Prop} (p : P) (f : P → Q) : Q := f p

def a := ( 2 : ℤ )
def b := 2 * a

def proof_b_eq_4 : ( b = 4 ) :=
begin
  have ha : (a = 2) := by reflexivity,
  have hb : (b = 2 * a) := by reflexivity,
  exact eq.subst ha hb,
end

#print proof_b_eq_4

def h : a = 2 → b = 4 := 
begin
  --  unfold b,
  --  unfold a,
  -- intro h1,
  -- reflexivity,
  tauto,
end

#check h
#print h

def proof_b_eq_4_bis : ( b = 4 ) := MP (eq.refl a) h

-- NEXT ONE IS MUCH, MUCH BETTER

def MP_example { n : ℤ } ( ha : n = 2 ) ( h : n = 2 → 2 * n = 4 ) : ( 2 * n = 4 ) := MP ha h

#check @MP_example
#print MP_example

def my_example { n : ℤ } : ( n = 2 → 2 * n = 4 ) := 
begin
  intro hn,
  rw hn,
  refl,
end

#check ℤ 
#check Prop

#print my_example

/- More on equality in Lean, equivalence relations -/

#check @eq.symm
#check @eq.trans

#check @eq.subst

namespace injectivity

variables {X Y Z : Type}

def comp (f : X → Y) (g : Y → Z) : X → Z  := λ (x : X), g (f x)

def id {X : Type} : X → X := λ x, x

#check @comp 
#check @id

def is_injective (f : X → Y) : Prop := ∀ x1 x2, f x1 = f x2 → x1 = x2

def has_left_inv (f : X → Y) : Prop := ∃ g : Y → X, ∀ x : X, g (f x) = x  

#check @is_injective

def has_left_inv_implies_is_injective (f : X → Y) : has_left_inv f → is_injective f :=
begin
  unfold has_left_inv,
  intro h,
  cases h with g h,
  unfold is_injective,
  intros x1 x2 hf,
  rw ← h x1,
  rw hf,
  exact h x2,
end

def left_inv_implies_is_injective (f :X →Y) (g : Y → X) : (∀ x : X, g (f x) = x) → is_injective f :=
begin
  intro left_inv,
  -- unfold is_injective,
  intros x1 x2 h,
  have h1 : g (f x1) = g (f x2) := eq.subst h (eq.refl (g (f x1))),
  have h2 : g (f x1) = x2 := eq.subst (left_inv x2) h1,
  exact eq.subst (left_inv x1) h2,
end

def left_inv_implies_is_injective_bis (f :X →Y) (g : Y → X) : (∀ x : X, g (f x) = x) → is_injective f :=
begin
  intro left_inv,
  -- unfold is_injective,
  assume x1 x2 h,
  rw ← left_inv x1,
  rw ← left_inv x2,
  rw h,
end

#print left_inv_implies_is_injective
#print left_inv_implies_is_injective_bis

end injectivity

/- And finally, some mathematics

Existential statements are still complicated, though, they should in the lecture on inductive types...

 -/

def div_by_two (n : ℤ) : Prop := ∃ k, n = 2 * k

def two_is_even : ∃ k : ℤ, 2 = 2 * k := 
-- by {use 1, refl}
begin
  apply exists.intro (1 : ℤ), -- or use 1, (does not produce the same proof term, though)
  exact eq.refl 2, -- or refl,
  -- exact exists.intro 1 (eq.refl 2),
end

#print two_is_even

def two_is_even_term_mode_proof : ∃ k : ℤ, 2 = 2 * k := 
exists.intro 1 (eq.refl 2)

def div_by_four (n : ℤ) : Prop := ∃ k, n = 4 * k

def div_by_four_implies_div_by_two (n : ℤ) : div_by_four n → div_by_two n := 
begin
  dsimp [div_by_four],
  dsimp [div_by_two],
  -- unfold div_by_four,
  -- unfold div_by_two,
  intro h,
  cases h with p hp,
  -- use (2 * p),
  apply exists.intro (2 * p),
  rw hp,
  -- rw ← int.mul_assoc,
  -- refl,
  ring,
end

def div_by_two_because_div_by_four {n : ℤ} (h : div_by_four n) : div_by_two n := 
begin
  dsimp [div_by_four] at h,
  dsimp [div_by_two],
  cases h with m hm,
  apply exists.intro (2 * m),
  rw hm,
  ring,
end

#print div_by_four_implies_div_by_two

#check div_by_two
#check div_by_two 2
#check div_by_two 3

-- #print is_even

def even_diff (n m : ℤ) : Prop := div_by_two (n - m)

def even_diff_is_reflexive : ∀ n, even_diff n n :=
begin
  intro n,
  -- unfold even_diff,
  -- unfold div_by_two,
  --
  -- show ∃ k, n - n = 2 * k,
  --
  use 0,
  -- ring,
  -- write the following using calc? TRY IT!
  -- also do it by *substituting* into equalities
  rw int.mul_zero,
  rw int.sub_eq_add_neg,
  rw int.add_right_neg,
end

#print even_diff_is_reflexive

def test {P Q : Prop} (p : P) : P ∨ Q :=
begin
  left,
  exact p,
end

#check @test
-- #print test

/- ## **Universal statements (`∀ x, P x`)**

Functions with values in `Prop` can be used to formalise equivalence relations or, more fundamentally, just a basic property... -/

def squares_are_nonneg (n : ℤ) : Prop := n^2 ≥ 0

#check squares_are_nonneg
#check squares_are_nonneg 2

#eval squares_are_nonneg 2

variable m : ℤ
#check squares_are_nonneg m
#eval squares_are_nonneg m

def proof_that_sq_are_nonneg (n : ℤ) : n^2 ≥ 0:= sq_nonneg n

def proof_that_sq_are_nonneg_bis (n : ℤ) : squares_are_nonneg n := sq_nonneg n

/- `∀` statements can be formalised using dependent types, and indeed we see that the type `n^2 ≥ 0` depends on the term `n` -/
def P (n : ℤ) : n^2 ≥ 0 := --sq_nonneg n
begin
  exact sq_nonneg n,
  -- apply sq_nonneg,
end

/- Here we see why the first option (with the dependent type) is the best -/
#check proof_that_sq_are_nonneg
#check proof_that_sq_are_nonneg 2

#check proof_that_sq_are_nonneg_bis
#check proof_that_sq_are_nonneg_bis 2

#check proof_that_sq_are_nonneg m


#check P
#print P

def P1 : ∀ n : ℤ, n^2 ≥ 0 := sq_nonneg
-- begin
--   exact sq_nonneg,
-- end
/- Note that the proof term of Pf1 is different from that of Pf, due to the slight modification in the input syntax, although one could argue that it is (also?) due to the syntax of `sq_nonneg` -/

#check P1
#print P1

/-
---
-/
