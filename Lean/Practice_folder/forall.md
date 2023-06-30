
# Dependent types

````lean
import tactic
attribute [pp_nodot] nat.succ -- used to make sure that `n.succ` appears as `succ n`.
open nat
````

## Universal statements (`∀ x, P x`)

Statements of the form `∀ (n : ℕ), P n`, where `P : ℕ → Prop` is a *sequence of propositions*, are common in mathematics (the symbol `∀` is obtained by typing `\forall` or even simply `\fo`).

Similarly, we could have a statement of the form `∀ (n : ℤ), P n`. For instance, the fact that the square of an integer `n` is non-negative, can be written as follows

````lean
`∀ (n : ℤ), n^2 ≥ 0`
````

and this, too, is a statement that Lean understands.

````lean
#check ∀ (n : ℤ), n^2 ≥ 0
````

In fact, this result is proved under a very general form in `mathlib`, the mathematical library of Lean. It is recorded there as a function `sq_nonneg : R → Prop` which sends a term `a` of type `R` (where `R` is an ordered ring) to a proof of the proposition `a^2 ≥ 0`.

````lean
#check @sq_nonneg
````

To understand better how the function `sq_nonneg` works, let us use it here to construct a more specific function called `squares_are_non_neg`, which sends an integer `n` to a proof of `n^2 ≥ 0`.

````lean
def squares_are_non_neg : ∀ (n : ℤ), n^2 ≥ 0 :=
begin
intro n,
exact sq_nonneg n,
end

#check squares_are_non_neg
#check squares_are_non_neg 3
````

This last `#check` gives us a hint of how a such a so-called *universal statement* is defined.

As we see, `squares_are_non_neg 3` is *a proof of the proposition* `3^2 ≥ 0`.

So `squares_are_non_neg` is a function from `ℤ` to `Prop` that sends `n : ℤ` to a proof of `n^2 ≥ 0 : Prop`. In other words, `squares_are_non_neg n` is a term of type `squares_are_non_neg n`, *a type that itself depends on* `n`.

Such a type is called a **dependent type**. We used dependent types here in order to define a statement involving the *universal quantifier* `∀`.

To define the function `squares_are_non_neg` without using the symbol `∀`, we proceed as follows.

````lean
def squares_are_non_neg_bis (n : ℤ) : n^2 ≥ 0 := --sq_nonneg n
begin
  exact sq_nonneg n,
end
````

This syntax makes it clearer that `squares_are_non_neg_bis n` is a term of type `n^2 ≥ 0`, which is seen to depend on `n`.

Note that, after the initial declaration, the rest of the definition of `squares_are_non_neg_bis` is the same as for `squares_are_non_neg`, except that we no longer need to introduce `n` when going into tactic mode.

If we check the type of `squares_are_non_neg_bis`, we find the exact same thing as for `squares_are_non_neg`.

````lean
#check squares_are_non_neg
#check squares_are_non_neg_bis
````

## Exercise 1

Write a proof of `∀ (n : ℤ), n^2 ≥ 0` without using the function `sq_nonneg`.

Hint: using `by_cases n ≥ 0`, separate the cases `n ≥ 0` and `n ≤ 0`. When `n ≥ 0`, then find in `mathlib` a proof of `∀ a b, (a ≥ 0 ∧ b ≥ 0) → ab ≥ 0` (or something similar) and apply it with `a = b = n`. When `n ≤ 0`, argue that `n^2 = (-n)^2` and that `-n ≥ 0`, then repeat the previous argument.

Here is something to get you started. Try to fill in the `sorry`s. The solution is available in the [Solutions](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/Practice_folder/Solutions/) folder.

````lean
example : ∀ (n : ℤ), n^2 ≥ 0 :=
begin
  intro n, 
  by_cases n ≥ 0,
  {
    rw sq,
    apply mul_nonneg h,
    sorry,
  },
  {
    simp at h,
    rw ← neg_sq,
    rw sq,
    sorry,
  },
end
````

# Functions defined recursively

## The factorial function

Let us give an example of a function defined recursively.

A natural number is either `0` or of the form `n+1` for some already defined natural number `n`. So, to define a function on the natural numbers, it suffices to define it in these two cases.

The syntax to do that is as follows. In this example, the definition of `fac (n+1)` uses the already defined `fac n`, making the function recursive.

````lean
def fac : ℕ → ℕ
| 0 := 1
| (n + 1) := (n + 1) * fac n

#check fac
#eval fac 5
````

We can intoduce a commonly used notation for the factorial function. The `:10000` is optional in principle but here it is actually necessary (the number `10000` parameterises the "strength" with which the notation is to be "upheld").

````lean
notation n `!`:10000 := fac n
````

We will prove below that `∀ (n : ℕ), fac n > 0`. Given the way the function `fac` is defined, it makes sense to prove it by induction, using the `induction` tactic.

This can be done directly, which is a good exercise, or we can first define an *induction principle* function, that enables us with the readability of induction as it is performed later in the proof of `∀ (n : ℕ), fac n > 0`.

Indeed, in the definition of the function `induction_pple`, the final goal of the induction appears as `P(succ k)`, while in the proof of `∀ (n : ℕ), fac n > 0`, the successor function `succ` does not appear at all, making everything closer to the usual mathematical notation.

````lean
def induction_pple {P : ℕ → Prop} (p0 : P 0) (ih : ∀ (k : ℕ), P k → P (k + 1)) : ∀ (n : ℕ), P n :=
begin
  intro n,
  induction n with k hk,
  exact p0,
  exact ih k hk,
end

def fac_pos : ∀ (n : ℕ), n! > 0 :=
begin
  apply induction_pple,
  {
    -- rw fac,
    exact zero_lt_one,
  },
  {
    intro k,
    intro h,
    rw fac, -- unfold fac (also works)
    apply mul_pos,
    apply succ_pos,
    exact h,
  },
end

#check fac_pos
````

## Exercise 2

Define a function `S : ℕ → ℚ` sending `n` to `0 + 1 + 2 + ... + n`, then prove by induction that `∀ n : ℕ, S n = n * (n+1) / 2`.

---
