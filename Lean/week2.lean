/- # **Functions and logical implications**

**Author:** Florent Schaffhauser, Uni-Heidelberg, Summer Semester 2023

Our goal in this file is to keep exploring basic definitions and tactics in Lean. It is a direct follow-up to the previous [*Introduction to Lean*](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/week1.md).

The main objective today is to learn about functions:

* How to define basic functions in Lean
* What it means to *curry* and *uncurry* a function of two variables
* How to use functions to write and prove basic logical implications

As a matter of fact, we have already seen an important example of a function, in the [*modus ponens* file](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/Practice_folder/modus_ponens.lean), where we also learned about the following tactics:

* `exact`
* `apply`
* `intro`
* `cases`

In what follows, we will encounter new tactics:

* `show`
* `split`
* `by_contradiction`

Recall that in [week1.lean](https://github.com/matematiflo/Comp_assisted_math/blob/2023_SoSe/Lean/week1.lean), we also learned about the `reflexivity` tactic, usually abbreaviated to `refl`.

We start by importing the `data.nat.pow` library, which will be used in this file. The `import` command must be used at the beginning of the .lean file. 

As a consequence of this import, the basic `goals accomplished` message of Lean gets upgraded to the fancy `goals accomplished 🎉` version :-) -/

import data.nat.pow
import data.real.basic

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

/- ### Exercise 1

> Given a type `X : Type`, define an "identity function" from `X` to itself.
-/

/- ### Currying and uncurrying

We are used to defining functions of two or more variables as functions from a product set to another set. For instance, a real-valued function of two real variables can be formalised as term of type `ℝ² → ℝ` (the superscript notation `²` is obtained by typing in `\^2` followed by a space character).

To define a term of type `ℝ² → ℝ`, we need to define the type `ℝ²` first. This is already programmed in `Lean`, via the `prod` construction: if `T₁` and `T₂` are types, there is a type `T₁ × T₂` (or `prod T₁ T₂`; the notation `×` is obtained by typing in `\x` followed by a space character), whose terms are pairs `(t₁, t₂)` such that `t₁` is a term of type `T₁` and `t₂` is a term of type `T₂`. -/

#check (3,4)

#check ℕ × ℤ  
#check ( (3, -4) : ℕ × ℤ )

/- By construction, the type `T₁ × T₂` comes equipped with two projection functions `fst : T₁ × T₂ → T₁` and `snd : T₁ × T₂ → T₂`, that we can use to define functions `h : T₁ × T₂ → T₃`. -/

#check (3,4).fst
#check (3,4).snd

/- They can also be denoted by `.1` and `.2`. -/

#eval (3,4).1
#eval (3,4).2

def h : ℕ × ℕ → ℕ := λ x, 2 * x.1 + x.2

/- However, it is *much more convenient* to define a function of two variables `T₁ × T₂ → T₃` as a function `T₁ →  (T₂ → T₃)`, meaning a function from `T₁` to the functions `T₂ → T₃`. -/

def g : ℕ → (ℕ → ℕ) := λ n m, 2 * n + m

#check g
#eval g 1 3

#check h
#eval h (1, 3)

/- The precise correspondence between terms `h` of type `T₁ × T₂ → T₃` and terms `g` of type `T₁ → (T₂ × T₃)` is given as follows.

If `h : T₁ × T₂ → T₃`, we define, for `t₁ : T₁` the term `(g t₁) : T₂ → T₃` as the function sending `t₂ : T₂` to the term `(g t₁) t₂ := h (t₁, t₂)`, which is indeed of type `T₃`.

Conversely, to a term `g : T₁ → (T₂ → T₃)`, we can associate a term `h` of type `T₁ × T₂ → T₃` by setting `h (t₁, t₂) := (g t₁) t₂`. Since `(g t₁)` is a function from `T₂` to `T₃`, the term `h (t₁, t₂)` thus defined is indeed of type `T₃`.

The process of replacing `h : T₁ × T₂ → T₃` by `g : T₁ → (T₂ → T₃)` is known as [*currying*](https://en.wikipedia.org/wiki/Currying). The reverse process is known as *uncurrying*.

This is basically saying that we can replace a function of two variables `h` from `T₁ × T₂` to `T₃` by a *family* `g` (indexed by `T₁`) of [*partial applications*](https://en.wikipedia.org/wiki/Partial_application) from `T₂` to `T₃`.

Here is for instance a family of sequences of natural numbers. This uses the power function (denoted using the caret symbol `^`), which was imported at the beginning of this file via the `import data.nat.pow` command. -/

def u (q : ℕ) (n : ℕ) : ℕ := q^n

variable (q : ℕ) 

#check u q
#eval u 2 4

/- It is easy to iterate this process and define functions  of three variables or more. The upshot is that, under this form, functions of three real variables can be defined without defining a type `ℝ³` first. -/

def F ( x y z : ℝ ) : ℝ := x^2 - y + z

#check F

/- ### Exercise 2

> Given types `X Y Z : Types`, define a function `compose` sending functions `f : X → Y` and `g : Y → Z` to a function `compose f g` from `X` to `Z`, sending a term `x : X` to the term `g (f x)`.  

### ***Logical implications***

### Negatives

There is a proposition (i.e. a term of type `Prop`) called `false` and characterised by the fact that it does not admit a proof. In other words, `false` is a type that has no terms.

Technically, the type `false` is defined as an *inductive type* (we will come back to that later). For now, we will use the type `false` to define negatives.

Indeed, in Lean, given a term `P : Prop`, the type `¬P` is *defined* as the type `P → false` (i.e. the type of functions from `P` to `false`). In other words, supplying a proof of `¬P` means supplying a proof that a to a proof of `P` there is associated a proof of `false`.

It will take a bit of time to wrap our heads around that, so let us start manipulating this notion. The symbol `¬` is obtained by typing in `\n` or `\not`, followed by  a space character. -/

#check false

variables P : Prop
#check ¬P

/- Here is an example of a statement using negatives. It is known as *modus tollens* and it says that `( (P → Q) ∧ ¬Q ) → ¬P`. In other words, if we can prove `P → Q` and `¬Q`, then we can prove `¬Q`.

In order to write a proof of this statement (and many other involving `¬`), it is useful to keep in mind that a term of type `¬P` is (by definition) a term of type `P → false`, meaning a *function* from `P` to `false`, and that it should be manipulated as such. -/

def MT { P Q : Prop } ( hPQ : P → Q ) ( nq : ¬Q ) : ¬P :=
begin
  -- show P → false,
  intro p,
  apply nq,
  apply hPQ,
  exact p,
end

/- The `show` tactic that was used in the proof above is facultative: it enables us to visualise better what we are supposed to prove. It works if, when you write `show t`, Lean is able to find a term that matches `t` in the target.

### The contrapositive

As an application of our definition of the function `MT`, we can prove the implication `(P → Q) → (¬Q → ¬P)`. -/

#check @MT

def contrapositive  { P Q : Prop } : ( P → Q ) → ( ¬Q → ¬P ) :=
begin
  intro hPQ,
  intro nq,
  exact MT hPQ nq,
end

/- The implication `¬Q → ¬P` is known as the [*contrapositive*](https://en.wikipedia.org/wiki/Contraposition#Formal_definition) of the implication `P → Q`.

In practice, it is often used to prove `P → Q` because, if we apply contraposition to `¬Q → ¬P`, we find `¬¬P → ¬¬Q` and, in everyday mathematics, `¬¬P` is equivalent to `P`.

Again, this is a lot to digest, so let us break it down into several steps. -/

def contrapositive_with_double_neg { P Q : Prop } ( H : ¬Q →  ¬P ) : ¬¬P → ¬¬Q :=
begin
  intro f,
  -- show ¬Q → false,
  intro x,
  apply f,
  apply H,
  exact x,
end

/- It is not necessary at this stage, but here is a shorter proof of the previous proposition, which says that `( ¬Q → ¬P ) → ( ¬¬P → ¬¬Q )`. -/

def contrapositive_with_double_neg_again { P Q : Prop } ( H : ¬Q →  ¬P ) : ¬¬P → ¬¬Q :=
begin
  intros f x,
  exact f (H x),
end

/- We now would like to be able to say that `¬¬P ↔ P` (the left-right arrow `↔` means *equivalence* and it is obtained by typing in `\lr`, followed by a space character).

More precisely, we want to prove `P → ¬¬P` and `¬¬P → P`. Without getting too much into the details, let us just mention that there is a way to *split* the proof of an equivalence `P ↔ Q` into two implications `P → Q` and `Q → P` and that this is what the `split` tactic does (see below).

Once we have two implications to prove, we can observe that the implication `P → ¬¬P` does not use any tactic: we prove it by showing that, to a proof of `P`, we can associate a proof of `¬P → false`, which is the definition of `¬¬P`.

For the implication `¬¬P → P`, however, more is needed. We have to argue *by contradiction*. This means that, after introducing a term `g` of type `¬¬P`, we replace the target `P` by `false` *while also adding a term* `h : ¬P` (i.e. a proof of `P → false`) to our local context. -/

def double_neg {P : Prop} : P ↔ ¬¬P :=
begin
  split,
  intro p,
  show ¬P → false,
  intro f,
  exact f p,
  intro g,
  by_contradiction,
  exact g h,
end

/- So, after using the tactic `by_contradiction` (which can be abbreviated to `by_contra`), we have proofs of *both* `¬¬P` and `¬P` in our local context, and this is how we produce a proof of `false`.

Since `false` is a type that has no terms, what we did means that adding a proof of `¬P` to our local context was, in a way, illicit. In other words, we cannot assume that `¬P` has a proof (for otherwise we get a proof of `false`) so this must mean that `P` has a proof.

This is indeed the case for us: we *are working* under the assumption that either `P` or `¬P` has a proof. This known as the [*Law of Excluded Middle*](https://en.wikipedia.org/wiki/Law_of_excluded_middle) (LEM) and [it is needed](https://en.wikipedia.org/wiki/Contraposition#Intuitionistic_logic) in order to prove the equivalence `(P → Q) ↔ (¬Q → ¬P)`.

Note that, since we are now equipped with the tactic `by_contradiction`, we can get rid of the double negatives in the proof of the implication `( ¬Q → ¬P ) → ( ¬¬P → ¬¬Q )` and prove that `( ¬Q → ¬P ) → ( P → Q )`. -/

def contra { P Q : Prop } ( H : ¬Q →  ¬P ) : P → Q :=
begin
  intro p,
  by_contradiction,
  exact (H h) p,
end

/- ### Exercise 3

> Formalise the equivalence `( P → Q ) ↔ ( ¬Q → ¬P )` and use the `split` tactic and the functions `MT` and `contra` defined above to write a proof of it.

---
-/