
# **Introduction to Lean**

**Author:** Florent Schaffhauser, Uni-Heidelberg, Summer Semester 2023

**Lean is a programming language** that can be used as a *proof assistant* (also called an *interactive theorem prover*).

This means that Lean can be used to check and certify the correctness of certain computer programmes and formalised mathematical proofs.

It was created and first implemented by **Leonardo de Moura** at Microsoft Research, where the first version was launched in 2013.

The current version is Lean 4, dating back to 2021. It is not backwards-compatible wih **Lean 3**, which is the version that we use for the purposes of this seminar.

## Types and terms

In Lean, we have access to certain data types, which are part of the language.

The command `#check` tells us the type of an expression, for instance `char` for a character, `string` for a string of characters, and `ℕ` (also called `nat`) for an integer.  This last one will turn out to be of a different "nature" than the first two.

If `#check t` returns `T`, one says that **`t` is a term of type `T`**. This is abbreviated to `t : T`.

```lean
#check 'H'
#check "Hello, world!"
#check 42

#check "Hello, ".append( "world!" )
#check 41 + 1
```

The data types `string` and `ℕ` are themselves terms of type `Type`. You can obtain the symbol `ℕ` by typing `\nat` or `\N` followed by the space bar. You can also just use `nat` instead of `ℕ`.

```lean
#check string
#check ℕ 
#check nat
```

Not all data types are terms of type `Type`. Some are more complex than that, for instance the type `list`.

```lean
#check [ "Hello, ", "world!" ]
#check [ 1, 2, 3 ]

-- We will see later what the following result means.

#check list
```

If `T` is a type, `list T` is the type of *lists of terms of type `T`*. We will see later how the lists of terms of type `T` are defined.

```lean
#check list string
#check list nat 
```

Note that we cannot have a list containing terms of different types. Nor can we have a list of lists, which might be counterintuitive compared to other programming languages you may know (it comes from the way `list` is defined, which we will see later.)

Uncomment the following commands to see that indeed Lean does not accept them.

```lean
-- #check [ 1, "a" ]
-- #check list list 
-- #check list list nat
```

A particularly important type for us will be the type `Prop`, which he used to denote the type whose terms are formal statements, *regardless of whether they are true or not*.

Note that a formal statement does *not* have to be a mathematical statement. And if it is a mathematical statement, it does not have to be correct.

```lean
#check 1 + 1 = 2
#check 1 + 1 = 3

#check "Hello, ".append("world!") = "Hello, world!"
```

All three terms above are natural numbers, but Lean does not perform any kind of computation to check whether the equality in the statement is true or not.

```lean
#check 1 + 1 
#check 2
#check 3
```

However, we can *evaluate* certain expressions and see whether the result corresponds to what we think these expressions are.

Not all expressions can be evaluated, though.

```lean
#eval 1 + 1 
#eval "Hello, ".append("world!")
```

-- Uncomment the next two lines to see that the proposed terms cannot be evaluated

```lean
-- #eval 1 + 1 = 2
-- #eval "Hello, ".append("world!") = "Hello, world!"
```

If we look at the term of type Prop `1 + 1 = 2`, we see that it looks like something that should be *provable*, and in a formal sense. In fact it is so, and we will soon learn how to write a proof of it.

But first, a word about the syntax. And expression of the form `def t : T`, where `t` is of type `T`, means that that we are about to *define* a term `t` that will be of type `T`.

The `def` is used to store a data type and keep a `record` of it, which will enable us to call it later, for instance via the command `#print` or inside another definition. This can be applied to all the examples seen so far.

In order to use the recorded terms later, we choose names that are easy to remember (for instance we do not use `Def_1` or similar labels as names).

```lean
def my_first_sentence : string := "Hello, world!"
def my_favourite_integer : ℕ := 42

#check my_first_sentence
#check my_favourite_integer

-- #print my_first_sentence
-- #print my_favourite_integer

def my_second_sentence : string := "Hello, ".append("world!")
def my_brother_s_favourite_integer : nat := 41 + 1

#check my_second_sentence
#check my_brother_s_favourite_integer

-- #print my_second_sentence
-- #print my_brother_s_favourite_integer
```

Now let us see a particularly important case, in which we define a term of type `P` for `P`a term of type `Prop`. The meaning of such a definition is encapsulated in the following slogan.

**If `P` is a term of type `Prop`, then defining a term of type `P` means proving `P`.**

As earlier, the actual definition of a term `p : P` comes after the `:=` symbol. So here, *what comes after `:=` will be the proof of the proposition `P`*. If we do not know what to put after that symbol, we can always write `sorry` and come back to it later.

Seeing a proposition `P` as a type, and terms of type `P` as proofs of `P`, is known as the [**Curry-Howard correspondence**](https://en.wikipedia.org/wiki/Curry–Howard_correspondence).

```lean
-- def one_plus_one_eq_two : 1 + 1 = 2 := sorry
-- #check one_plus_one_eq_two 

-- def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := sorry
-- #check my_two_sentences_are_the_same

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := sorry 
-- #check my_brother_and_I_agree 
```

It is also possible to declare these as theorems, using the command `theorem`. Let us do it below but in a separate "environment", so there is no conflict and we can use the same name for the `theorem` as we did for the `def`.

We can enter a different environment by using the command `namespace`. The name `playground` is arbitrary. However, we cannot use it more than once in the entire document.

```lean
namespace playground 

-- theorem one_plus_one_eq_two : 1 + 1 = 2 := sorry
-- #check one_plus_one_eq_two 

-- theorem my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := sorry
-- #check my_two_sentences_are_the_same

-- theorem my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := sorry 
-- #check my_brother_and_I_agree 

end playground
```

Note that Theorems `my_two_sentences_are_the_same` and `my_brother_and_I_agree` can be written in a way that resembles Theorem `one_plus_one_eq_two` more.

On the one hand, it is less readable. On the other hand, the information is more directly visible.

```lean
namespace Spielplatz 

-- theorem my_two_sentences_are_the_same : "Hello, world!" = "Hello, ".append("world!") := sorry
-- #check my_two_sentences_are_the_same

-- theorem my_brother_and_I_agree : 42 = 41 + 1 := sorry 
-- #check my_brother_and_I_agree 

end Spielplatz
```

## **Proving equalities**

Let us finally prove the results stated above. There at least three ways to write these proofs, more or less concise, and we will present all three.

Note that what all our statement have in common is that they are **equalities**. Now, in Lean, this is a strong requirement: **an equality between terms in Lean means that the two terms are *definitionally* equivalent**.

It is difficult at this moment to explain what this means, but basically it says that `1 + 1 = 2` holds because the terms `1 + 1` and `2` have the same formal definition.

The point is, if you have to prove an equality, you should first try to see if it holds *by definition*. This will indeed be the case for `1 + 1 = 2`.

### **First way of writing the proof : tactic mode**

Proofs are usually written using the *tactic mode*, which we enter with a `begin`command and exit with an `end` command.

At the end of the proof, one should get a `goals accomplished` message in the *local context* to the right of the VS Code / CoCalc window (the *Infoview* tab).

**This will not happen, though, if you do not put a comma before the `end` command**.

The tactic we use here is called `reflexivity` which you can think of as saying that if two terms `a` and `b` have the same definition according to Lean, then the equality `a = b` is true. It can abbreviated to `refl`.

```lean
def one_plus_one_eq_two : 1 + 1 = 2 := 
begin
  reflexivity,
end

-- def one_plus_one_eq_two : 1 + 1 = 2 := 
-- begin
--   refl,
-- end
```

### **Exercise 1**

Use the `reflexivity` tactic to prove the results below.

```lean
-- def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := 
-- begin
--   sorry,
-- end

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := 
-- begin
--   sorry,
-- end
```

### **Second way of writing the proof: tactic mode revisited**

For short tactic proofs like this, we can dispense with the `begin` ... `end` and replace it with a `by { *name-of-the-tactic* }`.

You can play around with the examples below, but do not forget to first comment out the definitions introduced above, because I have used the same name in both cases.

```lean
-- def one_plus_one_eq_two : 1 + 1 = 2 := by { reflexivity }

def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := by { reflexivity }

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := by { reflexivity }
```

### **Third way of writing the proof: proof terms**

A tactic proof is mostly useful when we reach a certain level of complexity, which requires that said proof be carried out in various steps (tactic mode is also the way proofs are usually constructed in the daily practice of mathematics).

But in any case, what Lean does is *compile the tactic proof into a proof term*, which becomes accessible via the `#print` command.

We can then use that proof term to provide a proof without entering tactic mode, simply by copying the proof term generated via the `#print` command (it will appear in the Infoview* tab if you put the keyboard cursor on the same line as the `#print` command) and pasting it after the `:=` symbol.

We test this out below with the `my_brother_and_I_agree` proposition.
Note that, in this case, Lean generates no `goal accomplished` message (this is only in tactic mode). If you use a proof term, the only way to know it worked is via the absence of an error message.

```lean
#print my_two_sentences_are_the_same

def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := eq.refl my_first_sentence

def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := eq.refl my_favourite_integer
```

### **Exercise 2**

Use a proof term to write a proof of `1 + 1 = 2`.

Note that `eq.refl ( 1 + 1 )` and `eq.refl 2` work equally well and check that this is also the case for the definitions of the terms `my_two_sentences_are_the_same` and `my_brother_and_I_agree`.

At this stage, it might be instructive to try out `#check eq.refl 2` and `#check eq.refl ( 1 + 1 )`. Or even `#check eq.refl my_favourite_integer` and `#check eq.refl my_first_sentence`. See below for the corresponding code and a remark on the content of `eq.refl 2`.

Try also `#check eq.refl` and `#check @eq.refl`. Using `@` should produce something better-looking.

```lean
def one_plus_one_eq_two_again : 1 + 1 = 2 := eq.refl (1 + 1)
```

The following command `#check eq.refl 2` returns `eq.refl 2 : 2 = 2`, which means that `eq.refl 2` is a term of type `2 = 2`. In other words, **`eq.refl 2` is a proof of the Proposition `2 = 2`.** This is crucial in understanding how *Lean* works.

```lean
#check eq.refl 2

-- #check eq.refl ( 1 + 1 )
-- #check eq.refl my_favourite_integer
-- #check eq.refl my_first_sentence

-- #check eq.refl
-- #check @eq.refl
```

In Exercise 2, the term which is being defined has been given a different name: it is still a term of type `1 + 1 = 2` but now it is called `one_plus_one_eq_two_again`.

So we now have two terms of type `1 + 1 = 2`, namely `one_plus_one_eq_two` and `one_plus_one_eq_two_again`. We will now prove that they are equal, using the only tactic we have for now!

```lean
def the_two_proofs_we_gave_are_equal : one_plus_one_eq_two = one_plus_one_eq_two_again := by { refl }
```

To conclude this session, let us see an example of a case when we do not get what we might expect at all. If we write to write fractions naively, we see that the types of those terms is not what we think it is.

```lean
#check 42 / 21
#check 1 / 3
#check 0.5

#eval 42 / 21
#eval 1 / 3
#eval 0.5

#eval 1 / 2
```

The above fact comes from the *definition* of the operation `/`, which is not what we might expect. And since this is a definition, we can prove funny identities. To understand the following, note that 42 / 15 = 2.8 as decimal numbers.

```lean
#eval 42 / 15
#eval 2.8

def fun_fact_1 : 42 / 15 = 2 := eq.refl ( 42 / 15 ) 
def fun_fact_2 : 2.8 = 2 := eq.refl ( 42 / 15 ) 
def fun_fact_3 : 2.8 = 2.7 := eq.refl ( 42 /15 ) 
```

As a final remark, we point out that, in Lean, it is possible to introduce anonymous definitions, via the `example` command. This can be useful if it is a definition of a term that we do not plan to use again after introducing it and we do not want to waste a name on it.

```lean
example : 2.8 = 2.7 := by { refl }
```

---
