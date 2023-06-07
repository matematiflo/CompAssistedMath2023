
/- # **Introduction to Lean**

**Author:** Florent Schaffhauser, Uni-Heidelberg, Summer Semester 2023

**Lean is a programming language** that can be used as a *proof assistant* (also called an *interactive theorem prover*). 

This means that Lean can be used to check and certify the correctness of certain computer programmes and formalised mathematical proofs.

It was created and first implemented by **Leonardo de Moura** at Microsoft Research, where the first version was launched in 2013.

The current version is Lean 4, dating back to 2021. It is not backwards-compatible wih **Lean 3**, which is the version that we use for the purposes of this seminar. -/

/- ## Types and terms -/

/- In Lean, we have access to certain data types, which are part of the language. 

The command `#check` tells us the type of an expression, for instance `char` for a character, `string` for a string of characters, and `ℕ` (also called `nat`) for an integer.  This last one will turn out to be different from the first two.

If `#check t` returns `T`, one says that **`t` is a term of type `T`**. This is abbreviated to `t : T`. -/

#check 'H'
#check "Hello, world!"
#check 42

#check "Hello, ".append("world!")
#check 41 + 1

/- The data types `string` and `ℕ` are themselves terms of type `Type`. You can obtain the symbol `ℕ` by typing `\nat` or `\N` followed by the space bar. You can also just use `nat` instead of `ℕ`. -/

#check string
#check ℕ 
#check nat

/- Not all data types are terms of type `Type`. Some are more complex than that, for instance the type `list`. -/

#check [ "Hello, ", "world!" ]
#check [ 1, 2, 3 ]

-- We will see later what the following result means.

#check list

/- If `T` is a type, `list T` is the type of *lists of terms of type `T`*. We will see later how the lists of terms of type `T` are defined. -/

#check list string
#check list nat 

/- Note that we cannot have a list containing terms of different types. Nor can we have a list of lists, which might be counterintuitive compared to other programming languages you may know (it comes from the way `list` is defined, which we will see later.)

Uncomment the following commands to see that indeed Lean does not accept them. -/

-- #check [ 1, "a" ]
-- #check list list 
-- #check list list nat

/- A particularly important type for us will be the type `Prop`, which he used to denote the type whose terms are formal statements, *regardless of whether they are true or not*.

Note that a formal statement does *not* have to be a mathematical statement. And if it is a mathematical statement, it does not have to be correct. -/

#check 1 + 1 = 2
#check 1 + 1 = 3

#check "Hello, ".append("world!") = "Hello, world!"

/- All three terms above are natural numbers, but Lean does not perform any kind of computation to check whether the equality in the statement is true or not. -/

#check 1 + 1 
#check 2
#check 3

/- However, we can *evaluate* certain expressions and see whether the result corresponds to what we think these expressions are.

Not all expressions can be evaluated, though. -/

#eval 1 + 1 
#eval "Hello, ".append("world!")

-- Uncomment the next two lines to see that the proposed terms cannot be evaluated

-- #eval 1 + 1 = 2
-- #eval "Hello, ".append("world!") = "Hello, world!"

/- If we look at the term of type Prop `1 + 1 = 2`, we see that it looks like something that should be *provable*, and in a formal sense. In fact it is so, and we will soon learn how to write a proof of it.

But first, a word about the syntax. And expression of the form `def t : T`, where `t` is of type `T`, means that that we are about to *define* a term `t` that will be of type `T`.

The `def` is used to store a data type and keep a `record` of it, which will enable us to call it later, for instance via the command `#print` or inside another definition. This can be applied to all the examples seen so far.

In order to use the recorded terms later, we choose names that are easy to remember (for instance we do not use `Def_1` or similar labels as names). -/

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

/- Now let us see a particularly important case, in which we define a term of type `P` for `P`a term of type `Prop`. The meaning of such a definition is encapsulated in the following slogan.

**If `P` is a term of type `Prop`, then defining a term of type `P` means proving `P`**

As earlier, the actual definition of a term `p : P` comes after the `:=` symbol. So here, *what comes after `:=` will be the proof of the proposition `P`*. If we do not know what to put after that symbol, we can always write `sorry` and come back to it later.

Seeing a proposition `P` as a type, and terms of type `P` as proofs of `P`, is known as the **Curry-Howard correspondence**. -/

-- def one_plus_one_eq_two : 1 + 1 = 2 := sorry
-- #check one_plus_one_eq_two 

-- def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := sorry
-- #check my_two_sentences_are_the_same

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := sorry 
-- #check my_brother_and_I_agree 

/- It is also possible to declare these as theorems, using the command `theorem`. Let us do it below but in a separate "environment", so there is no conflict and we can use the same name for the `theorem` as we did for the `def`. 

We can enter a different environment by using the command `namespace`. The name `playground` is arbitrary. However, we cannot use it more than once in the entire document. -/

namespace playground 

-- theorem one_plus_one_eq_two : 1 + 1 = 2 := sorry
-- #check one_plus_one_eq_two 

-- theorem my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := sorry
-- #check my_two_sentences_are_the_same

-- theorem my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := sorry 
-- #check my_brother_and_I_agree 

end playground

/- Note that Theorems `my_two_sentences_are_the_same` and `my_brother_and_I_agree` can be written in a way that resembles Theorem `one_plus_one_eq_two` more.

On the one hand, it is less readable. On the other hand, the information is more directly visible. -/

namespace Spielplatz 

-- theorem my_two_sentences_are_the_same : "Hello, world!" = "Hello, ".append("world!") := sorry
-- #check my_two_sentences_are_the_same

-- theorem my_brother_and_I_agree : 42 = 41 + 1 := sorry 
-- #check my_brother_and_I_agree 

end Spielplatz

/- ## **Proving equalities**

Let us finally prove the results stated above. There at least three ways to write these proofs, more or less concise, and we will present all three.

Note that what all our statement have in common is that they are **equalities**. Now, in Lean, this is a strong requirement: **an equality between terms in Lean means that the two terms are *definitionally* equivalent**.

It is difficult at this moment to explain what this means, but basically it says that `1 + 1 = 2` holds because the terms `1 + 1` and `2` have the same formal definition.

The point is, if you have to prove an equality, you should first try to see if it holds *by definition*. This will indeed be the case for `1 + 1 = 2`. -/

/- ### **First way of writing the proof : tactic mode** 

Proofs are usually written using the *tactic mode*, which we enter with a `begin`command and exit with an `end` command.

At the end of the proof, one should get a `goals accomplished` message in the *local context* to the right of the VS Code / CoCalc window (the *Infoview* tab). 

**This will not happen, though, if you do not put a comma before the `end` command**.

The tactic that we use here is called `reflexivity`, which you can think of as saying that if two terms `a` and `b` have the same definition according to Lean, then the equality `a = b` is true. It can abbreviated to `refl`. -/

def one_plus_one_eq_two : 1 + 1 = 2 := 
begin
  reflexivity,
end

-- def one_plus_one_eq_two : 1 + 1 = 2 := 
-- begin
--   refl,
-- end

/- ### **Exercise** 

Use the `reflexivity` tactic to prove the results below. -/

-- def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := 
-- begin
--   sorry,
-- end

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := 
-- begin
--   sorry,
-- end

/- ### **Second way of writing the proof: compact tactic mode** 

For short tactic proofs like this, we can dispense with the `begin` ... `end` and replace it with a `by {*name-of-the-tactic*}`.

You can play around with the examples below, but do not forget to first comment out the definitions introduced above, because I have used the same name in both cases. -/

-- def one_plus_one_eq_two : 1 + 1 = 2 := by {reflexivity}

def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := by {reflexivity}

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := by {reflexivity}

/- ### **Third way of writing the proof: proof terms**

A tactic proof is mostly useful when we reach a certain level of complexity, which requires that said proof be carried out in various steps (tactic mode is also the way proofs are usually constructed in the daily practice of mathematics).

But in any case, what Lean does is *compile the tactic proof into a proof term*, which becomes accessible via the `#print` command. 

We can then use that proof term to provide a proof without entering tactic mode, simply by copying the proof term generated via the `#print` command (it will appear in the Infoview* tab if you put the keyboard cursor on the same line as the `#print` command) and pasting it after the `:=` symbol.

We test this out below with the `my_brother_and_I_agree` proposition. 

Note that, in this case, Lean does not generates a `goal accomplished` message (this is only in tactic mode). If you use a proof term, the only way to know it worked is via the absence of an error message. -/

-- #print my_two_sentences_are_the_same

-- def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := eq.refl my_first_sentence

def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := eq.refl my_favourite_integer

/- ### **Exercise** 

Use a proof term to write a proof of `1 + 1 = 2`. 

Note that `eq.refl (1 + 1)` and ` eq.refl 2` work equally well and check that this is also the case for the definitions of the terms `my_two_sentences_are_the_same` and `my_brother_and_I_agree`.

At this stage, it might be instructive to try out `#check eq.refl 2` and `#check eq.refl (1 + 1)`. Or even `#check eq.refl my_favourite_integer` and `#check eq.refl my_first_sentence`. See below for the corresponding code and a remark on the content of `eq.refl 2`.

Try also `#check eq.refl` and `#check @eq.refl`. Using `@` should produce something better-looking. -/

def one_plus_one_eq_two_again : 1 + 1 = 2 := eq.refl (1 + 1)

/- The following command `#check eq.refl 2` returns `eq.refl 2 : 2 = 2`, which means that `eq.refl 2` is a term of type `2 = 2`. In other words, **`eq.refl 2` is a proof of the Proposition `2 = 2`.** This is crucial in understanding how *Lean* works.-/

#check eq.refl 2

-- #check eq.refl (1 + 1)
-- #check eq.refl my_favourite_integer
-- #check eq.refl my_first_sentence

-- #check eq.refl
-- #check @eq.refl

/- In the previous Exercise, the term which is being defined has been given a different name: it is still a term of type `1 + 1 = 2` but now it is called `one_plus_one_eq_two_again`. 

So we now have two terms of type `1 + 1 = 2`, namely `one_plus_one_eq_two` and `one_plus_one_eq_two_again`. We will now prove that they are equal, using the only tactic we have for now! -/

def the_two_proofs_we_gave_are_equal : one_plus_one_eq_two = one_plus_one_eq_two_again := by {refl}

/- To conclude this session, let us see an example of a case when we do not get what we might expect at all. If we write to write fractions naively, we see that the types of those terms is not what we think it is. -/

#check 42 / 21
#check 1 / 3
#check 0.5

#eval 42 / 21
#eval 1 / 3
#eval 0.5

#eval 1 / 2

/- The above fact comes from the *definition* of the operation `/`, which is not what we might expect. And since this is a definition, we can prove funny identities. To understand the following, note that 42 / 15 = 2.8 as decimal numbers. -/

#eval 42 / 15
#eval 2.8

def fun_fact_1 : 42 / 15 = 2 := eq.refl (42 / 15) 
def fun_fact_2 : 2.8 = 2 := eq.refl (42 / 15) 
def fun_fact_3 : 2.8 = 2.7 := eq.refl (42 /15) 

/- As a final remark, we point out that, in Lean, it is possible to introduce anonymous definitions, via the `example` command. This can be useful if it is a definition of a term that we do not plan to use again after introducing it and we do not want to waste a name on it. -/

example : 2.8 = 2.7 := by {refl}

/- Answers to some of the questions asked during the session

There were several questions about the result shown by the programme for basic computations in Lean.

For instance, why do we get `41 - 42 = 0` ? Or why is `31 / 10 * 52` not equal to `52 * 31 / 10` ?

The reason at the heart of both phenomena is the same: because the operations corresponding to the familiar pieces of notation `-` and `/` is not what we think they are.

That being said, the second phenomenon is more complex than the first one, as we shall see. -/

/- The following result is not what we expect. -/

#eval 41 - 42 

/- And indeed Lean considers that `41-42` is of type `ℕ`, while we think it should be of type `ℤ`. -/

#check 41 - 42

/- Now, for natural numbers, the result of the operation `n - m` is, **by definition**, equal to the what we think it is (namely, the unique `r` in `ℕ` such that `m + r = n`) *if* `n - m ≥ 0`, but to `0` if `n - m < 0`. Again, this is the definition of substraction as an operation on `ℕ`. -/

def A : ℕ := 41 - 42
#check A
#eval A

/- Now, in *integers*, the result should be different. Namely, the unique `r` such that `m + r = n` is now allowed to be negative.

We can achieve that by changing *only one parameter* in the previous definition (apart from the name of the term itself). Namely, we change `ℕ` to `ℤ`, which is accessible via `\Z` or `\int` (the type `ℤ` is also denoted `int`). -/

def B : ℤ := 41 - 42
#check B
#eval B

/- For the second question, first we check that the two results disagree, and that both are indeed considered to be *natural numbers* by Lean. -/

#eval 31 / 10 * 52
#eval 52 * 31 / 10

#check 31 / 10 * 52
#check 52 * 31 / 10

/- Then a first remark is that, by definition, if `p` and `q` are natural numbers, then Lean considers that `p / q` is the natural number (in particular, *not* the rational number) defined by the floor function applied to what *we* think the rational number `p / q` is (for instance `31 / 10` is `3` and not `3.1`, *by definition*).

A second remark is that `52 * 31 / 10` is interpreted by Lean as `(52 * 31) / 10`, which is `1612 / 10`, and the latter is equal to `161`, by definition of the operation `/` on `ℕ`. While `31 / 10 * 52 = 3 * 52 = 156`.

With these two remarks, we see that `(31 / 10) * 52` is equal to `52 * (31 / 10)` but *not* to `(52 * 31) / 10`. And quite obviously, perhaps, `31 / (10 * 52)` is again different. -/

#eval 31 / 10
#eval (31 / 10) * 52
#eval 31 / 10 * 52

#eval 52 * (31 / 10)

#eval 52 * 31 
#eval (52 * 31) / 10
#eval 52 * 31 / 10

#eval 31 / (10 * 52)

/- As a final remark, we point out that the command `#print` cannot be applied to numbers (but strings are OK). In particular, the command `#print` is not the same as outputting the result of a computation to the screen, like in other languages you may know). -/

-- #print 42
#print "Hello, world!"

/- Below, we define `m` to be equal to `42`. So `#print m` returns the definition of the term `m`, namely `def m : ℕ := 42`, which is what we had entered. -/

def m : ℕ := 42
#print m
