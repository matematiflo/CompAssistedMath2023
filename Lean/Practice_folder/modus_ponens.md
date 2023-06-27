
# ***Modus ponens***

Let us use tactic mode to write a proof of the rule of deductive reasoning known as *modus ponens*, which says that if we have a proof of proposition `P` and a proof of the implication `P → Q`, then we have a proof of the proposition `Q`.

```lean
def MP {P Q : Prop} (p : P) (f : P → Q) : Q :=
begin
  apply f,
  exact p,
end
```

The proof we give can be understood as follows. First, let us make it clear that `P` and `Q` are propositions, that we have a proof `p` of `P` and a proof `f` of `P → Q`, and that our goal is to prove `Q`.

Since by assumption we have a proof of the implication `P → Q`, it suffices to prove `P`. This is what the `apply` tactic enables us to do. More precisely, the term `f`, being of type `P → Q`, is a function from `P` to `Q`, so it sends a term of type `P` (i.e. a proof a `P`) to a term of type `Q`, i.e. a proof of `Q`.

Now, after the `apply` tactic, the goal is changed to `P`. And since, again by assumption, we have a proof of `P`, we can close the goal using the `exact` tactic.

Alternately, we can write the proof using just the `exact` tactic, because `f p` is the result of applying the function `f : P → Q` to the term `p`, which is of type `P`, so it is a term of type `Q`.

```lean
def MP_bis {P Q : Prop} (p : P) (f : P → Q) : Q :=
begin
  exact f p,
end
```

And in term mode, `MP` is defined as follows.

```lean
def MP_ter {P Q : Prop} (p : P) (f : P → Q) : Q := f p
```

In this example, we see three approaches to definitions in *Lean*:

* A concise term mode definition (`MP_ter`).
* A tactic mode definition that just adds the word `exact` in front of the term mode definition (`MP_bis`).
* A longer tactic mode definition, `MP`, that uses the `apply` tactic to change the goal before closing it.

The longer the proof, the more it becomes necessary to use the third approach (tactic mode). In that approach, *we work on the goal to reduce it to the assumptions*, and we close the reduced goal with the `exact` tactic.

We now check that `MP` is indeed a function that, in the presence of Propositions `P` and `Q`, sends a proof of the propositions `P` and `P → Q` to a proof of `Q`.

```lean
#check @MP
```

Here we use the `@` because `MP` has implicit arguments (namely `P` and `Q`). The result of `#check @MP` then looks as follows.

```lean
MP : ∀ {P Q : Prop}, P → (P → Q) → Q
```

It is instructive to check that the three definitions we have given are identical.

```lean
-- #print MP
-- #print MP_bis
-- #print MP_ter
```

Next, by using the command `variables`, we add to our context the Propositions `P` and `Q`, as well as a proof of `P` and a proof of the implication `P → Q`.  This is just for commodity here.

```lean
variables {P Q : Prop} (p : P) (f : P → Q)
```

And now, using the function MP and the variables `p` and `f`, we can give a proof of Proposition `Q`: we simply apply the *modus ponens* function to the proofs of the propositions `P` and `P → Q`. Note that `proof_of_Q` is a term of type `Q` and that we are *defining* it.

```lean
def proof_of_Q : Q := MP p f
```

Let us check that the term MP p f is indeed of type `Q`, i.e. that it is a proof of the Proposition `Q`.

```lean
#check MP p f
```

Alternately, we can write the following:

```lean
#check @MP P Q p f
```

The two terms `MP p f` and `@MP P Q p f` are in fact identical, but in the second notation we include the *implicit variables* `P` and `Q`. These implicit variables were declared with curly brackets `{ }` (see the definition of `MP`), as opposed to `p` and `f`, which were defined using round brackets `( )`.

We now give the tactic mode version of our proof of `Q`, using only the `exact` tactic.

```lean
def proof_of_Q_bis (p : P) (f : P → Q) : Q :=
begin
  exact MP p f,
end
```

Note that here, in order to use the variables `p` and `f` *in tactic mode*, we need to include them in the definition. However, we can check that the proof terms of `proof_of_Q` and `proof_of_Q_bis` are identical.

```lean
-- #print proof_of_Q
-- #print proof_of_Q_bis
```

To conclude, we give an alternate formulation for the definition of the *modus ponens*, where the variables `p : P` and `f : P → Q` do not appear explicitly, making the definition more compact. The tactic proof, however, is longer, as we must now introduce the variables ourselves, using the `intro` tactic.

```lean
def MP_no_var {P Q : Prop}: P → (P → Q) → Q :=
begin
  intro p,
  intro f,
  apply f,
  exact p,
end
```

Equivalently, we can write `P ∧ (P → Q) → Q`, instead of `P → (P → Q) → Q`. The symbol `∧` is read *and* and can be obtained by typing in the command `\and`.

In that case, the proof is even longer, and we wust apply the `cases` tactic in order to replace the hypothesis `h : P ∧ (P → Q)` by the two hypotheses `p : P` and `f : (P → Q)`.

The names `h` and `f` are chosen arbitrarily. If we simply write `cases h` instead of `cases h with p f`, *Lean* will assign names automatically.

```lean
def MP_no_var_bis {P Q : Prop}: P ∧ (P → Q) → Q :=
begin
  intro h,
  cases h with p f,
  apply f,
  exact p,
end
```

It is instructive to see that the proof term corresponding to `MP_no_var` is quite simple (the `λ` term means that we are defining a function), while the one corresponding to `MP_no_var_bis` is more involved (because of the `cases` tactic).

```lean
-- #print MP_no_var
-- #print MP_no_var_bis
```

---
