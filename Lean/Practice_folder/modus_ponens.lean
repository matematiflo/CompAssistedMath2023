
/- # ***Modus ponens*** -/

/- Here is a definition of a term called `MP`. 

It is a function that sends `hP` and `hPQ` to `hPQ hP`. The latter expression makes sense because `hPQ` is a function from `P` to `Q` and `hP` is a term of type `P`, so `hPQ hP` is a term of type `Q`.

In term mode, `MP` is defined as follows.

def MP {P Q : Prop} (hP : P) (hPQ : P → Q) : Q := hPQ hP`

In tactic mode, we need to add the `exact` keyword in front of that definition to close the goal. Alternately, one can first use the `apply` tactic, which changes the goal to `P`, and then use close the goal with `exact hP`. Note that, in the expression `exact hPQ hP`, what appears after the `exact` is precisely the term mode definition of `MP`.

In this example, we see:

* A concise term mode definition.
* A tactic mode definition that just adds the word `exact` in front of the term mode definition.
* A longer tactic mode definition that uses the `apply` tactic as well to change the goal before closing it.

The longer our proofs become, the more necessary it will be to use the third approach. In that approach, *we work on the goal to reduce it to the assumptions, and we close the reduced goal with the `exact` tactic.
-/

def MP {P Q : Prop} (hP : P) (hPQ : P → Q) : Q := 
-- hPQ hP
begin
  -- apply hPQ,
  -- exact hP,
  exact hPQ hP,
end

/- We now check that `MP` is indeed a function that, in the presence of Propositions `P` and `Q`, sends a proof of the propositions `P` and `P → Q` to a proof of `Q`. 

Here we use the `@` because `MP` has implicit arguments (namely `P` and `Q`). See below for more on this. -/

#check @MP

/- This is the result of `#check @MP`:

MP : ∀ {P Q : Prop}, P → (P → Q) → Q

-/

variables {P Q : Prop} (hP : P) (hPQ : P → Q)

/- By using the command `variables`, we have just added to our context the Propositions `P` and `Q`, as well as a proof of `P` and a proof of the implication `P → Q`.  Using the function MP and the variables `hP` and `hPQ`, we can *define a proof* of Proposition `Q`: we simply apply the *modus ponens* function to the proofs of the propositions `P` and `P → Q`. -/

def proof_of_Q : Q := MP hP hPQ

/- The following terms are both of type `Q`, i.e. proofs of the Proposition `Q`. In fact, it is the same term, namely `MP hP hPQ`, but in the first notation we include the *implicit variables* `P` and `Q`. These implicit variables were declared with curly brackets `{ }` (see the definition of `MP`), as opposed to `hP` and `hPQ`, which were defined using round brackets `( )`. -/

#check @MP P Q hP hPQ
#check MP hP hPQ

/- The tactic proof of `Q` that we give below uses the `exact` tactic.

Note that here, in order to use the variables `hP` and `hPQ` *in tactic mode*, we need to include them in the definition. -/

def proof_of_Q_bis (hP : P) (hPQ : P → Q) : Q :=
begin
  exact MP hP hPQ,
end

/- Note that the proof terms of `proof_of_Q` and `proof_of_Q_bis` are identical. -/

-- #print proof_of_Q
-- #print proof_of_Q_bis

/-
---
-/
