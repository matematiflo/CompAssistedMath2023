
/- # ***Modus ponens*** -/

def MP {P Q : Prop} (hP : P) (hPQ : P → Q) : Q :=
begin
  apply hPQ,
  exact hP,
end

/- `MP` appears as a function that, given Propositions `P` and `Q`, sends a proof of the propositions `P` and `P → Q` to a proof of `Q`. -/

#check @MP

/- This is the results of `#check MP`
MP : ∀ {P Q : Prop}, P → (P → Q) → Q
-/

variables {P Q : Prop} (hP : P) (hPQ : P → Q)

/- We have just added to our context the Propositions `P` and `Q`, as well as a proof of `P` and a proof of the implication `P → Q`.  Using the function MP and the variables `hP` and `hPQ`, we can *define a proof* of Proposition `Q`: we simply apply the *modus ponens* function to the proofs of the propositions `P` and `P → Q`. -/

def proof_of_Q : Q := MP hP hPQ

/- The following terms are both of type `Q`, i.e. proofs of the Proposition `Q`. In fact, it is the same term, namely `MP hP hPQ`, but in the first notation we include the *implicit variables* `P` and `Q`. These implicit variables were declared with curly brackets `{ }` (see the definition of `MP`), as opposed to `hP` and `hPQ`, which were defined using round brackets `( )`. -/

#check @MP P Q hP hPQ
#check MP hP hPQ

/- The tactic proof that `Q` is true in our context uses the `exact` tactic.

Note that here, in order to use the variables `hP` and `hPQ` *in tactic mode*, we need to include them in the local context.-/

def proof_of_Q_bis (hP : P) (hPQ : P → Q) : Q :=
begin
  exact MP hP hPQ,
end

/- At the end of the day, the two proof terms are in fact identical. -/

#print proof_of_Q
#print proof_of_Q_bis
