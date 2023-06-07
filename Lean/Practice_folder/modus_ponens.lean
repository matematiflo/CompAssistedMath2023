
/- #*Modus ponens* -/

def MP {P Q : Prop} (hP : P) (hPQ : P → Q) : Q :=
begin
  apply hPQ,
  exact hP,
end

/- MP appears as a function that, given propositions P and Q, sends a proof of the propositions P and (P → Q) to a proof of Q. -/

#check @MP

/-
MP : ∀ {P Q : Prop}, P → (P → Q) → Q
-/

variables {P Q : Prop} (hP : P) (hPQ : P → Q)

/- A proof that, in the context defined  by the functions MP and the variables P, Q, hP and hPQ, the Proposition Q is true: we simply apply the *modus ponens* function to the proofs of the propositions P and (P → Q). -/

def In_our_context_Q_is_true : Q := MP hP hPQ

#check @MP P Q hP hPQ
#check MP hP hPQ

/- The tactic proof that Q is true in our context actually repeats the steps of the def of MP. 

Note that in order to use the variable hP and hQ in tactic mode, we need to inclue them in the so-called local context as well.-/

include hP hPQ

def In_our_context_Q_is_true_bis : Q :=
begin
    apply hPQ,
    exact hP,
end
