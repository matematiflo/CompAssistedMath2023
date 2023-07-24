import tactic
import data.nat.prime
import data.nat.basic
import algebra.associated
import data.nat.units
open finset
open multiset
 



namespace project_new
  
  lemma greater_equal_not_one {n : ℕ}: 2 ≤ n → ¬ (n = 1) :=
    begin
      sorry,
    end 

  lemma not_one {n : ℕ}: ¬ n = 1 → (n = 0 ∨ 2≤n):=
    sorry


  lemma exists_factor {n : ℕ}: ( 2 ≤ n ∧ ¬ nat.prime n) -> ∃ a b : ℕ, (a*b=n ∧ 2≤a ∧ 2≤b ∧ a<n ∧ b<n):=
  begin
  -- introduce assumption
  intro ass,

  -- split at ∧-Operator
  cases ass with ass1 ass2,

  -- In ℕ it holds: p irreducible ↔ p prime
  rw[<-irreducible_iff_nat_prime] at ass2,

  -- Change to definition of irreducible element
  rw[irreducible_iff] at ass2,

  -- negate whole definition
  push_neg at ass2,
  
  -- is_unit ℕ n ↔ n = 1
  rw[nat.is_unit_iff] at ass2,

  -- Extract negation of irreducibility for our n
  have h : ∃(a b : ℕ), n = a * b ∧ ¬is_unit a ∧ ¬is_unit b, from ass2 (greater_equal_not_one ass1),

  -- Get two elements w,z that are not equal to 1 and fulfill n=w*z
  rcases h with ⟨w, z, ass_wz⟩,

  -- Extract 3 assumptions for w and z
  cases ass_wz with ass_wz1 ass_wz23,
  cases ass_wz23 with ass_wz2 ass_wz3,

  -- rewrite is_unit n as n=1
  rw[nat.is_unit_iff] at ass_wz2 ass_wz3,

  have ass_wz2_1 : (w = 0) ∨ (2 ≤ w), from not_one ass_wz2,
  have ass_wz3_1 : (z = 0) ∨ (2 ≤ z), from not_one ass_wz3,

  have statement_1 : (w*z=n), from eq.symm ass_wz1,
  -- w = 0, z = 0 not possible, because otherwise n = 0
  have statement_2 : (2 ≤ w), from sorry,
  have statement_3 : (2 ≤ z), from sorry,

  have statement_4 : (w < n), from sorry,
  have statement_5 : (z < n), from sorry,
  
  -- combine statements and introduce existential quantifier
  have statement_prod : ((w*z=n ∧ 2≤w ∧ 2≤z ∧ w<n ∧ z<n)), from ⟨statement_1,statement_2, statement_3, statement_4, statement_5⟩,
  have statement : (∃ w z : ℕ, (w*z=n ∧ 2≤w ∧ 2≤z ∧ w<n ∧ z<n)), from exists.intro (w) (exists.intro (z) (statement_prod)),
  assumption,
  end

def empt : multiset ℕ := 0
variable p : ℕ
def isp : Prop := prime p
#check multiset.map_singleton (isp) (p) 


/--evtl. nützliche Funktionen
multiset.card_singleton
multiset.map_singleton
multiset.card_eq_one.mp
--/


lemma prime_is_fact (p : ℕ)(h₁: nat.prime p) : ∃ (s : multiset ℕ), s.prod=p ∧ ∀ x ∈ s, nat.prime x :=
begin
    have g1 : multiset.prod {p} = p, from multiset.prod_singleton p,
    have g2 : multiset.card {p} = 1, from multiset.card_singleton p,
    have g3 : ∃ a : ℕ, {p} = {a}, from multiset.card_eq_one.mp g2,
    -- get element a with {p} = {a}
    cases g3 with el1 statement1,
    -- goal will be to prove the statement for our multiset {a}
    use {el1},
    -- split conjunctive statement
    split,
    --prove first goal {a}.prod = p
    rw[<-g1, statement1],
    -- introduce variable + statement 2
    intros el2 statement2,
    -- if {p} = {el1} singleton multisets => p = el1
    rw multiset.singleton_inj at statement1,
    -- same for statement2
    rw multiset.mem_singleton at statement2,
    -- el2 = p..so change goal to nat.prime p
    rw [<-statement2] at statement1,
    rw [<-statement1],
    exact h₁,
end


lemma prod_solution (a b: multiset ℕ):a.prod*b.prod=(a+b).prod:=
eq.symm(multiset.prod_add a b)

theorem prime_fact' (n : ℕ)(h₁ : 2 ≤ n) : ∃ (s : multiset ℕ), s.prod=n ∧ ∀ x ∈ s, nat.prime x :=
begin
    -- either n is prime (1) or not prime (2)
    by_cases np : n.prime,
    -- (1) proven in Lemma prime_is_fact
    use [prime_is_fact n np],
    -- (2) use strong induction
    induction n using nat.strong_induction_on with n ih,
    -- with Lemma exists_factor, we get n not prime as a product of two numbers
    have factors: ∃ a b : ℕ, (a*b=n ∧ 2≤a ∧ 2≤b ∧ a<n ∧ b<n), from exists_factor ⟨h₁, np⟩,
    -- get two factors and the statements from exists_factor
    rcases factors with ⟨el1,el2,stat⟩,
    -- split conjunction in statement
    rcases stat with ⟨ass1,ass2,ass3,ass4,ass5⟩,
      by_cases el1_p : el1.prime,
      {by_cases el2_p : el2.prime,
        --case el1 prime ∧ el2 prime
        {,},
        --case el1 prime ∧ el2 ¬ prime
        {sorry,},},
      
      {by_cases el2_p : el2.prime,
        --case el1 ¬prime ∧ el2 prime
        {sorry,},
        --case el1 ¬prime ∧ el2 ¬prime
        {sorry,},},
    --use[prod_solution (ih el1) (ih el2), 
end



end project_new