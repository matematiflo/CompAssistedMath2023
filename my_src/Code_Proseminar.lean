import tactic
import data.nat.prime
import data.nat.basic
import algebra.field.basic
import data.nat.modeq
import data.nat.choose.sum
import tactic
import data.list.big_operators.lemmas
import data.nat.choose.dvd

def L1 : list ℕ := [1,2,3]
def L2 : list ℤ := [-1,-2,-2]

#eval L2 
-- #eval L2[1]

def A : list (list ℤ) := [[1,2],[-2,3]]

#check A

#eval A

-- #eval A[1]
-- #eval A[1][0]

def B : list (list ℤ) := [[1,2],[-2,3]]

#check B

open finset
open multiset

open nat.prime

theorem fermat (p : ℕ) [fact : nat.prime p] (a : ℕ) : (a^p -a) % p = 0 := 
begin
  induction a with d hd,
  { sorry },
  { rw nat.succ_eq_add_one,
    rw add_pow,
    have aux : (∀ x ∈ finset.range (p+1),  ¬ ( (x = 0) ∨ (x = p) ) → p.choose x % p = 0) := sorry,
    simp [aux],
    have bin : ∀ x : ℕ, ¬(x = 0 ∨ x = p) → p.choose x % p = 0 := 
    begin
      intro x,
      intro hx,
      push_neg at hx,
      have hx1 := hx.1,
      have hx2 := hx.2,
      have aux2 : p ∣ (p.choose x) :=
      begin
        apply dvd_choose_self,
        exact fact,
        exact hx1,
        sorry,
      end,
      sorry,
    end,
    sorry,
  }


end

namespace project
--- Die Definition hab ich irgendwo geklaut

-- Proof of Lemma for iff-statement in exists.factor
lemma dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

lemma neg_forall {α : Type*} {p : α -> Prop} : (∃ x : α, p x) ↔ ¬ (∀ x : α, ¬ p x ) := 
  iff.intro
    (assume g : ∃ x, p x, show ¬ (∀ x, ¬ p x),
    from by_contradiction
        (assume h : ¬ (¬ ∀ x, ¬ p x), show false, 
         from exists.elim g (assume w : α, assume gw : p w , dne h w gw)) 
    )
    (sorry)


lemma neg_exists {α : Type*} {p : α -> Prop}: ¬ (∃ x : α, p x) ↔ (∀x : α, ¬ p x)  := 
  iff.intro
    (assume g : ¬ ∃ x, p x,
     show ∀x, ¬ p x, from by_contradiction
       (assume h : ¬ ∀x, ¬ p x, show false,
        from g (neg_forall.2 h))
    )
    (sorry)

lemma takeneg {x : ℕ × ℕ} {n : ℕ} : ¬ (x.1*x.2=n ∧ 2≤x.1 ∧ 2≤x.2 ∧ x.1<n ∧ x.2<n) ↔ (¬(x.1*x.2 = n) ∨ ¬(2≤x.1) ∨ ¬(2≤x.2) ∨ ¬(x.1<n) ∨ ¬(x.2<n)) :=
  begin
    rw [<- not_and_distrib.symm, <- not_and_distrib.symm,<- not_and_distrib.symm,<- not_and_distrib.symm],
  end

lemma alltakeneg {n : ℕ} : (∀ x : ℕ × ℕ , ¬ (x.1*x.2=n ∧ 2≤x.1 ∧ 2≤x.2 ∧ x.1<n ∧ x.2<n)) ↔ ∀ x : ℕ × ℕ , (¬(x.1*x.2 = n) ∨ ¬(2≤x.1) ∨ ¬(2≤x.2) ∨ ¬(x.1<n) ∨ ¬(x.2<n)) :=
  iff.intro
    (assume g : (∀ x : ℕ × ℕ , ¬ (x.1*x.2=n ∧ 2≤x.1 ∧ 2≤x.2 ∧ x.1<n ∧ x.2<n)), assume x : ℕ × ℕ,
      show (¬(x.1*x.2 = n) ∨ ¬(2≤x.1) ∨ ¬(2≤x.2) ∨ ¬(x.1<n) ∨ ¬(x.2<n)) ,
      from takeneg.mp (g (x))
    )
    (sorry)

def is_well_ordered (T : Type) [linear_ordered_field T]

-- Lemma imp_prime





-- Ende der Hilfssätze



-- Tatsächlicher Beweis
def prime (p : ℕ) := 2 ≤ p ∧ ∀ d ∣ p, d = 1 ∨ d = p

lemma umformen {n : ℕ}: ¬ (∃ x : ℕ × ℕ , x.1*x.2=n ∧ 2≤x.1 ∧ 2≤x.2 ∧ x.1<n ∧ x.2<n) ↔ ∀ x : ℕ × ℕ, (¬(x.1*x.2 = n) ∨ ¬(2≤x.1) ∨ ¬(2≤x.2) ∨ ¬(x.1<n) ∨ ¬(x.2<n)) :=
  begin
    rw [neg_exists, alltakeneg],
  end

lemma exists_factor {n : ℕ}: ( 2 ≤ n ∧ ¬ prime n) -> ∃ x : ℕ × ℕ, (x.1*x.2=n ∧ 2≤x.1 ∧ 2≤x.2 ∧ x.1<n ∧ x.2<n):=
begin
 intro g,
 cases g with g1 g2,
 rw [prime] at g2,
 push_neg at g2,
 let g3 := g2 g1,
 rcases g3 with ⟨d, hd⟩,
 let hd1 := hd.1,
 let hd2 :=hd.2.1,
 let hd3 := hd.2.2,
 sorry,
end
  
  /- assume g : 2 ≤ n ∧ ¬ prime n,
  show ∃ x : ℕ × ℕ, (x.1*x.2=n ∧ 2≤x.1 ∧ 2≤x.2 ∧ x.1<n ∧ x.2<n), from by_contradiction       
        
        (assume notass : ¬ (∃ x : ℕ × ℕ, (x.1*x.2=n ∧ 2≤x.1 ∧ 2≤x.2 ∧ x.1<n ∧ x.2<n)),-- from umformen.mpr neg_notass
         have neg_notass : ∀ x : ℕ × ℕ, (¬(x.1*x.2 = n) ∨ ¬(2≤x.1) ∨ ¬(2≤x.2) ∨ ¬(x.1<n) ∨ ¬(x.2<n)), from umformen.mp notass,
         assume z : ℕ × ℕ, 
         show false, from or.elim (umformen.mp (notass) z)  
            (assume dec1 : ¬(z.1*z.2 = n),
             have gst : 2 ≤ n, from g.left,
             have gnp : ¬ prime n, from g.right,
             sorry)

            (assume dec_rec1 : ¬(2≤z.1) ∨ ¬(2≤z.2) ∨ ¬(z.1<n) ∨ ¬(z.2<n), show false,
              from or.elim dec_rec1
                  (assume dec2 : ¬(2≤z.1), sorry)
                  
                  (assume dec_rec2 : ¬(2≤z.2) ∨ ¬(z.1<n) ∨ ¬(z.2<n), show false,
                   from or.elim dec_rec2
                    (assume dec3 : ¬(2≤z.2), sorry)
                    
                    (assume dec_rec3 : ¬(z.1<n) ∨ ¬(z.2<n), show false,
                     from or.elim dec_rec3
                      (assume dec4 : ¬(z.1<n), sorry)
                      (assume dec5 : ¬(z.2<n), sorry))
        )
  )
) -/

lemma simple_prod (p : ℕ): ([p].prod = p) :=
  begin 
   rw[list.prod], simp,
  end


lemma prime_is_fact (p : ℕ)(h₁: prime p) : ∃ (s : multiset ℕ), s.prod=p ∧ ∀ x ∈ s, prime x :=
  have s : multiset ℕ, from [p], 
  --have h1 : [p].prod = p, from simple_prod p,
  have h1 : s.prod = p, from sorry,
  have h2 : (∀ x ∈ s, prime x), from sorry,
  have h :  s.prod=p ∧ ∀ x ∈ s, prime x, from and.intro h1 h2,
  show ∃ (s : multiset ℕ), s.prod=p ∧ ∀ x ∈ s, prime x, from exists.intro (s) (h)


lemma prod_solution (a b: multiset ℕ)(p=a.prod)(q=b.prod):p*q=(a+b).prod:=
begin
    sorry,
end

theorem prime_fact' (n : ℕ)(h₁ : n ≥ 2) : ∃ (s : multiset ℕ), s.prod=n ∧ ∀ x ∈ s, prime x :=
begin
  sorry,
end

-- Ende tatsächlicher Beweis

end project