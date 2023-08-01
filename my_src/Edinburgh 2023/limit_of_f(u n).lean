import data.real.basic
import tactic

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N : ℕ, ∀ n > N, |u n - l| < ε

def continuous_function_at (f : ℝ → ℝ) (x0 : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x0| < δ → |f(x) - f(x0)| < ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x0 : ℝ )
(hu : sequence_tendsto u x0) 
(hf : continuous_function_at f x0) :
sequence_tendsto (f ∘ u) (f x0) := 

begin
show (∀ ε > 0, ∃ N : ℕ, ∀ n > N, |f(u n) - f(x0)| < ε),
assume (ε ε_pos),
have h1 : (∃ δ>0, ∀ x : ℝ, |x - x0| < δ → |f x - f x0| < ε) := 
  by {apply hf, exact ε_pos},
rcases h1 with ⟨δ, δ_pos, h2⟩,
have h3 : (∃ N : ℕ, ∀ n> N, |u n - x0| < δ) := 
  by {apply hu, exact δ_pos},
rcases h3 with ⟨N, h4⟩,
use N,
intros n n_large,
apply h2,
apply h4,
exact n_large,
end

lemma limit_f_circ_u (f : ℝ → ℝ) (u : ℕ → ℝ) (x0 : ℝ) :
(sequence_tendsto u x0) ∧ (continuous_function_at f x0) → 
sequence_tendsto (f ∘ u) (f x0) := 

begin
intro h,
cases h with hu hf,
show (∀ ε > 0, ∃ N : ℕ, ∀ n > N, |f(u n) - f(x0)| < ε),
assume (ε ε_pos),
have h1 : (∃ δ>0, ∀ x : ℝ, |x - x0| < δ → |f x - f x0| < ε) := 
  by {apply hf, exact ε_pos},
rcases h1 with ⟨δ, δ_pos, h2⟩,
have h3 : (∃ N : ℕ, ∀ n> N, |u n - x0| < δ) := 
  by {apply hu, exact δ_pos},
rcases h3 with ⟨N, h4⟩,
use N,
intros n n_large,
apply h2,
apply h4,
exact n_large,
end

-- The following writes the proof of limit_f_circ_u as a proof term
-- #print limit_f_circ_u

def g ( x : ℝ ) := 1+x

noncomputable def v (n : ℕ) := (1/↑n : ℝ)

#check (g∘v)
example : sequence_tendsto (g∘v) (g 0) :=

--  perhaps one would like instead the more explicit option
-- 'lemma limit_g_circ_v : sequence_tendsto (g∘v) 1 := ' ?
-- (observe that g(0) = 1 in our example)

begin
apply limit_f_circ_u g v 0,
split,
-- show (∀ ε>0, ∃ N : ℕ, ∀ n > N, |v n - 0| < ε),
-- simp,
-- OR
simp [sequence_tendsto],
assume (ε ε_pos),
-- let N := nat.floor (1/ε),
-- use N,
use nat.floor (1/ε),
intro n,
intro h,
rw v,
simp,
-- change ⌊1 / ε⌋₊ < n at h,
rw abs_eq_self.2,
rw inv_lt,
rw nat.floor_lt at h,
rw inv_eq_one_div,
exact h,
apply norm_num.nonneg_pos,
rw ← inv_eq_one_div,
apply inv_pos.2,
exact ε_pos,
-- change N < n at h,
simp,
linarith,
exact ε_pos,
apply inv_nonneg.2,
simp,
-- show (∀ ε>0, ∃ δ>0, ∀ x : ℝ , |x - 0| < δ → |g x - g 0| < ε),
simp [continuous_function_at],
intros ε ε_pos,
rw g,
simp,
let δ := ε,
use δ,
split,
exact ε_pos,
intro x,
intro x_small,
rw g,
simp,
exact x_small,
end

/- Kevin Buzzard's solution:
simp,
-- ⊢ |(↑n)⁻¹| < ε
-- I wouldn't have defined N, it's just getting in the way
change ⌊1 / ε⌋₊ < n at h,
-- know |n⁻¹|=n⁻¹
rw abs_eq_self.2, -- I guessed the name
-- x⁻¹ < y ↔ y⁻¹ < x
rw inv_lt, -- I guessed the name
-- now work on h; I guessed the name of the lemma
rw nat.floor_lt at h,
-- change ε⁻¹ to 1/ε ; I guessed the name
rw inv_eq_one_div,
exact h,
-- now we're done apart from a bunch of non-negativity hypotheses
all_goals {try {positivity}},
-- only one failed to die, namely 0 < ↑n; do this manually
norm_cast,
refine lt_of_le_of_lt _ h,
exact zero_le ⌊1 / ε⌋₊, -- I used library_search for this one
sorry, -- continuity goal remains
-/

example : sequence_tendsto (g∘v) (g 0) :=

begin
apply limit_f_circ_u g v 0,
split,
simp [sequence_tendsto],
assume (ε ε_pos),
-- let N := nat.floor (1/ε),
-- use N,
use nat.floor (1/ε),
intro n,
intro h,
rw v,
simp,
change ⌊1 / ε⌋₊ < n at h,
-- know |n⁻¹|=n⁻¹
rw abs_eq_self.2, -- I guessed the name
-- x⁻¹ < y ↔ y⁻¹ < x
rw inv_lt, -- I guessed the name
-- now work on h; I guessed the name of the lemma
rw nat.floor_lt at h,
-- change ε⁻¹ to 1/ε ; I guessed the name
rw inv_eq_one_div,
exact h,
-- now we're done apart from a bunch of non-negativity hypotheses
all_goals {try {positivity}},
-- only one failed to die, namely 0 < ↑n; do this manually
norm_cast,
refine lt_of_le_of_lt _ h,
exact zero_le ⌊1 / ε⌋₊, -- I used library_search for this one
sorry, -- continuity goal remains
end

example ( a b : ℝ ) : ( (a>0) ∧ (b>0) ∧ (1/a ≤ b) → (1/b) ≤ a)
:=
begin
intro h,
rcases h with ⟨a_pos, b_pos, ineq⟩,
ring_nf at ineq,
ring_nf,
apply inv_le_of_inv_le,
exact a_pos,
exact ineq,
end

example ( a b : ℝ ) : ( (a>0) ∧ (b>0) ∧ (1/a ≤ b) → (1/b) ≤ a) 
:=
begin
simp,
intros ha hb ineq,
apply inv_le_of_inv_le,
exact ha,
exact ineq,
end

example : 2 <3
:=
begin
--simp,
linarith,
end

example ( a b : ℝ ) (a_pos : a > 0) (b_pos : b > 0) 
(ineq : 1/a ≤ b) : (1/b) ≤ a
:=
begin
simp,
apply inv_le_of_inv_le,
exact a_pos,
simp at ineq,
exact ineq,
end

example ( A B : Prop ) : A ∧ ¬A → B
:=
begin
intro h,
cases h with a not_A,
exfalso,
-- apply not_A,
-- exact a,
exact not_A a,
end

example ( A B : Prop ) : A ∧ ¬A → B
:=
begin
intro h,
cases h with a na,
have h1 : ¬ A ∨ B,
by { left, exact na },
rw ← or_false B,
cases h1 with nna b,
right,
exact nna a,
left,
exact b,
end

example ( B : Prop ) : false → B
:=
begin
contrapose,
intro h,
exact not_false,
end

example ( B : Prop ) : B ↔ (B ∨ false)
:=
begin
split,
intro b,
left,
exact b,
intro h,
cases h with b f,
exact b,
have h : false → B,
by { contrapose, intro h, exact not_false },
exact h f,
end

example ( A B : Prop ) : A ∧ ¬A → B
:=
begin
intro h,
cases h with a na,
rw ← or_false B, 
right,
exact na a,
end

-- modus ponens
example ( P Q : Prop ) : P ∧ ( P → Q ) → Q
:=
begin
intro h,
cases h with hp hpq,
exact hpq hp,
end

-- syllogisme disjonctif? revoir aussi le modus tollens...
example ( P Q : Prop ) : P ∧ ( ¬ P ∨ Q ) → Q
:=
begin
intro h,
cases h,
cases h_right,
rw ← or_false Q, 
right,
exact h_right h_left,
exact h_right,
end

example ( P Q : Prop ) : ( P → Q ) ↔ ( ¬P ∨ Q )
:=
begin
split,
intro hpq,
by_cases P,
right,
exact hpq h,
left,
exact h,
intro nP_or_Q,
intro p,
rw ← or_false Q, 
cases nP_or_Q,
right,
exact nP_or_Q p,
left,
exact nP_or_Q,
end

-- I bet this is what exfalso does?
-- The point is that the contrapose tactic is an equivalence, of which one implication uses the LEM (see NNG Prop and Adv. Prop Worlds)
example ( A B : Prop) : ¬A → ( A → B)
:=
begin
intro H,
intro a,
-- have h : false → B,
-- by { contrapose, intro h, exact not_false },
-- exact h (H a),
exfalso,
exact H a,
end

-- without the LEM, one can only show that 
example ( A B : Prop) : ¬A → ( A → B ∨ false)
:=
begin
intro H,
intro a,
right,
exact H a,
end

example ( A B : Prop) : ¬A → ( A → B)
:=
begin
intro H,
intro a,
have h : B ∨ false,
by { right, exact H a },
cases h,
exact h,
have h1 : false → B,
by { contrapose, intro h, exact not_false },
exact h1 h,
end

example ( P : Prop ) : ¬¬P ↔ P
:=
begin
split,
intro nnp,
by_cases P,
exact h,
-- have F : false,
-- exact nnp h,
exfalso,
exact nnp h,
-- intro nnp,
-- by_cases P,
-- exact h,
-- have h1 : false → P,
-- by { contrapose, intro hp, exact not_false },
-- apply h1,
-- apply nnp,
-- exact h,
intro p,
intro h,
exact h p,
end

example ( P : Prop ) : (¬¬P → P) ↔ ( P ∨ ¬P )
:=
begin
split,
intro h,
by_cases h2 : ¬P, --bof...
right,
exact h2,
left,
exact h h2,
intro lem,
intro nnp,
cases lem with lem1 lem2,
exact lem1,
exfalso,
exact nnp lem2,
end

example ( P : Prop ) : ¬¬P → P
:=
begin
intro h,
by_cases h1 : P,
exact h1,
exfalso,
apply h,
exact h1,
end

example ( P : Prop ) : ¬¬P ↔ P
:=
begin
split,
intro h,
by_cases h1 : P,
exact h1,
exfalso,
apply h,
exact h1,
intro p,∨ 
intro np,
exact np p,
end

example ( A B : Prop ) : ¬A → ( A →B ) 
:=
begin
intro h,
intro a,
exfalso,
exact h a,
end

example ( P Q : Prop ) : ( ( ¬Q → ¬P ) → ( P → Q ) )
:=
begin
intro h,
intro p,
by_cases q : Q,
exact q,
have h1 : ¬P, by {exact h q},
have h3 : P → Q, by {intro p1, exfalso, exact h1 p1},
exact h3 p,
end

example ( P : Prop ) :  P ∨ false → P
:=
begin
intro h,
cases h with p F,
exact p,
exfalso,
exact F,
end