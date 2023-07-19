# Natural Number Game - Inequality World 

**Authors:** Leon Burgard, Karl Schamel, Seminar: Computer assisted mathematics by Florent Schaffhauser, Summer Semester 2023

The last world of the Natural Number Game is about inequalities, so in the first levels you only get to know a little bit how the ≤ sign is implemented in lean and to get used with it.
The main goal in this World is to proof that for all naturals a and b, a &lt b⟺succ(a)≤b.

## Level 1

If a and b are naturals, a ≤ b is defined to mean ∃ (c : mynat), b = a + c. In the beginning the expression a ≤ b seems to be hard to work with, so with the command ``rw le_iff_exists_add`` you can rewrite this expression to the it-exists-expression.

The second thing you learned in this level is the ``use``-tactic which changes an less-equal-expression to an equal-expression with adding a natural number.

```lean
-- If x is a natural number, then x≤1+x

lemma one_add_le_self (x : mynat) : x ≤ 1 + x :=
begin
rw le_iff_exists_add,
use 1,
rw add_comm,
end
```


## Level 2

In the second level you proof that the less-equal relation is reflexive. After the first level, this one is straight foreward because it uses the same tactics as the first level.

```lean
-- The ≤ relation is reflexive. In other words, if x is a natural number, then x≤x

lemma le_refl (x : mynat) : x ≤ x :=
begin
rw le_iff_exists_add,
use 0,
rw add_zero,
refl,
end
```


## Level 3

It is well known how to apply a tactic to an arbitrary hypothesis but here you learn to apply this tactic to an hypothesis as well as the goal itself using ``at h ⊢``.

```lean
-- For all naturals a, b, if a≤b then a≤succ(b)
theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) :=
 
begin
intro h,
rw le_iff_exists_add at h ⊢,
cases h with c hc,
rw succ_eq_add_one,
use (c+1),
rw hc,
refl,
end
```

It is important to note that you do not need to use ``rw le_iff_exists_add`` and it works as well without it. So in the following documentation we won´t use this command anymore.


## Level 4

```lean
-- For all naturals a, 0≤a
lemma zero_le (a : mynat) : 0 ≤ a :=
 
begin
use a,
rw zero_add,
refl,
end
```


## Level 5

```lean
-- ≤ is transitive. In other words, if a≤b and b≤c then a≤c
theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
 
begin
cases hab,
cases hbc,
rw hbc_h,
rw hab_h,
use hab_w + hbc_w,
rw add_assoc a hab_w hbc_w,
refl,
end
```

## Level 6

```lean
-- ≤ is antisymmetric. In other words, if a≤b and b≤a then a=b
theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
 
begin
cases hab,
cases hba,
rw hba_h at hab_h,
symmetry at hab_h,
rw add_assoc at hab_h,
have h1 := eq_zero_of_add_right_eq_self hab_h,
have h2 := add_right_eq_zero h1,
rw h2 at hba_h,
rw add_zero at hba_h,
exact hba_h,
end
```

## Level 7

```lean
-- For all naturals a, if a≤0 then a=0
lemma le_zero (a : mynat) (h : a ≤ 0) : a = 0 :=
 
begin
cases h with k1 h1,
symmetry at h1,
have h2 := add_right_eq_zero h1,
exact h2,
end
```

## Level 8

```lean
-- For all naturals a and b, if a≤b, then succ(a)≤succ(b)
lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b :=
 
begin
cases h with k h,
use k,
rw h,
rw succ_add,
refl,
end
```

## Level 9

This level is a very typical example of a lean proof because as you can see it is not a hard proof where you need to use difficult tactics, you just have to break it down to very small steps. 
An interesting thing about this proof is that it starts with the ``revert`` tactic which is the opposite of the ``intro`` tactic.

```lean
-- For all naturals a and b, either a≤b or b≤a
theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
 
begin
revert a,
induction b with d ih,
intro a,
right,
apply zero_le,
 
intro a,
cases a with k h,
left,
apply zero_le,
 
cases ih k,
left,
apply succ_le_succ,
exact h,
right,
apply succ_le_succ,
exact h,
end
```

## Level 10

```lean
-- For all naturals a, a≤succ(a).
lemma le_succ_self (a : mynat) : a ≤ succ a :=
 
begin
rw succ_eq_add_one,
use 1,
refl,
end
```

The game askes in this level if you can find a two-line solution. To do so you can use the ``ring`` tactic which is an expanded version of the ``refl`` tactic and clears associativity and commutativity by itselfs.

```lean
lemma le_succ_self (a : mynat) : a ≤ succ a :=
 
begin
use 1,
ring,
end
```

## Level 11

```lean
-- For all naturals a and b, a≤b implies that for all naturals t, a+t≤b+t
theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
 
begin
intro h,
intro t,
cases h with k h,
rw h,
use k,
ring,
end
```

## Level 12

```lean
-- For all naturals a and b, succ(a)≤succ(b)⟹a≤b.
theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b :=
 
begin
intro h,
cases h with k h,
rw succ_add at h,
have h1 := succ_inj h,
rw h1,
use k,
refl,
end
```

## Level 13

```lean
-- For all naturals a, succ(a) is not at most a
theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=
 
begin
intro h1,
induction a with k h2,
have h3 := le_zero (succ 0) h1,
apply ne_succ_self 0,
rw h3,
refl,
 
apply h2,
apply le_of_succ_le_succ,
exact h1,
end
```

## Level 14

```lean
-- If a≤b then for all t, t+a≤t+b
theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=
 
begin
rw add_comm,
rw add_comm t b,
apply add_le_add_right(h),
end
```

## Level 15

```lean
-- For all naturals a and b, a≤b∧¬(b≤a)⟹succ(a)≤b.
lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=
 
begin
intro h1,
cases h1 with h2 h3,
cases h2 with k2 h2,
cases k2,
rw add_zero at h2,
exfalso,
apply h3,
rw h2,
apply le_refl,
 
use k2,
rw succ_add,
rw add_succ at h2,
exact h2,
end
```

## Level 16

```lean
-- For all naturals a and b, succ(a)≤b⟹a≤b∧¬(b≤a).
lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=
 
begin
intro h1,
split,
apply le_of_succ_le_succ,
apply le_succ,
exact h1,
 
intro h2,
have h3 := le_trans (succ a) b a h1 h2,
apply not_succ_le_self a,
exact h3,
end
```

## Level 17

```lean
-- For all naturals a and b, a&lt b⟺succ(a)≤b.
lemma lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b :=
 
begin
split,
apply lt_aux_one,
apply lt_aux_two,
end
```
