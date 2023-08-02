# Well Ordering of the Natural Numbers

*Lean Project of Janosch and Anna-Lena in the Proseminar "Computer-assisted Mathematics"*

## 1. Goal

Our goal is to prove the well-ordering principle of the natural numbers. This principle states that every non-empty subset $S$ of $\mathbb{N}$ has a least element, in other words:

$$
    \forall S \subset \mathbb{N}, S \neq \emptyset : \exists k \in S, \forall l \in S, k \leq l
$$

This can be proven by induction, as we will do in this project. Furthermore, the well-ordering principle can also be used to prove induction, making them equivalent, but we will not prove this here.

## 2. Proof

Our proof is based on a proof from the book *Topology*.

We'll first prove the following weaker **Lemma**:

$$
    \forall n \in \mathbb{N}, \forall S \subset \lbrace 0, ..., n \rbrace, S \neq \emptyset : \exists k \in S, \forall l \in S, k \leq l
$$

**Proof of Lemma**

We'll prove the statement by *Induction* over $n$.

* $n=0$. Because $S$ needs to be nonempty, there's only one possibility for a subset of $\left\lbrace 0, ..., n \right\rbrace = \left\lbrace 0 \right\rbrace$ , which is: $S = \left\lbrace  0 \right\rbrace$. Then $k=0$ obviously satisfies $k \leq l, \forall l \in S$ and therefore is the smallest element of $S$.

* $n \rightarrow n+1$: Let $S \subset \left\lbrace 0, ..., n+1\right\rbrace$ be a nonempty subset. We observe two cases:

1. $S = \left\lbrace n+1 \right\rbrace$:
    Then $k=n+1$ is obviously the smallest element of $S$.
2. $S \neq \left\lbrace n+1\right\rbrace$:
    Let's consider the set $T = S \cap \left\lbrace 0, ..., n \right\rbrace$, which eliminates the element $n+1$ in case $(n+1) \in S$.
    Because $T \subset \left\lbrace 0, ..., n\right\rbrace$ we can apply our induction hypothesis. So $T$ has a smallest element $k$.
    If $(n+1) \in S$ then $k < n+1$, so $k$ is also the smallest element of $S$.

Therefore $S$ always has a smallest element $k \leq l, \forall l \in S$.
$q.e.d.$

Let's return to our **Theorem**.

$$
    \forall S \subset \mathbb{N}, S \neq \emptyset : \exists k \in S, \forall l \in S, k \leq l
$$

**Proof of Theorem**

Let $S \subset \mathbb{N}$ be a nonempty subset and $n \in S$. Let $T = S \cap \left\lbrace 0, ..., n \right\rbrace$.
Then $T \neq \emptyset$, because $n \in S \land n \in \left\lbrace 0, ..., n \right\rbrace$.
Because $T \subset \left\lbrace 0, ..., n \right\rbrace$ we can apply our Lemma, so there $\exists k \in T, \forall l \in T, k \leq l$ which is the smallest element of $T$.
So $k$ is the smallest element of $S \cap \left\lbrace 0, ..., n \right\rbrace$, but it's also the smallest element of $S$, because $k \leq n$ and $\forall l \in S - \left\lbrace 0, ..., n \right\rbrace : n < l \Rightarrow k < l$  and $S = (S \cap \left\lbrace 0, ..., n\right\rbrace) \cup (S - \left\lbrace 0, ..., n\right\rbrace)$.
That proves our Theorem. $q.e.d.$

## 3. Lean

### 3.1 Formalising the theorem

Like in our proof we split our theorem into a lemma and our main theorem to make our lifes easier when trying to prove the well ordering of natural numbers. Both are structured quite similar, as the mathematical expressions are also quite similar.

Let's start with the lemma:

$$ \forall n \in \mathbb{N}, \forall S \subset \left\lbrace 0, ..., n\right\rbrace, S \neq \emptyset : \exists k \in S, \forall l \in S, k \leq l$$

Our first difficulty was generalizing a nonempty subset of $\left\lbrace 0, ..., n \right\rbrace$. We therefore need three things in lean. First: specifying any subset. Lean offers the function ```set``` which does exactly this, although it is a bit confusing that it's not called ```subset```. To make it nonempty we need a hypothesis giving our subset ```S``` the attribute ```nonempty```. We tried it with ```[hS : nonempty S]```, but that seems deprecated and is impossible to revert. So instead we use ```[hS : S.nonempty]```. 
For the set $\left\lbrace 0, ..., n \right\rbrace$ we tried two approaches: ```fin(n + 1)``` and ```finset.range (n + 1)```. Both define the set $\left\lbrace x \in \mathbb{N} \mid x < n + 1 \right\rbrace  = \left\lbrace 0, ..., n\right\rbrace$ which is a bit confusing, because in the proof we use $n$ while the Lean equivalent is $n + 1$. They both work perfectly fine, but we approaches because the have different theorems and functions predefined. In the end we got a bit further with ```fin```, so we'll show that approach.
The rest is quite straight forward.

```lean
lemma well_ordering_0n (n : ℕ) (S : set (fin (n + 1))) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l := sorry
```

The theorem, as stated before, is almost the same as the lemma, so it uses the same definition of a nonempty subset. This time a subset of $\mathbb{N}$, that's why we don't need the ```fin``` function.

```lean
theorem well_ordering (S : set ℕ) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l := sorry
```

### 3.2 Proof in Lean

When we realised that we had to work with this "weird" ```fin``` function, we already had the feeling that the Lean proof would get way more complicated than the natural number game, because it not only involved induction and lemmas regarding addition, multiplication and inequalities.

That's why we did our best trying to prove our theorem with Lean tactics, but we ran into some big walls and didn't manage it fully.

```lean
lemma well_ordering_0n (n : ℕ) (S : set (fin (n + 1))) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l :=
```

Starting with our lemma we obviously start with induction over $n$ like in our proof by hand. This only worked after we figured out to write the nonempty statement as ```S.nonempty```, because Lean had problems reverting a Type of ```nonempty S```, which it automatically does when using the ```induction``` tactic.

```lean
  begin
    induction n with a ha,
```

We now want to prove our induction start where $n = 0$. In that case $k = 0$, because it's the only element in a subset of $\left\lbrace 0\right\rbrace$. So the ```use``` tactic seemed to be right.

```lean
    {
      use 0,
      {
        sorry,
      },
```

But the goal then looks like the following (where the ```sorry``` is). This looks trivial to a mathematician, but sadly not to Lean. Even high power tactics like ```library_search``` or ```hint``` don't seem to find any way around that.

```lean
S: set (fin (0 + 1))
hS: S.nonempty
⊢ 0 ∈ S
```

The next step is proving that ```⟨0, _⟩ ≤ l``` which probably means that our $k = 0$ is smaller than ```∀ (l : ↥S)```. But the ```⟨0, _⟩``` and the up-arrow ```↥``` confused us and we're still not sure what they stand for. Luckily with the ```library_search``` tactic we found a nice way of solving this goal. We don't fully understand it, but we know that ```subsingleton``` is a set with only one element. That's clearly the case for our $S$.

```lean
      {
        intro l,
        apply le_of_eq (subsingleton.elim _ _),
        exact set.subsingleton_coe_of_subsingleton,
      },
    },
```

After proving our induction start, we tried introducing our own cases like in the proof where $S = \left\lbrace n+1\right\rbrace\lor S \neq \left\lbrace n+1\right\rbrace$. We tried proving that using Lean, but we didn't manage, so our hypothesis ```hS``` got a ```sorry```. But we can now ```split``` this assumption and solve the first one (surprisingly) unsing the ```finish``` tactic.

```lean
    simp at *,
    have hS : S = {a.succ + 1} ∨ S ≠ {a.succ + 1} := sorry,
    cases hS with hSn1 hSany,
    {
      finish,
    },
```

With the right part we had our problems though. We tried introducing our intersection $T$, but neither ```fin``` nor ```finset.range``` have the ```has_inter``` attribute, which allows them to be part of a intersection. So there we stopped, because we couldn't find any way out.
We tried however a brute force approach which you can find as a comment in the ```.lean``` file. But the last goal looks quite complicated and because we couldn't simplify it anymore using with the help of ```hint``` and because it didn't have anything to do with our proof by hand, we stopped there.

```lean
    {
      -- have T : S ∩ fin(a + 1) := sorry,
      sorry,
    },
  end
```

Let's move forward to our main theorem.

```lean
theorem well_ordering (S : set ℕ) [hS : S.nonempty] : ∃ (k : S), ∀ (l : S), k ≤ l :=
```

Sadly we have almost nothing here. The only thing we could do was introducing a variable $n \in S$ and knowing that we'd need to apply the ```well_ordering_0n``` lemma. Here we're stuck again with the problem of introducing a ```T : S ∩ fin(a + 1)```, so sadly our journey on the well-ordering of the Natural Numbers ends here.

```lean
  begin
    have n : S := sorry,
    -- proof

    -- exact well_ordering_0n _ _,
    sorry,
  end
```

## 4. Conclusion

Though this was a difficult project as there is quite a learning curve with Lean, we are happy about and proud of what we have accomplished. Even just formalizing our statements was fairly hard as there are different ways of doing it that allow for different tactics to be used, but we worked through this and managed to accomplish what we set out to do. Along the way, we were thrilled about every part of a statement we managed to prove. Overall, this project was a rewarding experience.
We are both very excited about what we learned and are keen on learning more about Lean in the future. It is a very helpful tool and we look forward to continue using it and hone our skills.

## 5. xkcd comic

xkcd has a great comic on the well-ordering principle, which we of course want to share:
![xkcd: Well-Ordering Principle](https://imgs.xkcd.com/comics/well_ordering_principle_2x.png)
<https://xkcd.com/2193/>

*Janosch Alze, Anna-Lena Herzog, Summer Semester 2023, Heidelberg University*
