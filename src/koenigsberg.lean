/- We'll try to formalize Euler's solution to the problem
of the bridges of Koenigsberg. -/

import tactic


-- Some preliminaries.

/- Unordered pair of integers.
------------------------------
These show up as edges in the graphs, so we record a couple
of facts.
-/
def upair (n m : ℕ) : finset ℕ := {n} ∪ {m} 

lemma mem_upair {x n m : ℕ}:
    x ∈ upair n m ↔ x = n ∨ x=m 
:=begin 
rw upair,
rw finset.mem_union,
repeat {rw finset.mem_singleton},    
end

lemma card_single (n : ℕ) : (upair n n).card = 1
:=begin
let single : finset ℕ := {n},
have pair_eq_single : upair n n = single, {
    ext,
    rw mem_upair,
    rw finset.mem_singleton,
    tauto,
},
have cardseq : (upair n n).card = single.card, by {rw pair_eq_single},
rw cardseq,
exact finset.card_singleton n,
end

/-The proof of the next lemma is quite long,
but straightforward.-/
lemma eq_upairs {a1 a2 b1 b2 : ℕ} :
    (upair a1 a2) = (upair b1 b2) ↔ (a1=b1 ∧ a2=b2 ) ∨ (a1=b2 ∧ a2=b1)
:=begin 
split,
---- First suppose the pairs are equal. ----
intro h,
have a1mem : a1 ∈ (upair a1 a2), by {apply mem_upair.mpr, left, refl},
rw h at a1mem,
have a1_or := mem_upair.mp a1mem,
-- At this stage, we know a1 is either b1 or b2
cases a1_or with one two,
-- (1) case a1=b1 --
left, -- need to show a2=b2
have a2mem : a2 ∈ (upair a1 a2), by {apply mem_upair.mpr, right, refl},
rw h at a2mem,
have a2_or := mem_upair.mp a2mem,
-- two more cases for a2 !
cases a2_or with one1  one2,
-- subcase a1=b1, a2=b1, longest case by far!
have a1eqa2 : a1=a2, by {rw one, rw one1},
have b2mem : b2 ∈ (upair b1 b2), by {apply mem_upair.mpr, right, refl},
rw ← h at b2mem,
have b2_or := mem_upair.mp b2mem,
have a2eqb2: a2 = b2, {
    cases b2_or with bval bval',
    -- case b2=a1
    rw a1eqa2 at bval,
    exact bval.symm,
    -- case b2=a2
    exact bval'.symm,
},
exact ⟨one, a2eqb2 ⟩,
-- subcase a2=b2, trivial
split, assumption, assumption,
-- (2) case a1 = b2 --
-- we mostly copy & paste the argument above, swapping b1 and b2
right, -- need to show a2=b1
have a2mem : a2 ∈ (upair a1 a2), by {apply mem_upair.mpr, right, refl},
rw h at a2mem,
have a2_or := mem_upair.mp a2mem,
-- two more cases for a2 !
cases a2_or with two1  two2,
-- subcase a1=b2, a2=b1, trivial
split, assumption, assumption,
-- subcase a1=b2, a2=b2 longest case by far!
have a1eqa2 : a1=a2, by {rw two, rw two2},
have b1mem : b1 ∈ (upair b1 b2), by {apply mem_upair.mpr, left, refl},
rw ← h at b1mem,
have b1_or := mem_upair.mp b1mem,
have a2eqb1: a2 = b1, {
    cases b1_or with bval bval',
    -- case b1=a1
    rw a1eqa2 at bval,
    exact bval.symm,
    -- case b2=a2
    exact bval'.symm,
},
exact ⟨two, a2eqb1 ⟩,
---- Converse: suppose the equalities, show pairs are equal ----
intro h,
ext,
rw mem_upair, rw mem_upair,
cases h with one two,
rw one.1, rw one.2, -- case one
rw two.1, rw two.2, 
tauto,--case two
end


/- Cardinality and bijection
----------------------------

We prove a result saying that, when there's a bijection between two sets,
then they have the same cardinal. Of course there's something similar in
mathlib, but it's formally different (the statement below does not use
a "function" in the sense of the underlying programming language, but in
ZF it would be a function, hence the name). 
-/
lemma card_eq_of_ZFbij {α β : Type*} [decidable_eq α] [decidable_eq β]
{A : finset α} {B : finset β} (R : α → β → Prop)
(one : ∀ a : α, a ∈ A → ∃! b:β, b ∈ B ∧ R a b )
(two : ∀ b : β, b ∈ B → ∃! a:α, a ∈ A ∧ R a b ) :
        A.card = B.card
:= begin
-- We proceed by (set-)induction on A. 
revert B,
induction A using finset.induction_on with a0 A' h IH,
---- First the case when A is empty. Need to show B is empty. ----
intros B one two,
have Bempty : B = ∅, {
    rw finset.eq_empty_iff_forall_not_mem,
    intro b,
    by_contradiction abs_h,
    have ha := two b abs_h,
    rcases ha with ⟨a, h1, h2 ⟩ ,
    exact h1.1,
},
rw Bempty, refl,
---- Now the induction step. ----
-- Need to show the result for A = A' ∪ {a0}, assuming it
-- holds for A'. 
intros B one two,
/-
one : ∀ (a : α), a ∈ insert a0 A' → (∃! (b : β), b ∈ B ∧ R a b),
two : ∀ (b : β), b ∈ B → (∃! (a : α), a ∈ insert a0 A' ∧ R a b)
⊢ (insert a0 A').card = B.card
-/
-- There is an element b0 in B corresponding to a0. 
have ha0 : a0 ∈ insert a0 A', from finset.mem_insert_self a0 A',
have exists_b := one a0 ha0,
rcases exists_b with ⟨b0, hb0, unique_b0⟩,-- OK, have b0
dsimp at unique_b0,
-- So B = B' ∪ {b0}, and induction will apply to A' and B'. 
let B' := finset.erase B b0,
-- We prove the variants of one and two with B' replacing B. 
-- First oneB', variant of one. 
have oneB' : ∀ a : α, a ∈ A' → ∃! b:β, b ∈ B' ∧ R a b, {
    intros a ha,
    have binB := one a (finset.mem_insert_of_mem ha),
    rcases binB with ⟨ b, hb, unique_b ⟩ ,
    dsimp at unique_b,
    -- the point will be to prove b ∈ B'.
    have bneqb0 : b ≠ b0, {
        by_contradiction beqb0,
        -- we show that this would imply a = a0. 
        --First show R a0 b. 
        have Ra0b: R a0 b0, from hb0.2,
        rw ← beqb0 at Ra0b,
        -- extract the uniqueness statement from "two"
        rcases (two b hb.1)  with ⟨a', ha', uniqueness ⟩ ,
        dsimp at uniqueness,
        have aeqa': a = a', from uniqueness a ⟨ finset.mem_insert_of_mem ha, hb.2⟩,
        have a0eqa': a0 = a', from uniqueness a0 ⟨ ha0, Ra0b ⟩,
        have aeqa0 :a = a0, by {rw a0eqa', exact aeqa' },
        -- OK we have have a = a0. 
        rw aeqa0 at ha,
        -- contradiction!
        exact h ha,
    },
    have binB' : b ∈ B', from finset.mem_erase.mpr ⟨bneqb0, hb.1 ⟩,
    use b, dsimp,
    split,
    exact ⟨ binB', hb.2⟩,
    -- only need to reprove the uniqueness, but this will be trivial from unique_b
    intros y hyp,
    have yinB : y ∈ B, from finset.mem_of_mem_erase hyp.1,
    exact unique_b y ⟨yinB, hyp.2  ⟩,
},

-- Second, we have twoB', variant of two. Copy & paste, mostly. 
have twoB' : ∀ b : β, b ∈ B' → ∃! a:α, a ∈ A' ∧ R a b, {
    intros b hb,
    have ainA := two b (finset.mem_of_mem_erase hb),
    rcases ainA with ⟨ a, ha, unique_a ⟩ ,
    dsimp at unique_a,
    -- the point will be to prove a ∈ A'.
    have aneqa0 : a ≠ a0, {
        by_contradiction aeqa0,
        -- we show that this would imply b = b0. 
        --First show R a b0. 
        have Rab0: R a0 b0, from hb0.2,
        rw ← aeqa0 at Rab0,
        -- extract the uniqueness statement from "one"
        rcases (one a ha.1)  with ⟨b', hb', uniqueness ⟩ ,
        dsimp at uniqueness,
        have beqb': b = b', from uniqueness b ⟨ finset.mem_of_mem_erase hb, ha.2⟩,
        have b0eqb': b0 = b', from uniqueness b0 ⟨ hb0.1, Rab0 ⟩,
        have beqb0 :b = b0, by {rw b0eqb', exact beqb' },
        -- OK we have have b = b0. 
        rw beqb0 at hb,
        -- contradiction!
        have b0neqb0 := (finset.mem_erase.mp hb).1,
        trivial,
    },
    have ainA' : a ∈ A', {
        have aininsert := ha.1,
        rw [finset.mem_insert] at aininsert,
        cases aininsert with case1 case2,
        exfalso, -- case 1 a = a0 is absurd
        exact aneqa0 case1,
        exact case2,
    },
    use a, dsimp,
    split,
    exact ⟨ ainA', ha.2⟩,
    -- only need to reprove the uniqueness
    intros y hyp,
    have yininsert : y ∈ insert a0 A', from finset.mem_insert_of_mem hyp.1,
    exact unique_a y ⟨yininsert, hyp.2  ⟩,
},
-- Hurray we can apply the induction hypothesis to A' and B'.
have cardA'eqcardB' := IH oneB' twoB',
-- Only need to establish that card A = card A' + 1 and same with B. 
have cardA := finset.card_insert_of_not_mem h,
have cardB := finset.card_erase_of_mem hb0.1,
rw ← cardA'eqcardB' at cardB,
have eq : A'.card + 1 = B.card.pred + 1, by rw cardB,
rw ← cardA at eq,
-- The very last step will be to show B.card.pred + 1 = B.card... 
have Bnonempty: B.nonempty, by {use b0, exact hb0.1},
have cardBpos := finset.nonempty.card_pos Bnonempty,
have succpred:= nat.succ_pred_eq_of_pos cardBpos,
rw (nat.succ_eq_add_one B.card.pred) at succpred,
rw succpred at eq,
exact eq,
end 

/-We finish the preliminaries with a couple of boring 
identities in ℕ which show up later.-/

lemma succ_pred (i:ℕ) (h: 0 < i) : (i-1+1 = i) ∧ (i-1+2 = i+1) := 
begin
have one : i - 1 + 1 = i, {
    rw ← (nat.pred_eq_sub_one i),
    rw ← (nat.succ_eq_add_one i.pred),
    exact nat.succ_pred_eq_of_pos h,
},
have two : i - 1 + 2 = i + 1, {
    have : 2=1+1, by refl,
    rw this,
    rw ← add_assoc,
    rw one,
},
exact ⟨ one, two ⟩,
end 


lemma pm_one {i j:ℕ} (h : 0 < i) (h' : i = j+1) : i-1 = j:=
begin 
have im1 : i - 1 + 1 = i, from (succ_pred i h).1,
have : i - 1 + 1 = j+1, from eq.trans im1 h',
exact nat.succ.inj this,
end 

/----------------------------
Start of the actual argument.
-----------------------------/


/- First, the definition of a graph. We assume that the vertices are
integers. Many other definitions would have worked, including something
like ℕ → ℕ → Prop or something, but this definitions plays well with
that of "eulerian" below. 
-/
structure graph := 
(vertices : finset ℕ)
(edges    : finset (finset ℕ))
(edge_hyp : ∀ E : finset ℕ, E ∈ edges → E.card = 2 ∧ E ⊆ vertices)


-- The definition of a path on a graph.
/- We define this as a map vertex : ℕ → ℕ, together with an integer "len",
 such that the values vertex i for i ≤  len define a path in the 
 usual sense, while vertex i for i > len is ignored. It is more convenient
 than to have "vertex" defined on fin len and then having coercions everywhere.

 TO DO: rewrite this using ℤ instead of ℕ. This way, identities like i-1+1=1
 simply follow from "ring". 
-/
structure path (Γ : graph) :=
(len : ℕ)
(vertex : ℕ  → ℕ)
(via_edges: ∀ i : ℕ, i < len  → 
        upair (vertex i) (vertex (i+1)) ∈  Γ.edges   ) 
/-Note : len is then the number of edges visited, not the number 
of vertices (which is len +1). For example for len = 3, the vertices 
are 0, 1, 2, 3, the last edge is {2, 3}.  Also note that first vertex to be
visited is vertex 0 and and the last is vertex len. 
 -/

-- Given a path p, we can talk about the i-th visited edge. 
-- This is edge_visited p i, according to the definition below.
def edge_visited {Γ : graph} (p: path Γ) : ℕ → finset ℕ
:= λ i, upair (p.vertex i) (p.vertex (i+1))  

lemma edge_visited_on_graph {Γ : graph} (p : path Γ) :
    ∀ i < p.len, edge_visited p i ∈ Γ.edges :=
begin
intros i,
rw edge_visited, dsimp,
exact p.via_edges i,
end 

-- Vertices with are successive in a path are different:
lemma succ_vertices_different {Γ : graph} (p : path Γ) {i : ℕ } (hi : i < p.len):
        p.vertex i ≠ p.vertex (i+1)
:=begin
intro hyp,
have card1 : (upair (p.vertex i) (p.vertex (i+1))).card = 1, {
    rw ← hyp,
    exact card_single (p.vertex i),
},
have card' : (edge_visited p i).card = 1, 
    by {rw edge_visited, dsimp, exact card1},
have is_an_edge := edge_visited_on_graph p i hi,
have contr := Γ.edge_hyp (edge_visited p i) is_an_edge,
rw contr.1 at card',
-- we have shown 2 = 1. 
have : 2 ≠ 1, by norm_num,
exact this card',
end




/-Now a path is going to be called *eulerian* if it uses each edge
of the graph just once. -/
def eulerian {Γ : graph} (p : path Γ):= 
    (∀ E ∈ Γ.edges, ∃ i : ℕ, i < p.len ∧ E = edge_visited p i) ∧
    (∀ i j : ℕ, i < p.len → j < p.len → edge_visited p i = edge_visited p j → i = j)


/-Next we need to define the degree of a vertex, which is the number
of edges incident with it.-/
def degree (Γ : graph) (v : ℕ ) :=
(Γ.vertices.filter (λ w: ℕ, (upair v w) ∈ Γ.edges)).card 




/-Main theorem : Suppose there is a eulerian path on the graph Γ,
and suppose v is a vertex, but not the starting or ending point of the
path. Then the degree of v is even.
-/
theorem eulerian_even_degree {Γ : graph} (p : path Γ) (euler : eulerian p)
    (v : ℕ) (notfirst : v ≠ p.vertex 0) (notlast : v ≠ p.vertex p.len) :
    even (degree Γ v)
:=begin
-- Start by rewriting what eulerian means. 
rw eulerian at euler,
cases euler with surj inj,
/-
surj : ∀ (E : finset ℕ), E ∈ Γ.edges → (∃ (i : ℕ), i < p.len ∧ E = edge_visited p i),
inj : ∀ (i j : ℕ), i < p.len → j < p.len → edge_visited p i = edge_visited p j → i = j
-/
-- Consider the set N of neighbours of v. 
let N:= Γ.vertices.filter (λ w: ℕ, (upair v w) ∈ Γ.edges),
-- We'll split the neighbours into incoming and outgoing.
let incoming:= Γ.vertices.filter (λ w : ℕ, ∃ i : ℕ, i < p.len ∧ 
    w = p.vertex i  ∧ v = p.vertex (i+1) ),
let outgoing:= Γ.vertices.filter (λ w : ℕ, ∃ i : ℕ, i < p.len ∧ 
    v = p.vertex i  ∧ w = p.vertex (i+1) ),
-- We will show that there is a bijection between incoming and outgoing,
-- and that N is the disjoint union of them. We start with the latter. 


-- Part I : the union is disjoint. 
have dis : disjoint incoming outgoing, {
    simp [disjoint],
    intros w hyp,
    rw finset.mem_inter at hyp,
    cases hyp with win wout,
    rw finset.mem_filter at win,
    rw finset.mem_filter at wout,
    rcases win.2 with ⟨ i, iltlen, vertex_eq ⟩,
    /-
    w : ℕ,
    vertex_eq : w = p.vertex i ∧ v = p.vertex (i + 1)
    -/
    -- show that upair u w is the ith visited edge
    have ith_visited : upair v w = edge_visited p i, {
        rw edge_visited, dsimp,
        rw eq_upairs, right,
        exact vertex_eq.symm,
    },
    -- and now do the same with "wout" instead of "win"
    rcases wout.2 with ⟨ j, jltlen, vertex_eq' ⟩,
    -- show that upair u w is the ith visited edge
    have jth_visited : upair v w = edge_visited p j, {
        rw edge_visited, dsimp,
        rw eq_upairs, left,
        exact vertex_eq',
    },
    -- use injectivity of edge_visited
    rw ith_visited at jth_visited,
    have ieqj:= inj i j iltlen jltlen jth_visited,
    -- OK so i=j. 
    rw ← ieqj at vertex_eq',
    have veqw : v = w, by {rw vertex_eq.1, exact vertex_eq'.1},
    rw vertex_eq'.1 at veqw,
    rw vertex_eq'.2 at veqw,
    -- This is a contradiction, since successive points in a path are different.
    exact succ_vertices_different p iltlen veqw,
},


-- Part II : N is the union of incoming and outgoing. 
have union : N = incoming ∪ outgoing, {
    ext w, rw finset.mem_union, split,
        ---- First prove that w ∈ N → w ∈ union
        begin 
        intro h,
        simp at h,
        let edge:= upair v w,
        have visited := surj edge h.2,
        rcases visited with ⟨ i, iltlen, edge_eq ⟩ ,
        simp [edge] at edge_eq,
        rw edge_visited at edge_eq,
        dsimp at edge_eq,
        /-
        edge_eq : upair v w = upair (p.vertex i) (p.vertex (i + 1))
        -/
        -- OK now we can apply the lemma on equalities of pairs
        rw eq_upairs at edge_eq,
        /-
        edge_eq : v = p.vertex i ∧ w = p.vertex (i + 1) ∨ v = p.vertex (i + 1) ∧ w = p.vertex i
        -/
        cases edge_eq with one two,
        -- case one, will prove w is outgoing,
        right, -- one : v = p.vertex i ∧ w = p.vertex (i + 1)
        have condition : ∃ i : ℕ, i <p.len ∧ v = p.vertex i  ∧ w = p.vertex (i+1), 
            by {use i, exact ⟨ iltlen, one.1, one.2 ⟩},
        exact finset.mem_filter.mpr ⟨ h.1, condition ⟩,
        -- case two, will prove w in incoming,
        left, -- two : v = p.vertex (i + 1) ∧ w = p.vertex i
        have condition : ∃ i : ℕ, i < p.len ∧ w = p.vertex i  ∧ v = p.vertex (i+1), 
            by {use i, exact ⟨ iltlen, two.2, two.1 ⟩},
        exact finset.mem_filter.mpr ⟨ h.1, condition ⟩,
        end, -- first inclusion proved

        ---- now prove w ∈ union → w ∈ N
        begin
        intro wunion,
        cases wunion with one two,
        -- subcase w incoming
        have condition := finset.mem_filter.mp one,
        rcases condition.2 with ⟨ i, iltlen, vertex_eq ⟩,
        -- vertex_eq : w = p.vertex i ∧ v = p.vertex (i + 1)
        have edge_eq : upair v w = upair (p.vertex i) (p.vertex (i+1)), {
            rw eq_upairs,
            right,
            exact vertex_eq.symm,
        },
        have is_an_edge := edge_visited_on_graph p i iltlen,
        rw edge_visited at is_an_edge,
        dsimp at is_an_edge,
        rw ← edge_eq at is_an_edge,
        apply finset.mem_filter.mpr,
        exact ⟨ condition.1, is_an_edge⟩,
        -- subcase w outgoing, mostly copy & paste
        have condition := finset.mem_filter.mp two,
        rcases condition.2 with ⟨ i, iltlen, vertex_eq ⟩,
        have edge_eq : upair v w = upair (p.vertex i) (p.vertex (i+1)), {
            rw eq_upairs,
            left,
            exact vertex_eq,
        },
        -- end of the argument is exactly the same
        have is_an_edge := edge_visited_on_graph p i iltlen,
        rw edge_visited at is_an_edge,
        dsimp at is_an_edge,
        rw ← edge_eq at is_an_edge,
        apply finset.mem_filter.mpr,
        exact ⟨ condition.1, is_an_edge⟩,
        end,
},
-- So the card of N is the sum of the other two cardinals. 
have cardeq: N.card = (incoming ∪ outgoing).card, 
    by {rw union},
simp [finset.card_disjoint_union dis] at cardeq,



-- Part III : there's a bijection between incoming
-- and outgoing, so they have the same cardinal
have same_card : incoming.card = outgoing.card, {
    -- We will construct a ZFbij between the two.
    -- (As in the statement of card_eq_of_ZFbij) 
    -- We use the following relation:
    let R:= λ (wi wo : ℕ ), ∃ i : ℕ, i < p.len ∧  
            p.vertex i = wi ∧ p.vertex (i+1) = v ∧ p.vertex (i+2) = wo,
    apply card_eq_of_ZFbij R,
    -- Need to check the two conditions. 
    begin -- first one ------------------
    -- ⊢ ∀ (a : ℕ), a ∈ incoming → (∃! (b : ℕ), b ∈ outgoing ∧ R a b)
    intros wi win,
    rw [finset.mem_filter] at win,
    rcases win.2 with ⟨ i, iltlen, vertex_eq ⟩,
    let wo := p.vertex (i+2),
    -- A couple of preliminary remarks:
    have Rwiwo : R wi wo, {
        simp [R],
        use i,
        split, exact iltlen, 
        split, exact vertex_eq.1.symm,
        split, exact vertex_eq.2.symm,
        refl,
    },
    -- And second:
    have succiltlen : i+1 < p.len, {
    by_contradiction abs_h,
    have : i+1 = p.len, by linarith,
    have last : v = p.vertex p.len, 
        by {rw vertex_eq.2, rw this},
    exact notlast last,
    },
    -- Here we go:
    use wo, dsimp, split, split,
    rw [finset.mem_filter], split,
    -- ⊢ wo ∈ Γ.vertices
    -- Let's prove that wo is a vertex of the graph
    have is_edge:= edge_visited_on_graph p (i+1) succiltlen,
    have  h:= (Γ.edge_hyp (edge_visited p (i + 1)) is_edge).2,
    simp [edge_visited] at h,
    have duh : i+1+1 = i+2, by ring,
    rw duh at h,
    have w0inpair : wo ∈ upair (p.vertex (i + 1)) (p.vertex (i + 2)), 
        by { apply mem_upair.mpr, right, refl},
    exact h w0inpair,
    -- The other conditions are easy.
    -- ⊢ ∃ (i : ℕ), i < p.len ∧ v = p.vertex i ∧ wo = p.vertex (i + 1)
    use i+1,
    have duh : i+1+1 = i+2, by ring,
    rw duh,
    exact ⟨ succiltlen, vertex_eq.2, by refl ⟩,
    exact Rwiwo,
    -- Now comes the uniqueness statement. 
    intros y hyp,
    cases hyp with h1 h2,
    simp [R] at h2,
    rcases h2 with ⟨j, zero, one, two, three ⟩,
    /-
    zero : j < p.len,
    one : p.vertex j = wi,
    two : p.vertex (j + 1) = v,
    three : p.vertex (j + 2) = y
    ⊢ y = wo
    -/
    have edges_eq : 
    upair (p.vertex i) (p.vertex (i+1)) = upair (p.vertex j) (p.vertex (j+1)), {
        rw eq_upairs, left,
        split,
        rw one, rw ← vertex_eq.1,
        rw two, rw ← vertex_eq.2,
    },
    have edges_eq' : edge_visited p i = edge_visited p j, {
        repeat {simp [edge_visited]},
        exact edges_eq,
    },
    have ieqj := inj i j iltlen zero edges_eq',
    rw ← ieqj at three,
    rw ← three,
    end,

    begin -- second one (similar) ---------------
    -- ⊢ ∀ (b : ℕ), b ∈ outgoing → (∃! (a : ℕ), a ∈ incoming ∧ R a b)
    intros wo wout,
    rw [finset.mem_filter] at wout,
    rcases wout.2 with ⟨ i, iltlen, vertex_eq ⟩,
    let wi := p.vertex (i-1),
    -- A couple of preliminary remarks:
    have ipos : 0 < i, {
    by_contradiction abs_h,
    have : i = 0, by linarith,
    have first : v = p.vertex 0, 
        by {rw vertex_eq.1, rw this},
    exact notfirst first,
    },
    have im1ltlen : i-1 < p.len, by linarith,
    have duh : i-1 + 1 = i, from (succ_pred i ipos).1,
    have duh' : i-1 + 2 = i+1, from (succ_pred i ipos).2,
    -- And second:
    have Rwiwo : R wi wo, {
        simp [R],
        use i-1,
        split, linarith, 
        split, refl,
        split, 
        rw duh, exact vertex_eq.1.symm,
        rw duh', exact vertex_eq.2.symm,
    },
    
    -- Here we go:
    use wi, dsimp, split, split,
    rw [finset.mem_filter], split,
    -- Let's prove that wo is a vertex of the graph
    have is_edge:= edge_visited_on_graph p (i-1) (by linarith),
    have  h:= (Γ.edge_hyp (edge_visited p (i - 1)) is_edge).2,
    simp [edge_visited] at h,
    rw duh at h,
    have wiinpair : wi ∈ upair (p.vertex (i - 1)) (p.vertex i), 
        by { apply mem_upair.mpr, left, refl},
    exact h wiinpair,
    -- The other conditions are easy. 
    use i-1,
    rw duh,
    exact ⟨ by linarith, by refl, vertex_eq.1⟩,
    exact Rwiwo,
    -- Now comes the uniqueness statement. 
    intros y hyp,
    cases hyp with h1 h2,
    simp [R] at h2,
    rcases h2 with ⟨j, zero, one, two, three ⟩,
    /-
    zero : j < p.len,
    one : p.vertex j = y,
    two : p.vertex (j + 1) = v,
    three : p.vertex (j + 2) = wo
    ⊢ y = wi    
    -/
    have edges_eq : 
    upair (p.vertex i) (p.vertex (i+1)) = upair (p.vertex (j+1)) (p.vertex (j+2)), {
        rw eq_upairs, left,
        split,
        rw two, rw ← vertex_eq.1,
        rw three, rw ← vertex_eq.2,
    },
    have edges_eq' : edge_visited p i = edge_visited p (j+1), {
        repeat {simp [edge_visited]},
        exact edges_eq,
    },
    have jp1ltlen : (j+1) < p.len, {
        by_contradiction abs_h,
        have : j+1 = p.len, by linarith,
        have last : p.vertex p.len = v, by {rw ← this, exact two},
        exact notlast last.symm,
    },
    have ieqjp1 := inj i (j+1) (by linarith) jp1ltlen edges_eq',
    have im1eqj : i-1 = j, from pm_one ipos ieqjp1,
    rw ← im1eqj at one,
    rw ← one,
    end,
},


-- We can conclude.
rw same_card at cardeq,
have : outgoing.card + outgoing.card = 2*outgoing.card, by ring,
rw this at cardeq,
simp [degree],
use outgoing.card,
exact cardeq,
end

