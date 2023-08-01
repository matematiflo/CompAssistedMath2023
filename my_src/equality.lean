universes u v

inductive Equ {A : Type u} (x : A) : A → Type u
  | refl : Equ x

def Equ_is_reflexive : ∀ {A : Type u} (x : A), Equ x x := 
begin
intros A x,
constructor,
-- exact Equ.refl,
end

def Equ_is_symmetric : ∀ {A : Type u} (x y : A), Equ x y → Equ y x := 
begin
intros A x y a1,
induction a1, constructor,
end

def Equ_is_transitive : ∀ {A : Type u} (x y z : A), Equ x y → Equ y z → Equ x z := 
begin
intros A x y z a1 a2,
induction a1,
apply a2,
end

-- Resizing Type
def Leibniz : ∀ {A : Type u} (x y : A), (Type (u + 1))
  | A x y := ∀ (P : A → Type u), P x → P y

def Leibniz_refl : ∀ {A : Type u} (x : A), Leibniz x x :=
begin
intros,
unfold Leibniz,
intros P a,
apply a
end

def Leibniz_trans : ∀ {A : Type u} (x y z : A), Leibniz x y → Leibniz y z → Leibniz x z :=
begin
intros A x y z a1 a2,
unfold Leibniz at a1 a2,
unfold Leibniz,
intros P a3,
apply a2 P (a1 P a3),
end

def Leibniz_symm : ∀ {A : Type u} (x y : A), Leibniz x y → Leibniz y x :=
begin
intros A x y a1,
unfold Leibniz,
unfold Leibniz at a1,
intros P,
let Q : A → Type u := λz : A, P z → P x,
let Qx : Q x := Leibniz_refl x P,
exact a1 Q Qx,
end

def Equ_implies_Leibniz: ∀ {A : Type u} (x y : A), Equ x y → Leibniz x y :=
begin
intros A x y a1,
induction a1,
apply Leibniz_refl,
end

def Leibniz_implies_Equ : ∀ {A : Type u} (x y : A), Leibniz x y → Equ x y :=
begin
intros A x y a1,
unfold Leibniz at a1,
let Q : A → Type u := Equ x,
let Qx : Q x := Equ.refl,
exact a1 Q Qx,
end

def funExt {A : Type u} (B : A → Type v) {f g : ∀ (a : A), B a}
(p : ∀ (a : A), f a = g a) : f = g :=
begin
sorry,
end
