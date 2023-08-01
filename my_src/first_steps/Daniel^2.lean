import tactic
import linear_algebra.finite_dimensional --dim vector_space
import algebra.module.algebra --def vector_space
import algebra.module.linear_map -- lin. operators
import algebra.algebra.basic -- def Field
import data.real.basic --  to say F = ℝ
import linear_algebra.eigenspace.basic --

open finite_dimensional
open linear_map
open module

--variables (m : ℕ) -- divisor vor dim of the vector_space
          --{F : Type v } {V : Type w} [field F] [add_comm_group V] [module F V] --defines a vector_space / module over a field

lemma comm_lin_op_has_comm_eigenvec (F : Type) [field F] (V : Type) [add_comm_group V] [module F V] [free F V] [finite F V] (m : ℕ) (hm : ¬( m ∣  finrank F V)) (hV : (∀ f : End F V, ∃ μ : F, ∃ v : V , f.has_eigenvector μ v)) (g h : End F V) (hgh : g ∘ h = h ∘ g) : (∃ x : V, ∃ α β : F , g.has_eigenvector α x ∧ h.has_eigenvector β x)
:=
--statement: is there an  F vector_space V, such that m > 1 doesn't divide dim V and ever lin. operator f has eigenvector, then every F vector_space V that fullfills the asumption  has for every commuting lin operator a common eigenvector
begin
  sorry,
end

theorem real_odd_dim_space_has_real_eigenval (V : Type) [h : field ℝ] [add_comm_group V] [module ℝ V] [free ℝ V] [finite ℝ V](hV : ¬( 2 ∣ finrank ℝ V)) :
(∀ g : End ℝ V, ∀ h : End ℝ  V, (g ∘ h = h ∘ g) →
(∃ x : V, ∃ α β : ℝ, g.has_eigenvector α x ∧ h.has_eigenvector β x)) :=
-- statement: for every real vector_space V with an odd dimension, has a real eigenvalue
begin
intros g h,
intro hgh,
-- apply comm_lin_op_has_comm_eigenvec ℝ h V _inst_2 2,
end
