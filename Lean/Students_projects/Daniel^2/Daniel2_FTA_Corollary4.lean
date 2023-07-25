import tactic -- for tactics
import linear_algebra.finite_dimensional --dim vector_space
import algebra.module.algebra --def vector_space
import algebra.module.linear_map -- def lin. operators
import algebra.algebra.basic -- def Field
import data.real.basic --  to say F = ℝ 
import linear_algebra.eigenspace.basic -- to use "has_eigenvector" command

open finite_dimensional
open linear_map
open module

lemma lemma_3 (F : Type) [field F] (V : Type) [add_comm_group V] [module F V] [finite F V] 
(m : ℕ ) (hm : ((m > 1) ∧ ¬( m ∣  finrank F V))) (hV : (∀ f : End F V, ∃ μ : F, ∃ v : V , f.has_eigenvector μ v)) : 
∀ g : End F V, ∀ h: End F V, (g ∘ h = h ∘ g) → (∃ x : V, ∃ α β : F , g.has_eigenvector α x ∧ h.has_eigenvector β x) :=
--statement: is there an  F vector_space V, such that m > 1 doesn't divide dim V and every lin. operator f has eigenvector, then each pair of commuting lin. operators  has a common eigenvector
begin
  sorry,
end

theorem corollary_4 (V : Type) [field ℝ] [add_comm_group V] [module ℝ V] [finite ℝ V](hV : ¬( 2 ∣  finrank ℝ V)) : 
(∀ g : End ℝ V, ∀ h : End ℝ  V, (g ∘ h = h ∘ g) → 
(∃ x : V, ∃ α β : ℝ, g.has_eigenvector α x ∧ h.has_eigenvector β x)) := 
-- statement: for every real vector_space V with an odd dimension, each pair of commuting linear operators on V has a common eigenvector in V .
begin
 sorry,  
end
