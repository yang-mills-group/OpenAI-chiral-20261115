import YM.CF.Phase.Hop
import Mathlib.Topology.Separation.Lemmas

/-! Two kinds of continuation, no implicit branch convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Set
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {I : Type*} [TopologicalSpace I]
lemma solo {v : I→ℂ} {s : Set I} (h : IsPreconnected s) (u : ContinuousOn v s)
    (k : Set ℂ) (g : k.Countable) (e : MapsTo v s k) (x y : I) (hx : x∈s) (hy : y∈s) : v x=v y :=
  (g.isTotallyDisconnected _ e.image_subset (h.image v u)) (mem_image_of_mem v hx) (mem_image_of_mem v hy)
lemma stalk {v w : I → ℂ} {s : Set I} (h : IsPreconnected s) (u : ContinuousOn v s) (f : ContinuousOn w s) (x : I) (hx : x∈s)
    (g : ∀ y∈s, v y^2=w y^2) (e : ∀ y∈s,w y≠0) (k : v x=w x) : ∀ y ∈ s,v y=w y := by
  let t := v/w
  have ht y (hy:y∈s) : (t y)^2=1 := by simp only [t,Pi.div_apply,div_pow,g y hy]; rw [div_self (pow_ne_zero _ (e y hy))]
  let K : Set ℂ := {1,-1}
  have H : MapsTo t s K := by
    intro y hy; have hb := ht y hy; change t y ∈ Set.insert 1 {(-1:ℂ)} -- notation?
    exact (sq_eq_one_iff).mp hb
  intro y hy; have hb := solo h (u.div f e) K (by simp [K]) H y x hy hx
  change v y / w y = v x / w x at hb; rw [k,div_self (e _ hx),div_eq_one_iff_eq (e _ hy)] at hb; exact hb
lemma carry_log {v w : I → ℂ} {s : Set I} (h : IsPreconnected s) (u : ContinuousOn v s) (f : ContinuousOn w s) (x : I) (hx : x∈s)
    (g : ∀ y∈s, (v y).exp=(w y).exp) (k : v x=w x) : ∀ y∈s, v y=w y := by
  let F := fun t:ℤ => (t:ℂ)*(2*Real.pi*Complex.I)
  have he : MapsTo (v-w) s (range F) := by
    intro y hy; obtain ⟨n,H⟩ := Complex.exp_eq_exp_iff_exists_int.mp (g y hy)
    exact ⟨n, by simp [Pi.sub_apply,H,F,mul_assoc]⟩
  intro y hy; have hb := solo h (u.sub f) _ (countable_range F) he y x hy hx
  simp only [Pi.sub_apply,k, sub_self] at hb; exact sub_eq_zero.mp hb
end YM.CF.Phase
