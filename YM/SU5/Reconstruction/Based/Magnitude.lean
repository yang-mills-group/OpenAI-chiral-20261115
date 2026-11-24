import YM.SU5.Reconstruction.Based.Separables
import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false
noncomputable section
open Function Finset
open scoped Topology BigOperators Classical
namespace YM.CF.Segregate
variable {X:Type*}{S:Finset X}
lemma magnitude (f:X→ℂ)(e:ℝ)(h:0<e)(p:e≤ ‖∑ i∈ S,f i‖):∃ x∈ S, e≤S.card * ‖f x‖:=by
 have he:S.Nonempty:=by by_contra v; rw [Finset.not_nonempty_iff_eq_empty.mp v] at p; simp only [sum_empty,norm_zero] at p; exact not_lt.mpr p h
 obtain ⟨i,u,hz⟩:= exists_mem_eq_sup' he (fun i:X=> ‖f i‖)
 refine ⟨i,u,p.trans ((norm_sum_le ..).trans ?_)⟩
 calc
    _ ≤ ∑ _∈ S,‖f i‖ := Finset.sum_le_sum fun j p=> (le_sup' (fun i=>‖f i‖) p).trans hz.le
    _ = _ := by simp
end YM.CF.Segregate
