import YM.SU5.Reconstruction.AnglePath.Geometry
import YM.SU5.Reconstruction.AnglePath.Radius
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

namespace Organ
variable [AddCommGroup X][Module ℂ X](A:Organ X H D)(G:Clasp K H H)(p:A.Pre G)(C:Clasp J H D)(q:A.Core C)
open MeasureTheory Multiplier Clasp Complex
variable (f:X)(v:A.R f=A.L f)
include v q
lemma bloomB: C.look (A.L f)= A.d f ∧ ∀ u:ℝ, Organ.Pilot C u (A.L f)= A.L f:=by
 let g:=A.L f
 have he:(C.look g=A.d f ∧ ∀ z:ℝ,Picket.boost C z g=g):=Picket.victory C g (A.d f) ((show Faces _ _ _ _ J C from q).sees f) (fun x=>by unfold g; rw [←v]; exact (show Faces _ _ _ _ J C from q).meets f x)
 exact ⟨he.1, fun u=>he.2 (2*u)⟩
lemma archive(z:ℂ)(Z:z∈scroll): A.bond C z f=A.L f:=by
 let F:ℂ→H:=(A.bond C · f)- fun _=> A.L f
 apply sub_eq_zero.mp; apply Bank.entangles (H:=H) F (‖A.bill C f‖+‖A.L f‖) (fun z ζ=> (norm_sub_le ..).trans (add_le_add_left (A.bond_bound C z ζ f) _)) ((A.bond_inner C f).sub analyticOnNhd_const) ((A.bond_full C f).sub continuousOn_const) ?_ z Z
 intro i; change A.bond C _ f-A.L f=0; rw [(A.bond_train C q f).2.2.2 i]; apply sub_eq_zero.mpr
 let s:=-Real.pi*i/2; have he:C.cLeft i= Organ.Pilot C s:=congrArg C.cLeft (by unfold s; field_simp) -- tune
 rw [he]; exact (A.bloomB C q f v).2 s
end Organ
end YM.CrossedFrame.Cardio
