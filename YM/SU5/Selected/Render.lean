import YM.SU5.Selected.PureVac
/-! Wrap the selected GNS in a `Hilbert`. Use later for transport (without unfolding the GNS Type). -/

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
open Function Filter Set Topology NormedSpace MeasureTheory Measure ContinuousMap WeakDual
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ComplexOrder
variable {A W : Type*} {B : Type} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {D:Submodule ℂ W} [CompleteSpace D]

namespace Transaction
variable (T:Transaction A B D) (x:Resident A)
noncomputable def representation : Hilbert := { space := (T.selected x).GNS }
noncomputable def showOp : B →⋆ₐ[ℂ] ((representation T x).Op) := implement (T.selected x)
noncomputable def showVec : T.representation x := vector (T.selected x)
noncomputable def showForm : B →L[ℂ] (T.representation x).space := vectorForm (T.selected x)
lemma show_stamp (b:B): T.showOp x b (T.showVec x)=T.showForm x b:= rfl
lemma show_square (b c:B) : inner ℂ (T.showOp x b (T.showVec x)) (T.showOp x c (T.showVec x))=T.selected x (star b*c) := Theory.form_is (T.selected x) b c
lemma show_mean (b:B): inner ℂ (T.showVec x) (T.showOp x b (T.showVec x))=T.selected x b:= Theory.read_is (T.selected x) b
lemma show_spin : DenseRange (T.showForm x) := Theory.frequency (T.selected x) -- tune
lemma show_queue (b:B) (p:b∈T.steps) : T.showOp x b (T.showVec x)=T.showVec x := T.fixed_Ω x b p
lemma show_norm : ‖T.showVec x‖=1 := T.unit_Ω x
lemma show_fixed (p:T.FixedPhase x) : ∀ v : T.representation x,
      (∀ b∈T.steps, T.showOp x b v=v) → ∃ c:ℂ,v=c • T.showVec x:=p
end Transaction
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory.Transaction.show_fixed
