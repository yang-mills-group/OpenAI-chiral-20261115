import YM.SU5.Reconstruction.LinkMeasures.Socket
import YM.SU5.Reconstruction.LinkMeasures.MorningRoom
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Tower Tower.SatinVerification PaymentCamera
variable (S:Finset Cover)(w:Evens S)(K: Calibration)
private lemma noteNone (t:Evens S): note K (daub S 0) (tagWord S t.val)=0:=by funext m v; change note K (0:PairsC→ℂ) (tagWord S t.val) m v=0; rw [note_v]; change (0:ℂ) • _=0; rw [zero_smul]
private lemma nu_same (t:Pigment S): nuance S w t w=t:= Pi.single_eq_same ..
private lemma nu_diff (t:Pigment S){i:Evens S}(h:i≠ w): nuance S w t i=0 :=by unfold nuance; rw [Pi.single_eq_of_ne h] -- name?

lemma genuine (x:Listener S): render S K (singer S w x) = note K (x.val ∘ here S) (tagWord S w.val):=by
 rw [toneHere,render_eq,sum_eq_single w,nu_same,lyric]
 · intro i _ h; rw [nu_diff S w _ h,noteNone S K i]
 simp
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.genuine
