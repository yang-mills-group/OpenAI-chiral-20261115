import GaugeFieldConstruction.ArmeleMars
import GaugeFieldConstruction.StyriaRel.YM.Euclid.RPPeak
import GaugeFieldConstruction.StyriaRel.YM.Euclid.Pairing
/-!
 # complete formal derivative rows. Keep c and monomial prices explicit
# Extending RP values to tie configurations
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
-- directed reference masks paired without casts along append in downstream kernels
open NSF.Table.Pairing FirstPackMars
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C)(Y:AreaQc S)
local notation "T"=> BellTableMars p Y
variable (a:Axis)
open NSF.Table (PastTest)
open PlayArchiveMars
open scoped ComplexOrder
variable {p Y a}{J:Hilbert}(W:PlayArchiveMars p Y a J)
namespace PlayArchiveMars
variable (h: FirstPackMars p Y)
variable (X:∀ a: Axis,∃ H:Hilbert,Nonempty (PlayArchiveMars p Y a H))
include h X
lemma RipenedMars : NSF.Table.RPSmear (BellTableMars p Y):=by
 constructor
 · exact fun _ _ _=> pairedIntegrable _ h.SymHallMars (BellSmMars ..) _ _
 intro a n w c; obtain ⟨J,⟨A⟩⟩:= X a
 let u:= ∑ i:Fin n,c i • (A.FrostMantaMars (w i)); have he: 0≤ inner ℂ u u:= by rw [inner_self_eq_norm_sq_to_K]; positivity -- tune
 apply he.trans_eq; unfold u; rw[sum_inner]; refine sum_congr rfl (fun i _=>?_); rw[inner_sum]; refine sum_congr rfl (fun j _=>?_); rw[inner_smul_right,inner_smul_left, A.FrostπMars h, mul_assoc, mul_left_comm]; rfl
variable (hCap:∀ (n:ℕ)(F:Fin n→ΧiMars),CaporMars (WallMars Y F))
include hCap
lemma PlumFullMars : NSF.Table.Hierarchy (BellTableMars p Y):=⟨h.BellCommonMars,h.BellSpinMars,h.TableHomoMars,NSF.Table.Pairing.at_point h.SymHallMars (BellSmMars ..) (RipenedMars h X),RipenedMars h X,BellSmMars ..,TableLengthMars p Y hCap⟩
#print axioms PlumFullMars
end PlayArchiveMars
end YM.GaugeFieldConstruction.Ember.Volumetric
