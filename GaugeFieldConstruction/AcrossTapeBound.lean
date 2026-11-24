import YM.SU5.FiniteGaugeData.Tapestry.Rafters
import YM.SU5.FiniteGaugeData.Tapestry.Chalice
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

set_option quotPrecheck false
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (i k n:ℕ)(x:sequenceOf (tent Y H))
local notation "κ"=> tent Y H
local notation "Sx" n:max=> side Y i n
local notation "Z"=>fun i' : ℕ=> side Y i i'
/-- pay all operators at cutoff even with deep step growth. Actual ROster doesn't need this
bound in its reconstruction; needed to perturb entire schedule once and for all. -/
def ticketTape (i k:ℕ) : ℕ→ℝ | 0=> 1 | n+1=> (1+‖Tapestry.music Y n i k‖)* ticketTape i k n
lemma tickets_hi (i k s:ℕ) : 1≤ ticketTape Y i k s:=by
 induction s with
 | zero => exact le_rfl
 | succ n ih=> exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (norm_nonneg _)) ih
lemma ticket_tape_mono (i k:ℕ): Monotone (ticketTape Y i k):= monotone_nat_of_le_succ fun n=> by
  have ht:= tickets_hi Y i k n; apply (one_mul _).symm.le.trans; rw [ticketTape]; gcongr; exact le_add_of_nonneg_right (norm_nonneg _)
open Fashion
private lemma raise_tape{N:Side}(x y:Ward N) : ‖x*y‖ ≤ ‖x‖*‖y‖:= Ward.save _ (fun u => (norm_mul_le (attire x u) (attire y u)).trans (mul_le_mul (Ward.pay _ _) (Ward.pay _ _) (norm_nonneg _) (norm_nonneg _)))
lemma cardBound_tape (S:BillOfWork)(s:ℕ)(q:ℝ)(A:Cloud (Dome (tent Y H))) (h:Pocket (tent Y H) S s q A) :
 ∀ i k:ℕ, ‖breathing Y H s i k A‖ ≤ ticketTape Y i k s * cloudSpan s S * q:=by
 intro i k
 apply h.bequeath (breathing Y H s i k) (mul_nonneg (zero_le_one.trans (tickets_hi Y _ _ _)) (cloudSpan_pos s S)); intro x hv
 let Y₁:= impetus Y H i (employ (tent Y H) S x)
 let e:= stageRoll Y i k
 have he (n:ℕ) : ‖accolading (fun j=>side Y i j) e n Y₁‖ ≤ ticketTape Y i k n * nectar n Y₁:=by
   induction n with
   | zero=> exact (one_mul _).symm.le
   | succ n ih=>
     rw [awards_succ]
     refine (raise_tape _ _).trans ?_; have h: ‖e n‖≤ (1+ ‖Tapestry.music Y n i k‖):= le_add_of_nonneg_left zero_le_one
     apply le_trans (mul_le_mul_of_nonneg_right (((e n).le_opNorm _).trans (mul_le_mul h ih (norm_nonneg _) (add_nonneg zero_le_one (norm_nonneg _)))) (norm_nonneg _))
     rw [ticketTape,nectar]; apply le_of_eq; ring
 have p: ‖(breathing Y H s i k) (motif (tent Y H) S x)‖=‖accolading (fun j=>side Y i j) e s Y₁‖:= by
    unfold motif; rw [breathing_pure Y H s i k _ hv]; exact congrArg (norm) (enjoying Y H i k s (employ (tent Y H) S x)).symm
 change ‖(breathing Y H s i k) _‖ ≤ _; rw [p]; exact (he s).trans ((mul_le_mul_of_nonneg_left (fanPrice Y H i s S x) (zero_le_one.trans (tickets_hi Y _ _ _))).trans_eq (mul_assoc _ _ _).symm)
lemma at_entry_bound_tape (s:ℕ)(A:Cloud (Dome (tent Y H))) (h:A∈ shorter (Dome (tent Y H)) s) (r:ℝ)(_v:0≤r)(i k:ℕ)(hg: ‖breathing Y H s i k A‖ ≤ ticketTape Y i k s*r) (hx:s ≤ Y.uv k): ‖breathing Y H (Y.uv k) i k A‖≤ ticketTape Y i k (Y.uv k)*r :=by
 have hp(t:ℕ)(d:s≤ t): ‖breathing Y H t i k A‖≤ ticketTape Y i k t*r:=by
    induction t,d using Nat.le_induction with
    | base=> exact hg
    | succ n hp ih=>
        have q:= (tidalDressing Y H i k).joins n A (auxiliaryPad (tent Y H)) (climbs (Dome (tent Y H)) hp h)
        change breathing Y H _ i k A= music Y n i k (breathing Y H n i k A) at q; rw [q]; apply ((music Y n i k).le_opNorm _).trans; rw [ticketTape,mul_assoc]; gcongr; linarith
 exact hp _ hx
#print axioms cardBound_tape
#print axioms at_entry_bound_tape
end YM.CF.Buffered.Afterglow.Tapestry
end
