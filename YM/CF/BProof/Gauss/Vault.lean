import YM.CF.BProof.Gauss.Week

/- Sup transform and locality. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open Prox (Base Show Scope Pup Solo)
open YM.SectorNext.Vacuum.Panel
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {I:Type*} [Fintype I][DecidableEq I]
lemma beam_charge {I:Type}[Fintype I][DecidableEq I] (H:Pool I) (p: I){W: Via I} (z:ℝ)(C:ℝ)(hz:0≤z)(hv:∑ i,|H p i|≤ C)(u:∀ i,H p i≠0→ |W i|≤z) : |(H *ᵥ W) p|≤ C*z:=by
 unfold Matrix.mulVec dotProduct; apply (Finset.abs_sum_le_sum_abs ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right hv hz); rw [sum_mul]; refine sum_le_sum fun i h=>?_ ; by_cases he:H p i=0; simp [he]; exact (abs_mul ..).trans_le (mul_le_mul_of_nonneg_left (u i he) (abs_nonneg _))

namespace Beam
local instance {α:Type} : MeasurableSpace (Finset α) := ⊤
local instance {α:Type} : MeasurableSingletonClass (Finset α) := ⟨fun i=> trivial⟩
variable {s:Side}{Y:Yard s}(T:PathData SU.group) {M:ℕ}{c:Clip}(θ:ℝ) {P y q w:ℝ} (U:Beam c P Y.short M y)(Z:Finset Y.Col)

variable (H:Room Y M)(u:T.Bounds c w P q)(h: θ∈Set.Icc (1/2) 2)
def tide (c:Clip)(d:ℕ):= Bin.maximum (Gauss.floor c d)
def guard (d:ℕ):= d*3*SU.group.lieDim
def low (c:Clip)(P:ℝ)(d M:ℕ):= Bin.pay (peak c P d M)
abbrev cost (c:Clip)(d R:ℕ):ℝ:= (((2*R+1)^3*(guard d):ℕ):ℝ)*tide c d
def time (U:Beam c P Y.short M y):ℝ :=Journey.bill (Gauss.base Y) U.q (guard Y.short) U.horizon' U.n
lemma round : Journey.Bloc (Gauss.base Y) (tide c Y.short) (low c P Y.short M) U.q (edge Y).roof U.horizon' U.n:=by rw [roof_eq]; exact U.route _ rfl -- name round ambiguous
include H u h
private lemma numeric : Numeric (U.ζ T θ Z) (low c P Y.short M) (tide c Y.short):= (U.measured T θ H u h Z).2.1 -- arg order tune
private lemma reflect : (U.ζ T θ Z).IsHermitian:=(U.measured T θ H u h Z).1
private lemma attend : Prox.Show (Journey.feeO (Scope.flags _) (U.ζ T θ)) (edge Y) (edge Y) (fun Z=>(U.ζ T θ Z)⁻¹) U.q ((tide c Y.short)⁻¹*U.time):= by
 unfold time; rw [← show (edge Y).roof=guard Y.short from roof_eq _]
 exact Journey.bound_inv (edge Y) (Scope.flags _) (U.ζ T θ) (tide c Y.short) _ _ (U.ζ_v T θ H) U.round (reflect T θ U · H u h) (numeric T θ U · H u h) -- implicit local inst

theorem options : Nonempty (Night.Design (Gauss.base Y) (Night.logDiff (U.ζ T θ)) (U.q/3) (Night.fareD 3 (guard Y.short) U.time U.q)):=by
 unfold time; rw [← show (edge Y).roof=guard Y.short from roof_eq _]; exact Night.settle _ _ _ _ _ (U.ζ_v T θ H) U.round (reflect T θ U · H u h) (numeric T θ U · H u h)
lemma bright : 0 < (U.ζ T θ Z).det :=(YM.SectorNext.Vacuum.Panel.determinant (U.reflect T θ Z H u h) (U.numeric T θ Z H u h) U.round.precise).1
lemma fast (i:Stamp Y): ∑ j,|(U.ζ T θ Z)⁻¹ i j|≤(tide c Y.short)⁻¹*U.time:= (U.attend T θ H u h).dotPay U.round.cost.le Z i
lemma sup_meter (i:Stamp Y): ∑ j,|U.ζ T θ Z i j|≤cost c Y.short U.horizon':= by
 let b:= tide c Y.short; have hp:0≤b:= (norm_nonneg _).trans (U.measured T θ H u h Z).2.2.1; let F:=edge Y; let X:=(Gauss.base Y).ball i.1 U.horizon'
 calc
   _ ≤ ∑ j: Stamp Y with F.port j∈ X, b:= by
     rw [sum_filter]; refine sum_le_sum fun j _=>?_ ; split; · exact (entry ..).trans ((U.measured T θ H u h Z).2.2.1)
     next h=> rw [(U.ζ_v T θ H).door _ _ _ (fun e=>h (((Gauss.base Y).ball_m ..).2 e)),abs_zero]
   _ ≤ _:=by
     rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hp; apply Nat.cast_le.mpr; apply le_trans (b:=X.card*F.roof) (by convert F.vent X using 1 <;> congr!); change _≤_*guard _; rw [show guard Y.short=F.roof from (roof_eq _).symm]; exact Nat.mul_le_mul_right _ ((Gauss.base Y).size i.1 U.horizon')
end Beam
end YM.CF.BProof.Gauss
