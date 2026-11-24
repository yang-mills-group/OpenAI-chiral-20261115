import SatinThinProcess
import SatinThinTripods
import SatinThinCardiff
import YM.SU5.Regis.Legend
import YM.SU5.Hiro.Ladles
import YM.SU5.Regis.Voyance
import YM.SU5.Celeste.Custodian

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
variable (z:PlaqAxes→ℝ) {I U:Type} [Fintype I] [Fintype U] (T:Trip I)(s:ℕ)(b:U→ ℕ)
local notation "xθ"=> hat P.par.R.L P.par.x s
/-! # affine pose bill and count. -/
variable (A:ℝ)
local notation "M"=> P.par
open BProof Py.Rate.Pannier Py.Rate.LocalLimit.Papal
open Signal.Interval (separationCost)
open Lattice
/-! # Per-placement variance tariff from two-tour estimate. No asymptotic here. -/
abbrev mixCost (d:ℕ) := sunRank P.par.K.top.clip (padC z SU.group A xθ) d
abbrev stipend (f:P.Test) (q:ℂ):= (∫ x, ‖P.singleState j s x f-q‖^2∂ P.pillars j)
include T
lemma total_border [Nonempty U] {ε:ℝ} (u:0 ≤ ε)(h:∀ i k:U, let Q':=P.win_stack j T b i k; ‖P.E s (P.visitLedger z Q' s).val- (P.parish z Q' s A:ℂ)‖≤ ε)(v:Injective b)(g:∀ i,Tower.region j 0 P.calibration.ℓ (onFlight P.par.block T.canvasC j (b i))):
   (Fintype.card U:ℝ)^2* (∫ x, ‖P.singleState j s x (P.visitLedger z T s)‖^2 ∂ P.pillars j) ≤ ((Fintype.card U:ℝ)*P.parish z T s A)^2+ (Fintype.card U)*P.mixCost z s A (Fintype.card I)+(Fintype.card U:ℝ)^2*ε:= by
 let D:= P.mixCost z s A (Fintype.card I); let N:ℝ:= Fintype.card U; let a(i k:U):= P.eReadL s (P.visitLedger z (P.win_stack j T b i k) s); let a'(i k:U):= P.parish z (P.win_stack j T b i k) s A
 let P':= ∑ i, ∑ j',a' i j'; let V:= (N* P.parish z T s A)^2; have he: |P'-V|≤ N* D:= P.duelCapital j z T s b A v
 have hf: |P'|≤ V+N*D:= by nth_rw 1 [← sub_add_cancel P' V]; exact (abs_add_le ..).trans ((add_le_add he (le_of_eq (abs_of_nonneg (sq_nonneg _)))).trans_eq (add_comm ..))
 let X:=∑ i:U,∑ j':U,a i j'; have t: ‖X- (P':ℂ)‖≤N^2*ε:=by
    unfold X P'; push_cast; rw [←sum_sub_distrib]; simp_rw [←sum_sub_distrib]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (s:=univ) (g:=fun _=> ε) (fun j _=> h i j)))).trans_eq ?_); unfold N; simp; ring
 apply (P.stamp_bound j z T s b g).trans; apply (norm_le_norm_sub_add X (P':ℂ)).trans; rw [Complex.norm_real,Real.norm_eq_abs]; exact (add_le_add t hf).trans_eq (add_comm ..)
lemma variance_cost [Nonempty U] {E ε C:ℝ} (u: 0 ≤ ε)(h0: ‖P.E s (P.visitLedger z T s).val-(P.parish z T s A:ℂ)‖≤ε)(h:∀ i k:U, let Q':=P.win_stack j T b i k; ‖P.E s (P.visitLedger z Q' s).val- (P.parish z Q' s A:ℂ)‖≤ ε)
  (v:Injective b)(g:∀ i,Tower.region j 0 P.calibration.ℓ (onFlight P.par.block T.canvasC j (b i)))(hg: |P.parish z T s A|≤ C)
  (w:P.mixCost z s A (Fintype.card I) ≤ Fintype.card U*(E/3))(z': (1+2*C)*ε ≤ E/2) (hp:0≤E):
  P.stipend j s (P.visitLedger z T s) (P.parish z T s A:ℂ) ≤ E:=by
 let D:= P.mixCost z s A (Fintype.card I); let N:ℝ:= Fintype.card U; let V:=(P.visitLedger z T s); let f:= P.parish z T s A; let y:= P.E s V.val
 have hx: |y.re-f| ≤ ε:= by apply h0.trans'; rw [← Complex.ofReal_re f, ←Complex.sub_re]; exact Complex.abs_re_le_norm _
 have hN:0<N:=Nat.cast_pos.mpr Fintype.card_pos
 let u':=∫ x, ‖P.singleState j s x V‖^2 ∂ P.pillars j; have hv:u' ≤ f^2+ε+ E/3:=by
    have hl:N^2*u'≤ (N*f)^2+N*D+N^2* ε:= P.total_border j z T s b A u h v g; have hW:D≤N*(E/3):=w
    apply le_of_mul_le_mul_left ?_ (sq_pos_of_pos hN); linarith only [hl,mul_le_mul_of_nonneg_left hW hN.le]
 have hy: f*(f-y.re) ≤ C*ε:= by apply (le_abs_self _).trans; rw [abs_mul,abs_sub_comm]; exact mul_le_mul hg hx (abs_nonneg _) ((abs_nonneg _).trans hg)
 rw [stipend,P.viewpointV]; change u'-2*f*y.re+f^2≤E; linarith only [hv,hy,z',hp]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.variance_cost
