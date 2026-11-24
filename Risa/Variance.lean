import Risa.Array
import Risa.Testify
import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
local notation "D1" => CF.Compass.decor
variable (Xh:Hike) (y:ℝ)
local notation "χ"=> Xh.cost
local notation "Γ"=> (ridges:ℝ)
local notation "𝕥"=>p.threshold
local notation "τh"=>tempRate p Xh y
local notation "Υ₀"=>posess G Xh
section
universe wP
variable {I:Type wP}[Fintype I](o:I→Bool→Site n)(p0:∀i:Bool,Injective (fun j:I=>o j i))(t:I→Bool→Signed)(a:I→ℝ)(n₀:Bool)
section
universe wQ
variable {T':Type wQ}[Fintype T']
lemma rays_priced (Ap:Etch G T')(r:I→ Site n)(p:Injective r)(t:I→Signed) (x z:Altar G n): (∑ i:I,|Ap.chalk q y (t i) (r i) x-Ap.chalk q y (t i) (r i) z|) ≤ (Ap.lensLimit q y * Real.sqrt (Fintype.card I)) * ‖x-z‖:=by
 let X(i:I)(b:Signed)(j:T'):=‖Etch.cup (slotFace (skewSlot G (Ap.slot j) b) (r i)) (x-z)‖; let c:ℝ:= Ap.favor*Etch.rays q y; have h:0 ≤ c:=by unfold c Etch.rays; positivity
 refine (Finset.sum_le_sum (g:=fun i=> c* (∑ b:Signed,∑ j:T',X i b j)) (fun i _=>(Ap.chalk_steady q y (t i) (r i) x z).trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun b=> ∑ j:T', X i b j) (fun b _=> sum_nonneg (fun j _=> norm_nonneg _)) (mem_univ (t i))) h))).trans ?_
 rw [← mul_sum, Finset.sum_comm]; refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun _=> Fintype.card T'*(Real.sqrt (Fintype.card I)*‖x-z‖)) ?_) h).trans_eq ?_
 · intro i _; rw [Finset.sum_comm]; refine (Finset.sum_le_sum (fun u _=> Etch.cup_sum r p (skewSlot G (Ap.slot u) i) _)).trans_eq (?_); simp
 rw [sum_const,card_univ,nsmul_eq_mul]; unfold c Etch.lensLimit; ring
end
open scoped NNReal
variable {k:ℝ}(h:∀i, |a i|≤ k)(u:0 ≤ k)
local notation "Λ₁"=>limitRay Xh y (G:=G) (q:=q)
noncomputable abbrev portent (G:Gauge)(q:Clip)(Xh:Hike)(k R y:ℝ):=2*k*R*limitRay Xh y (G:=G) (q:=q)
include u in
lemma port_low {R:ℝ}(m:1 ≤ R):0 ≤ portent G q Xh k R y:= mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) u) (zero_le_one.trans m)) (xRay ..)
include p0 h u
theorem table_change {R:ℝ}(m:1 ≤ R)(d:(Υ₀).arc ≤ R) (x:Altar G n) : ‖fderiv ℝ (tableZ G q Xh y o t a n₀) x‖ ≤ portent G q Xh k R y*Real.sqrt (Fintype.card I):=by
 let μ:=portent G q Xh k R y; let E:=Real.sqrt (Fintype.card I); let N:ℝ≥0:=⟨μ*E,mul_nonneg (port_low Xh y u m) (Real.sqrt_nonneg _)⟩
 refine norm_fderiv_le_of_lipschitz ℝ (C:=N) (LipschitzWith.of_dist_le_mul fun x z=>?_)
 rw [dist_eq_norm,dist_eq_norm,Real.norm_eq_abs]; unfold tableZ; rw [←sum_sub_distrib]
 let M(i:I)(j:Bool)(x:Altar G n):= (Υ₀).chalk q y (t i j) (o i j) x; let F (i:I)(j:Bool):=|M i j x - M i j z|
 have ht(i:I)(j:Bool)(x): |M i j x| ≤ R:= ((Υ₀).chalk_bound ..).trans d
 apply (Finset.abs_sum_le_sum_abs ..).trans
 refine (sum_le_sum (g:=fun i:I=>k*(R*∑ j:Bool,F i j)) (fun i _=>?_)).trans ?_
 · rw [← mul_sub_left_distrib,abs_mul]; exact mul_le_mul (h _) (grainL m (fun j=>ht i j x) (fun j=>ht i j z)) (abs_nonneg _) u
 rw [← mul_sum]; simp_rw [←mul_sum] --? outer R
 rw [sum_comm]; let P:= Λ₁*E* ‖x-z‖
 have h0: (∑ j:Bool,∑ i:I,F i j) ≤ ∑ _:Bool,P:= sum_le_sum fun j _=> rays_priced y (Υ₀) (fun i=>o i j) (p0 j) (fun i=>t i j) x z
 rw [sum_const,card_univ,nsmul_eq_mul,Fintype.card_bool] at h0
 change k*(R*_)≤ μ*E*_
 unfold μ portent; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h0 (zero_le_one.trans m)) u).trans_eq (by unfold P; norm_num; ring)
#print axioms table_change
end
end Risa
end YM.Gleam.Luster
