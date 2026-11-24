import Risa.Dune
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
local notation "Υ₀"=>posess G Xh
-- order right(used)+optional left; Bool true=test mirrored and etc.Theor primitive.
def loader (a:Bool)(f:Bool→ℝ):ℝ:= if a then f false*f true else f true
lemma grainD {a:Bool}{f:Bool→ℝ}{u:ℝ}(h:1  ≤ u)(v:∀i, |f i|≤ u):|loader a f| ≤ u^2:=by
 unfold loader; split; · rw [abs_mul,pow_two]; exact mul_le_mul (v _) (v _) (abs_nonneg _) (zero_le_one.trans h)
 exact (v _).trans (show u ≤ u^2 by nlinarith only [h])
lemma grainL {b:Bool}{f g:Bool→ℝ}{u:ℝ}(h:1 ≤ u)(v:∀i,|f i| ≤ u)(t:∀i,|g i| ≤ u): |loader b f-loader b g|≤ u* (∑ i:Bool,|f i-g i|):=by
 rw [Fintype.sum_bool]; unfold loader; split
 · let a:=true; let b:=false
   rw [show (f b)*(f a)-g b*g a=f b*(f a-g a)+(f b-g b)*g a from (by ring)]; apply (abs_add_le ..).trans; rw [abs_mul,abs_mul,mul_add]
   exact add_le_add (mul_le_mul_of_nonneg_right (v _) (abs_nonneg _)) ((mul_le_mul_of_nonneg_left (t _) (abs_nonneg _)).trans_eq (mul_comm ..))
 exact (le_add_of_nonneg_right (abs_nonneg _)).trans (le_mul_of_one_le_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) h)
-- all samples for now at finite torus; mark true right & possibly left. sensitivity via cup_sum
section
universe wP
variable {I:Type wP}[Fintype I](o:I→Bool→Site n)(t:I→Bool→Signed)(a:I→ℝ)(n₀:Bool)
abbrev raiseX(G:Gauge)(p:BudgetPoint)(y:ℝ)(n₀:Bool)(V:Config G n)(t:Bool→Signed)(o:Bool→Site n):=loader n₀ (fun i=>solicit G p y (t i) (o i) V)
abbrev raiseZ(G:Gauge)(q:Clip)(Xh:Hike)(z:ℝ)(n₀:Bool)(V:Altar G n)(t:Bool→Signed)(o:Bool→Site n):=loader n₀ (fun i=>(posess G Xh).chalk q z (t i) (o i) V)
abbrev tables(G:Gauge)(p:BudgetPoint)(y:ℝ)(o:I→Bool→Site n)(t:I→Bool→Signed)(a:I→ℝ)(n₀:Bool)(V:Config G n):=∑ i:I,a i * raiseX G p y n₀ V (t i) (o i)
abbrev tableZ(G:Gauge)(q:Clip)(Xh:Hike)(z:ℝ)(o:I→Bool→Site n)(t:I→Bool→Signed)(a:I→ℝ)(n₀:Bool)(V:Altar G n):=∑ i:I,a i * raiseZ G q Xh z n₀ V (t i) (o i)
-- unify costs
abbrev tempRate(p:BudgetPoint)(Xh:Hike)(y:ℝ):=1+ max (gradM p y) ((ridges:ℝ)*Xh.cost^2)
lemma rate_at(p:BudgetPoint): 1 ≤ tempRate p Xh y ∧ (Υ₀).arc  ≤ tempRate p Xh y ∧ gradM p y ≤ tempRate p Xh y:=by
 unfold tempRate; have h: 0≤(ridges:ℝ)*Xh.cost^2:=by unfold ridges; positivity; -- annoying
 refine ⟨le_add_of_nonneg_right (le_max_of_le_right h),?_,?_⟩
 exact le_trans (le_max_right ..) (le_add_of_nonneg_left zero_le_one)
 exact le_trans (le_max_left ..) (le_add_of_nonneg_left zero_le_one)
noncomputable abbrev limitRay(z:ℝ):=(Υ₀).lensLimit q z
lemma xRay (a:ℝ):0  ≤ limitRay Xh a (G:=G) (q:=q):=Etch.lensLimit_non ..
local notation "Ł"=>tempRate p Xh y
lemma table_env(p:BudgetPoint)(G:Gauge): RG.Envelope (tables G p y o t a n₀):= RG.Envelope.sum (Finset.univ:Finset I) (fun i V=>a i*raiseX G p y n₀ V (t i) (o i)) fun i=> (Envelope.const _).mul (by
    unfold raiseX loader; split; · exact (launch_env ..).mul (launch_env ..)
    exact launch_env ..)
lemma table_gauge {V:Gauge}(p:BudgetPoint): GaugeInvariant (tables V p y o t a n₀):=by
 intro k X; exact Finset.sum_congr rfl fun i _=> by unfold raiseX; rw [show (fun b=> solicit V p y (t i b) (o i b) (Lattice.gauge k X))=(fun b=>solicit V p y (t i b) (o i b) X) from funext fun b=>green_Φ V p _ _ y k X]
lemma turnTable (s:Signed)(b:Site n): tables G p y o t a n₀ ∘ pull s b=tables G p y (fun i j=> affine s b (o i j)) (fun i j=> s*t i j) a n₀:=funext fun V=>Finset.sum_congr rfl fun i _=> by unfold raiseX; simp_rw [solic_pull]
lemma table_smooth : ContDiff ℝ 1 (tableZ G q Xh y o t a n₀):= ContDiff.sum (fun i _=> contDiff_const.mul (by unfold raiseZ loader; split; exact ((Υ₀).chalk_smooth ..).mul ((Υ₀).chalk_smooth ..); exact (Υ₀).chalk_smooth ..))
lemma table_cost(p1:BudgetPoint){k:ℝ}(e:∀i, |a i| ≤ k)(V:Altar G n): |tableZ G q Xh y o t a n₀ V|≤ Fintype.card I*k * (tempRate p1 Xh y)^2:=by
 refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>k*(tempRate p1 Xh y)^2) (fun i _=> ?_)).trans_eq ?_)
 next i _=> rw [abs_mul]; exact mul_le_mul (e i) (grainD (rate_at (G:=G) Xh y p1).1 (fun j=> (((Υ₀).chalk_bound q y (t i j) (o i j) (x:=V))).trans (rate_at Xh y p1).2.1)) (abs_nonneg _) ((abs_nonneg _).trans (e i))
 rw [sum_const,card_univ,nsmul_eq_mul]; ring
end
end Risa
end YM.Gleam.Luster
