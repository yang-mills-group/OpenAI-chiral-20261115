import Ridgetop.LoomV
import Risa.Cultural
import Compass.Prime
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 305000
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
namespace Ridgetop
open CF.Compass _root_.Factory
open scoped RealInnerProductSpace
variable (q) (o:Site n)(i:PlaqAxes)(j:G.ColorIndex)(hx:0 <δ)
abbrev stampB(o:Site n)(i:PlaqAxes)(t:Altar G n):ℝ:=‖(@heeled n G q o i t)‖^2
abbrev dye(i:PlaqAxes):ℝ:= (decor i:ℝ)
lemma dye_t(i:PlaqAxes): |dye i|≤1:=by unfold dye CF.Compass.decor; split_ifs <;> norm_num
abbrev imagine(o:Site n)(t:Altar G n):ℝ:=∑ i:PlaqAxes,dye i*stampB q o i t
local notation "🎱"=> dye
local notation "Sx"=> stamen B P n
local notation "μ*"=> stdGaussian Sx
lemma gild : Continuous (@imagine n G q o):=by unfold imagine stampB; apply continuous_finsetSum; exact fun i _=>continuous_const.mul ((can q _ _).norm.pow 2)
variable {q}
lemma imagery(t: Signed)(p:Site n)(x:fieldDir G n 1)(i:PlaqAxes): stampB q o i (tiler B P (bank t p x))=stampB q (affine t p o) ((PlaqAxes.transform t) i) (tiler B P x):=by unfold stampB; simp only [heeled_tiler,swivelV,reframe_norm]
lemma noneV(L:Floor H q n δ w)(O:Bid.Sworn H n G): clouds B P (imagine q o)=0:=by
 let t:=CF.Pec.X side01; let a:Site n:=o-t.act o
 have hx(tV:fieldDir G n 1): imagine q o (tiler B P (bank t a tV))= -imagine q o (tiler B P tV):=by unfold imagine; simp_rw [imagery,show affine t a o=o from (by unfold affine a; abel)]; apply unrule t quad_anchor (tax_s _ _ (by decide:(0:Axis)≠1)) (fun i=> stampB q o i (tiler B P tV))
 have he:=cover_calms t a B P L O _ (fun i:Altar G n=> -imagine q o i) (gild q o) hx; unfold clouds at *; rw [integral_neg] at he; linarith only [he]
abbrev packB(o:Site n)(i:PlaqAxes)(x:Sx): ℝ:=stampB q o i x.val
lemma stamp_cost(x:Sx): stampB q o i x.val= ∑ j:G.ColorIndex,ePower B P o i j 2 x:=EuclideanSpace.real_norm_sq_eq _
include hx L
lemma starB : Integrable (packB B P o i) μ*:=by unfold packB; simp_rw [stamp_cost]; exact integrable_finsetSum _ fun _ _=> loc_int B P L _ _ _ hx _
lemma moon(x:Site n)(m:PlaqAxes):Integrable (fun t=> stampB q o i t.val * stampB q x m t.val) μ*:=by
   simp_rw [stamp_cost,Finset.sum_mul,Finset.mul_sum]
   exact integrable_finsetSum _ (fun x _=> integrable_finsetSum _ (fun i _=>loc_mix B P L _ _ _ hx _ _ _ _ _))
abbrev ym (o:Site n)(i:PlaqAxes):ℝ:=finger H (loadM o i) (loadM o i)
local notation "c₀"=> ((Fintype.card G.ColorIndex):ℝ)
lemma grainS : (∫ x:Sx, packB B P o i x∂μ*)=c₀* ym (H:=H) o i:=by
 unfold packB; simp_rw [stamp_cost]; rw [integral_finsetSum]
 · unfold ePower; simp_rw [interests B P L o i _ hx,twice]; -- toDual.norm
   unfold webV; simp_rw [LinearIsometryEquiv.norm_map,←real_inner_self_eq_norm_sq,accounts B P L _ _ _ hx]; simp [ym]
 exact fun _ _=>loc_int B P L _ _ _ hx _
lemma skyB{x:Site n}{m:PlaqAxes}: clouds B P (fun t=>stampB q o i t*stampB q x m t)=c₀^2*ym (H:=H) o i*ym (H:=H) x m+2*c₀*(finger H (loadM o i) (loadM x m))^2:=by
 unfold clouds; simp_rw [stamp_cost,Finset.sum_mul,Finset.mul_sum]
 rw [integral_finsetSum]; swap; · intro j _; exact integrable_finsetSum _ (fun k _=>loc_mix B P L _ _ _ hx _ _ _ _ k)
 have gr(j:G.ColorIndex): (∫ t:Sx,∑ k:G.ColorIndex, ePower B P o i j 2 t * ePower B P x m k 2 t∂μ*)= ∑ k:G.ColorIndex, ∫ t:Sx,ePower B P o i j 2 t*ePower B P x m k 2 t∂μ*:= integral_finsetSum _ (fun k _=>loc_mix B P L o i j hx 2 2 x m k)
 simp_rw [gr]; unfold ePower
 simp_rw [fibre_pair B P L _ _ _ hx]
 simp [sum_add_distrib,ym]; ring
#print axioms grainS
#print axioms skyB
end Ridgetop
end Risa
end YM.Gleam.Luster
