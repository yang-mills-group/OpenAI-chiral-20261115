import Ridgetop.LoomV
import Ridgetop.SixPower
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
local notation "Γ"=> ((Fintype.card G.ColorIndex):ℝ)
local notation "Sx"=> stamen B P n
local notation "μ*"=> stdGaussian Sx
variable {q}
abbrev wingN:ℝ:= (3*Γ^2)*(Γ*(15*tug q^ (6:ℕ)))
abbrev tpack(x:Sx):ℝ:= ‖heeled (G:=G) (q:=q) o i x.val‖^6
lemma tpack_h:Continuous (tpack B P o i):=by unfold tpack; exact (((can q _ _).comp continuous_subtype_val).norm.pow 6)
abbrev powbox(x:Sx):ℝ:= (3*Γ^2)*(∑ j:G.ColorIndex,ePower B P o i j 6 x)
lemma riverbound(x:Sx):tpack B P o i x ≤ powbox B P o i x:=styles _
include hx L
lemma powbox_int:Integrable (powbox B P o i) μ*:=by unfold powbox; exact (integrable_finsetSum _ (fun _ _=>loc_int B P L _ _ _ hx _)).const_mul _
lemma tpack_int:Integrable (tpack B P o i) μ*:=by
 apply (powbox_int B P L o i hx).mono' (tpack_h B P o i |>.aestronglyMeasurable)
 exact Filter.Eventually.of_forall fun x=> (le_of_eq (Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 6))).trans (riverbound B P o i x)
lemma relish: (∫ x:Sx,tpack B P o i x∂ μ*) ≤ @wingN G q:=by
 apply (integral_mono (tpack_int B P L o i hx) (powbox_int B P L o i hx) (riverbound B P o i)).trans
 unfold powbox wingN
 rw [integral_const_mul,integral_finsetSum]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [show Γ * (15*tug q^6)=∑ _j:G.ColorIndex, 15*tug q^6 from (by simp)]; exact sum_le_sum fun _ _=> grazed B P L _ _ _ hx
 exact fun _ _=> loc_int B P L _ _ _ hx _
#print axioms relish
end Ridgetop
end Risa
end YM.Gleam.Luster
