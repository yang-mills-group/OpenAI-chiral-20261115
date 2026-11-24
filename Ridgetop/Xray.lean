import Ridgetop.Traces
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
local notation "Sx"=> stamen B P n
local notation "μ*"=>stdGaussian Sx
variable (o b:Site n)(hx:0< δ)(O:Bid.Sworn H n G)
include hx L
local notation "Γ"=> ((Fintype.card G.ColorIndex):ℝ)
lemma groin(a y:ℝ)(i m:PlaqAxes):(∫ t:Sx,(a*stampB q o i t.val)*(y*stampB q b m t.val)∂μ*)= a*y*(Γ^2*ym (H:=H) o i*ym (H:=H) b m+2*Γ*(finger H (loadM o i) (loadM b m))^2):=by
 rw [← skyB B P L o i hx]
 unfold clouds; simp_rw [show ∀ r s:ℝ,(a*r)*(y*s)=(a*y)*(r*s) from fun _ _=> by ring,integral_const_mul]
include O
include B P
lemma spending:(∑ i:PlaqAxes,dye i*(Γ * ym (H:=H) o i))=0:=by
 rw [← noneV B P o L O]; unfold clouds imagine; rw [integral_finsetSum]; swap; · intro i _; exact (starB B P L o i hx).const_mul _
 simp_rw [integral_const_mul]; refine sum_congr rfl fun i _=>?_ ; exact congrArg _ (grainS B P L o i hx).symm
-- product law
abbrev sconeR(H:Bed)(o b:Site n):ℝ:=∑ i:PlaqAxes,∑ j:PlaqAxes,dye i *dye j*(finger H (loadM o i) (loadM b j))^2
lemma pewter :clouds B P (fun t=> imagine q o t* imagine q b t)=2*Γ*sconeR H o b:=by
 unfold clouds imagine; simp_rw [Finset.sum_mul,Finset.mul_sum]
 have Hm(i m:PlaqAxes): Integrable (fun t:Sx=> (dye i*stampB q o i t.val)*(dye m*stampB q b m t.val)) μ*:=by
    simp_rw [show ∀ i m:PlaqAxes,∀ r s:ℝ,(dye i*r)*(dye m*s)=(dye i*dye m)*(r*s) from fun _ _ _ _=> by ring]
    exact (moon B P L o i hx b m).const_mul _ -- order check hx before b
 rw [integral_finsetSum]; swap; · intro i _; exact integrable_finsetSum _ fun m _=>Hm i m
 have hr(i:PlaqAxes): (∫ t:Sx,∑ m:PlaqAxes,(dye i*stampB q o i t.val)*(dye m*stampB q b m t.val)∂μ*) = ∑ m:PlaqAxes,dye i*dye m*(Γ^2*ym (H:=H) o i*ym (H:=H) b m+2*Γ*(finger H (loadM o i) (loadM b m))^2):=by
    rw [integral_finsetSum]; simp_rw [groin B P L o b hx]; exact fun m _=>Hm i m
 simp_rw [hr]
 have h(i m:PlaqAxes): dye i*dye m*(Γ^2*ym (H:=H) o i*ym (H:=H) b m+2*Γ*(finger H (loadM o i) (loadM b m))^2)=(dye i*(Γ*ym (H:=H) o i))*(dye m*(Γ*ym (H:=H) b m))+2*Γ*(dye i*dye m*(finger H (loadM o i) (loadM b m))^2):=by ring
 simp_rw [h,sum_add_distrib,← Finset.mul_sum,spending B P L b hx O]; trace_state; simp
#print axioms pewter
end Ridgetop
end Risa
end YM.Gleam.Luster
