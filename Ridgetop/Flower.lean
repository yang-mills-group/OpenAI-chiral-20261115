import Ridgetop.Origin
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
attribute [local instance] Gauge.frobInner
private lemma sunlight (a b:Lattice.Step)(o:Site n)(x:fieldDir G n 1) : linkSum (collect G x) o (oriented a b)= (flag a * flag b) • linkSum (collect G x) (atFace o a b) (square a.dir b.dir):=by
 -- from YM/AnalyticBridge/Lines
  rcases a with ⟨a,_|_⟩ <;> rcases b with ⟨b,_|_⟩ <;>
    simp [oriented,square, atFace, StressFlux.flag, posDir, negDir, Lattice.Step.rev, Lattice.Step.vec, Lattice.Step.used, Exterior.linkSum, add_right_comm o, sub_eq_add_neg] <;> abel_nf
variable (o:Site n)(i:PlaqAxes)
local notation "s" => i.val.1
local notation "d₀" => i.val.2
open scoped Classical
abbrev pla (u v:Bool) : Body 2 n:= (atFace o (digs s u) (digs d₀ v),plaquette i)
private lemma flour (u v:Bool)(x:fieldDir G n 1): HasDerivAt (fun t:ℝ=>plate (represent (t • x)) o (digs s u) (digs d₀ v)) ((flag (digs s u) * flag (digs d₀ v)) • faceCurl (atFace o (digs s u) (digs d₀ v),i) x) 0:=by
 have he:= curvature_of_hasDerivAt (Push.travell (oriented (digs s u) (digs d₀ v)) o x)
 rw [sunlight] at he; exact HasDerivAt.congr_deriv he (by unfold faceCurl; rw [←fundamental]; rfl)
local notation "κ*"=>(4:ℝ)⁻¹
abbrev cosmos{E:Type*}[AddCommGroup E][Module ℝ E](f:Bool→Bool→E):E:=κ* • ((f false false + f false true)+(f true false+f true true))
lemma esteem (x:fieldDir G n 1): salt o i x=cosmos (fun u v=>dColor G n 1 x (pla o i u v)):= by
 have he (u v:Bool):=flour o i u v x
 have hf:= (((he false false).sub (he false true)).sub ((he true false).sub (he true true))).const_smul κ*
 have h:HasDerivAt (fun t:ℝ=>petals (represent (t • x)) o i) (cosmos (fun u v=>dColor G n 1 x (pla o i u v))) 0:=by
    refine HasDerivAt.congr_deriv hf ?_
    simp only [digs,StressFlux.flag,↓reduceIte, Bool.false_eq_true, one_mul,mul_one,neg_mul_neg,one_smul,neg_one_smul,sub_neg_eq_add,cosmos,pla,faceCurl]
    module
 exact (hiker_d o i x).unique h
abbrev grainM : form 2 n:=cosmos (fun u v=>Pi.single (pla o i u v) (1:ℝ))
abbrev loadM : form 1 n:=(d 1 n).transpose*ᵥgrainM o i
lemma gateP(x:form 2 n):dotProduct (grainM o i) x=cosmos (fun u v=>x (pla o i u v)):=by unfold grainM cosmos; simp; ring
lemma gateL(x:form 1 n):dotProduct (loadM o i) x=cosmos (fun u v=>(d 1 n *ᵥx) (pla o i u v)):=by rw [dotProduct_comm,dotProduct_transpose_mulVec,gateP] -- loadM not exposed rw
lemma estate_tick(x:fieldDir G n 1)(j:G.ColorIndex):salt o i x j=dotProduct (loadM o i) (parts G 1 x j):=by
 rw [esteem,gateL]; rfl
#print axioms estate_tick
end Ridgetop
end Risa
end YM.Gleam.Luster
