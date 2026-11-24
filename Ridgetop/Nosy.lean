import Ridgetop.Hess
import YM.SU5.Circuit.Lark
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
open Head.Brecht Circuit
open scoped RealInnerProductSpace
include L
private lemma cradle(o:Site n)(i:PlaqAxes)(j:G.ColorIndex)(he:0<δ):fibreR B P o i j=cosmos (fun a b=> trill B P j (pla o i a b)):=by
   apply ext_inner_right ℝ -- requires hx L
   intro x; obtain ⟨y,rfl⟩:= song B P x
   change inner ℝ (fibreR B P o i j) _=_; rw [← InnerProductSpace.toDual_apply_apply]; change _root_.Factory.webV (fibreR B P o i j) ((tiler B P).rangeRestrict y) = _
   rw [← interests B P L o i j he]; change heeled (q:=q) (G:=G) _ _ (tiler B P y) j = _
   rw [heeled_tiler,esteem]; unfold cosmos; simp_rw [real_inner_smul_left,inner_add_left,praises]; rfl
variable (z w':Cover)(i m:PlaqAxes)(hx:0<δ)
local notation "S₀"=> stamen B P n
local notation "T" z=> wrap n z
variable (G)
-- real lift combos using cosmos works ℂ since module ℝ, inner linear
abbrev boreV (H:Bed)(x y:Site n)(i m:PlaqAxes):ℂ:=cosmos (fun a b=> cosmos (fun u v=>rimble n H (pla x i a b) (pla y m u v)))
private lemma combo{V:Type*}[NormedAddCommGroup V][InnerProductSpace ℝ V](f g:Bool→Bool→V){w:Bool→Bool→ Bool→Bool→ℂ}(h:∀a b c d,(inner ℝ (f a b) (g c d):ℂ)=w a b c d):
 ((inner ℝ (cosmos f) (cosmos g)):ℂ)=cosmos (fun i j=>cosmos (w i j)):=by
 unfold cosmos; simp_rw [real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right]; push_cast; simp_rw [h]; simp only [Complex.real_smul]; push_cast; simp_rw [mul_add]
include B P hx
-- fix Lie coordinate j to get sch=1. beam.exact
variable {G}
theorem buds (K:H.covered θ v)(p:0<θ)(V:Floor H q n δ v)(u:G.ColorIndex)(h:Even n.val): (↑(finger H (loadM (wrap n z) i) (loadM (wrap n w') m)):ℂ)=boreV H (wrap n z) (wrap n w') i m:=by
 let x:=wrap n z; let y:=wrap n w'
 have a:=accounts B P L x i u hx y m u; change _ = ite _ (finger H _ _) _ at a; rw [if_pos rfl] at a; change (↑(finger H (loadM x i) (loadM y m)):ℂ)=_
 rw [← a,cradle B P L _ _ _ hx,cradle B P L _ _ _ hx]; apply combo L; intro a b c d; let A:=pla x i a b; let E:= pla y m c d; have hb:=chimes B P V K p u u A E h
 simp_rw [←joy,appraisal] at hb; rw [show (sch (G:=G) u u:ℝ)=1 from if_pos rfl,Complex.ofReal_one] at hb; erw [one_mul] at hb; exact hb
#print axioms mercury
#print axioms chimes
#check ext_inner_right ℝ
#check Complex.real_smul
#check song
end Ridgetop
end Risa
end YM.Gleam.Luster
