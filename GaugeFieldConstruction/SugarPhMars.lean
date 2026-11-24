import GaugeFieldConstruction.CapeSounMars
import GaugeFieldConstruction.StyriaRel.YM.Ward.Sum
/-!
 # parametrized fixed vector coupon, angular derivative. G and Fu are hard unresolved until Analyt step
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable {p:Ticket u C}{Y:AreaQc S}
local notation "T"=> BellTableMars p Y
local notation "M"=> TerraMars p Y
namespace FirstPackMars
-- analysis shell on Points n+1. We'll use all signed.
variable (F: Points (n+1)→ℂ)(f:ContDiffOn ℝ ∞ F (conf (n+1))) (k:Fin n)(Ω:Ortho.Skew)(b:Bulb)
-- scalar quotient: via Pod.Cord etc
include f
lemma soilIntMars (x:Points n) (h:BreatherMars b k x)(R:Payroll n)(a i:Axis):Integrable (fun y:E4=>SoilMars F R b a i (y,x)):=by -- include f
    exact CohortMars _ {x|BreatherMars b k x} (run (LED b a)) (LED b a).c (fun x hx y=>SoilCapMars _ f R b a i x k hx y) (fun x _ y hy=>SoilAreaMars F R b a i y hy x) x h
include f
-- desk delta use K.L continuous linear ungen
abbrev filingMars (w:Points n)(a:Axis):= M4.move Ω.val (w k) a
abbrev ροδMars (i:Axis) : (E4×Points n)→ₗ[ℝ] ℝ:={
 toFun x:= M4.move Ω.val (x.1-x.2 k) i
 map_add' x y:= by dsimp only [Prod.fst_add,Prod.snd_add,PiLp.add_apply]; rw [add_sub_add_comm]; unfold M4.move; rw [map_add]; rfl -- tune
 map_smul' t x:=by dsimp; rw[←smul_sub]; unfold M4.move; rw[map_smul]; rfl }
lemma RollerMars (x:Points n)(h:BreatherMars b k x) (w:Points n)(a i:Axis)(y:E4): Analysis.D (0,w) (SoilMars F (Payroll.desk k Ω) b a i) (y,x)=
    SoilMars (Analysis.D (Points.cons 0 w) F) (Payroll.desk k Ω) b a i (y,x) - (filingMars k Ω w i) • SoilMars F (Payroll.ticket i) b a i (y,x) :=by
 let Z:= SoilMars F (Payroll.ticket i) b a i; let A:= SoilMars F (Payroll.desk k Ω) b a i; let m:=LinearMap.toContinuousLinearMap (ροδMars k Ω i)
 have H (F) (y x): SoilMars F (Payroll.desk k Ω) b a i (y,x)= m (y,x) • SoilMars F (Payroll.ticket i) b a i (y,x):=by
    rw [SoilMars,coatMars,Payroll.angle, ← mul_smul]; exact congrArg (· • _) (mul_comm ..) -- tune
 have He:A= (fun z=>m z • Z z):=funext fun z=> H _ z.1 z.2
 change D _ A (y,x)= _; rw [He, H _ y x]; -- rewrites not rhs first?
 have hp:m (0,w)= -(filingMars k Ω w i):=by
    change M4.move _ ((0:E4)-w k) i=_; rw [zero_sub]; exact congr_arg (fun z:E4=>z i) ((Matrix.toEuclideanLin Ω.val).map_neg (w k))
 have hr: DifferentiableAt ℝ Z (y,x):=(SoilCapMars F f _ _ _ _ x k h y).differentiableAt (by simp)
 have hw: D ((0:E4),w) Z (y,x)=SoilMars (Analysis.D (Points.cons 0 w) F) (Payroll.ticket i) b a i (y,x):= CamDMars b k x h _ _ _ f w y
 rw [←hw, D, fderiv_fun_smul m.differentiableAt hr, m.fderiv]; simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply, hp,neg_smul]; change _+_= _; unfold Analysis.D; abel
lemma spendDeskMars(x:Points n)(h:BreatherMars b k x)(w:Points n)(a i:Axis): Analysis.D w (RyeMars F (Payroll.desk k Ω) b a i) x= RyeMars (Analysis.D (Points.cons 0 w) F) (Payroll.desk k Ω) b a i x - filingMars k Ω w i • RyeMars F (Payroll.ticket i) b a i x:=by
 let G:=D (Points.cons 0 w) F
 have hG:ContDiffOn ℝ ∞ G (conf _):=fun z e=>(dSmooth (m:=∞) ((f _ e).contDiffAt ((conf_open _).mem_nhds e)) _ (by simp)).contDiffWithinAt
 unfold RyeMars; rw [CubicDMars _ {x|BreatherMars b k x} (BreathingMars b k) (run (LED b a)) (LED b a).c (fun x e y=>SoilCapMars F f _ _ _ _ x k e y) (fun x e y hy=>SoilAreaMars F _ b a i y hy x) x h]
 simp_rw [RollerMars F f k Ω b x h]
 rw [integral_sub (soilIntMars G hG k b x h (Payroll.desk k Ω) a i) (show Integrable (fun y:E4=> filingMars k Ω w i • SoilMars F (Payroll.ticket i) b a i (y,x)) from (soilIntMars F f k b x h (Payroll.ticket i) a i).smul (filingMars k Ω w i)), integral_smul]; rfl -- tune scalar order
-- if D not in clock
lemma clockStopMars(x:Points n)(h:BreatherMars b k x)(l:List (Points n))(a i:Axis)(s:∀ v∈l,v k=0): PoolDMars l (RyeMars F (Payroll.desk k Ω) b a i) x= RyeMars (PoolDMars (trailMars l) F) (Payroll.desk k Ω) b a i x:=by
 induction l generalizing x with
 | nil=> rfl
 | cons v l hl=>
    let Z:=PoolDMars (trailMars l) F; have hz:ContDiffOn ℝ ∞ Z (conf _):= fun x hx=> (poolSmMars _ _ _ ((f x hx).contDiffAt ((conf_open _).mem_nhds hx))).contDiffWithinAt
    have hv: PoolDMars l (RyeMars F (Payroll.desk k Ω) b a i)=ᶠ[𝓝 x] (RyeMars Z (Payroll.desk k Ω) b a i):=((BreathingMars b k).eventually_mem h).mono (fun i e=>hl i e (fun t ht=>s t (List.mem_cons_of_mem v ht)))
    rw [poolHeadMars,GermD v hv,spendDeskMars _ hz k Ω b x h, show filingMars k Ω v i=0 from ?_,zero_smul,sub_zero]; try rfl
    unfold filingMars M4.move; rw [s v List.mem_cons_self, map_zero]; rfl
#print axioms clockStopMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
