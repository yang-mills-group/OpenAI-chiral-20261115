import YM.SU5.Regis.Trophy
import YM.SU5.Regis.Visions
import YM.Work.G06.TurnSlot
/-! # Bounded aperture local gauge probes. Jotta smooth HERE on tangent curvature arguments only. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 ProbabilityTheory Submodule
open Gleam Matrix Next.SectorChange.Gaussian
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {n c:Side}{G:Gauge}{H:Bed}{m:ℕ}{η C S v δ : ℝ}{Z:PathData G}{I:Type*}
/-- `t` rotation, transported gauge observable. Choice theorem remembers correspondence on derivative via ray. -/
abbrev skewSlot (G:Gauge)(i:Slot)(t:Signed) := (Work.G06.slot_pull (G:=G) t i).choose
abbrev skewSig (G:Gauge)(i:Slot)(t:Signed) := (Work.G06.slot_pull (G:=G) t i).choose_spec.choose
variable (G)
@[simp] lemma skewSq (i:Slot)(t:Signed): |skewSig G i t|=1:= by
 let r:=skewSig G i t; change |r|=1; rcases (show r=1∨r= -1 from (Work.G06.slot_pull (G:=G) t i).choose_spec.choose_spec.1) with h|h <;> simp [h]
variable {G}
lemma reflects (i:Slot)(t:Signed)(x b:Site n)(V:Config G n): i.atSite (pull t b V) x=skewSig G i t • (skewSlot G i t).atSite V (affine t b x):=by
 rw [Slot.atSite, expandAt_pull]; exact (Work.G06.slot_pull (G:=G) t i).choose_spec.choose_spec.2 _
lemma reflex (i:Slot)(t:Signed)(x b:Site n)(V:Dir G n): faceCurl (slotFace i x) (bank t b V)= skewSig G i t • faceCurl (slotFace (skewSlot G i t) (affine t b x)) V:=by have he:=slot_deriv i x (bank t b V); simp_rw [bank_at, reflects] at he; exact he.unique ((slot_deriv _ _ V).const_smul (skewSig G i t))
variable [Fintype I]
structure Etch (G:Gauge) (I:Type*) [Fintype I] where
 slot : I → Slot
 f : (I→G.Color) → ℝ
 arc : ℝ
 bound(x) : |f x| ≤ arc
 diff : ContDiff ℝ 1 f
 favor : ℝ≥0
 steady : LipschitzWith favor f
-- invariant condition on ridges
 move (x:G.El) (y:I→G.Color) : f (fun i=> G.adjoint x (y i))=f y
namespace Etch
variable (A:Etch G I) (q:Clip)
lemma arc_non : 0 ≤ A.arc:= (abs_nonneg (A.f 0)).trans (A.bound 0)
/-- aperture ρ acts on physical curvatures -/
def portrait (ρ:ℝ)(x: CoverConfig G): ℝ:= A.f (fun i=> ρ • (A.slot i).eval x)
def palette (ρ:ℝ)(t:Signed)(b:Site n)(x:Config G n): ℝ:= A.portrait ρ (expandAt 0 (pull t b x))
variable (ρ:ℝ)(t:Signed)(b:Site n)
lemma pin (x:Config G n): A.palette ρ t b x= A.f (fun i=> ρ • skewSig G (A.slot i) t • (skewSlot G (A.slot i) t).atSite x b):=by
 let p(i:I):= skewSlot G (A.slot i) t; apply congrArg A.f; funext i; change ρ • (A.slot i).atSite _ _= _; rw [reflects,affine, Signed.act_zero,zero_add]
lemma panel_gauge : GaugeInvariant (A.palette ρ t b):=by
 intro u x; rw [pin,pin,←A.move (u b) (fun i=> ρ • _ • (skewSlot G (A.slot i) t).atSite x b)]; apply congrArg A.f; funext i; rw [Slot.atSite,expandAt_gauge, Work.G06.slot_gauge]; simp [Slot.atSite] -- map_smul tune
lemma panel_pull (a:Signed)(w:Site n)(x: Config G n): A.palette ρ t b (pull a w x)=A.palette ρ (a*t) (affine a w b) x:=by rw [palette,pull_pull]; rfl
lemma panel_bound {x}: |A.palette ρ t b x| ≤ A.arc:=A.bound _
lemma panel_smooth : Continuous (A.palette ρ t b):=by simp_rw [funext (A.pin ρ t b)]; refine A.diff.continuous.comp (continuous_pi (fun i=>?_)); unfold Slot.atSite Lattice.expandAt; fun_prop
lemma panel : Envelope (A.palette ρ t b) :=⟨ (A.panel_smooth ρ t b).measurable,A.arc, fun x=> by rw [Real.norm_eq_abs]; exact A.panel_bound ..⟩
variable {ρ t b}
def cup (b:Cell n): Altar G n →ₗ[ℝ] G.Color where
 toFun x:= WithLp.toLp 2 (fun i=> x (b,false,i))
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def river (b:Cell n): Altar G n →ₗ[ℝ] G.Color:=(Real.sqrt q.direct)⁻¹ • cup b
lemma river_now(B:Z.Bounds q η C S)(P:Attached H Z)(b:Cell n)(x:Dir G n): river q b (tiler B P x)=faceCurl b x:=by ext i; change (Real.sqrt q.direct)⁻¹*(Real.sqrt q.direct * faceCurl b x i)=_; rw [inv_mul_cancel_left₀ (Real.sqrt_pos.2 q.quadratic_pos).ne']
lemma river_here (B:Z.Bounds q η C S)(P:Attached H Z)(b:Cell n){r:Ratio c n}{F:Support c}(x y: Dir G n)(p:insideB r F m b):river q b (tiler B P x+ accession B P r F m y)=faceCurl b (x+y):=by
 rw [← river_now q B P b]; ext i; rw [map_add (tiler B P)]; unfold river cup; simp [accession,p]
/-- rate ρ = 1/continuing flux. tangent uses actual ρ*σ for cloud. -/
def chalk (ρ:ℝ)(t:Signed)(b:Site n) (y:Altar G n): ℝ:= A.f (fun i=> ρ • (skewSig G (A.slot i) t) • river q (slotFace (skewSlot G (A.slot i) t) b) y)
def sketch (ρ:ℝ)(b:Site n) (y:Altar G n):ℝ:=A.f (fun i=> ρ • river q (slotFace (A.slot i) b) y)
variable (ρ t b) (B: Z.Bounds q η C S)(P:Attached H Z)(L:Floor H q n δ v) (O:Bid.Sworn H n G)
lemma chalk_bound {x} : |A.chalk q ρ t b x| ≤ A.arc:=A.bound _
lemma sketch_bound {x}: |A.sketch q ρ b x| ≤ A.arc:= A.bound _
lemma chalk_smooth : ContDiff ℝ 1 (A.chalk q ρ t b):= A.diff.comp (contDiff_pi.mpr (fun i=> by
 let g:= river (G:=G) q (slotFace (skewSlot G (A.slot i) t) b)|>.toContinuousLinearMap
 change ContDiff ℝ 1 (fun x=> ρ • skewSig G (A.slot i) t •  g x)
 fun_prop))
lemma sketch_smooth : ContDiff ℝ 1 (A.sketch q ρ b):= A.diff.comp (contDiff_pi.mpr (fun i=> by
 let g:= river (G:=G) q (slotFace (A.slot i) b)|>.toContinuousLinearMap
 change ContDiff ℝ 1 (fun x=> ρ •  g x)
 fun_prop))
lemma chalk_now (x:Dir G n): A.chalk q ρ t b (tiler B P x)=A.sketch q ρ 0 (tiler B P (bank t b x)):=by unfold chalk sketch; simp_rw [river_now q B P,reflex,affine,Signed.act_zero,zero_add]
def muρ (B:Z.Bounds q η C S)(P:Attached H Z)(ρ:ℝ)(n:Side):ℝ:= clouds B P (A.sketch q ρ (0:Site n))
include O L in
lemma paid_chalk : clouds B P (A.chalk q ρ t b)= A.muρ q B P ρ n:= (cover_calms t b B P L O _ _ (A.sketch_smooth q ρ 0).continuous (fun i=>(A.chalk_now q ρ t b B P i).symm)).symm
lemma integr_chalk {E:Submodule ℝ (Altar G n)} : Integrable (fun i:E=> A.chalk q ρ t b i.val) (stdGaussian E):= Regis.bree _ _ ((A.chalk_smooth q ρ t b).continuous.comp continuous_subtype_val|>.measurable) (fun _=> A.chalk_bound ..)
lemma stable_budget : |A.muρ q B P ρ n| ≤ A.arc:=by
 let v(i: stamen B P n):= A.sketch q ρ (0:Site n) i.val; let μ:=stdGaussian (stamen B P n); rw [←Real.norm_eq_abs]; refine (norm_integral_le_of_norm_le (f:=v) (μ:=μ) (g:=fun i:stamen B P n=> A.arc) (integrable_const A.arc) (Eventually.of_forall fun i=>?_)).trans_eq ?_ -- check signature
 · rw [Real.norm_eq_abs]; exact A.bound _
 simp
end Etch
end YM.Regis.Head
#print axioms YM.Regis.Head.Etch.paid_chalk
