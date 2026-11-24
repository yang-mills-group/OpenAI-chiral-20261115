import GaugeFieldConstruction.FabreLuneMars
/-!
 # (132) authentic within actual FirstPack and cost T.
 Signed orientation on principal pi all orders. preserve test estim for later improvement projection
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
namespace FirstPackMars
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y))
open Loft
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg


-- (132)
abbrev CalendarMoon (T:Ortho) (x:Points n):= NSF.Points.move T x
lemma calend_oneMars (x:Points n): CalendarMoon 1 x=x:=PiLp.ext (fun i=>Ortho.move_one (x i))
lemma calend_mulMars (a b:Ortho)(x:Points n):CalendarMoon (a*b) x=CalendarMoon a (CalendarMoon b x):=PiLp.ext fun i=>Ortho.move_mul a b (x i)
abbrev motionMoonMars (a:SO)(x:Points n):= CalendarMoon a.val x
def SpherePulseMars (a:SO):Prop:=∀ (n:ℕ)(F:Fin n→ΧiMars)(x:Points n), x∈conf n→TerraMars p Y (compassPiMars p a ∘ F) (motionMoonMars a x)=TerraMars p Y F x
lemma sphereOneMars : SpherePulseMars (p:=p) (Y:=Y) 1:=fun n F x _=> congrArg₂ (TerraMars p Y) (funext fun i=> sailOneMars p _) (calend_oneMars x)
lemma WindyMissionMars(a b:SO)(x:Points n): motionMoonMars (a*b) x=motionMoonMars a (motionMoonMars b x):=calend_mulMars a b x
lemma missionMulMars (a b:SO)(u':SpherePulseMars (p:=p) (Y:=Y) a)(v:SpherePulseMars (p:=p) (Y:=Y) b): SpherePulseMars (p:=p) (Y:=Y) (a*b):=by
 intro n F x hx; rw [WindyMissionMars]; rw [show (compassPiMars p (a*b)) ∘ F= (compassPiMars p a) ∘ ((compassPiMars p b) ∘ F) from funext fun i=>sailMulMars p _ _ _, u' _ _ (motionMoonMars b x) (NSF.Points.move_in _ hx), v _ F x hx]
lemma PiFlowCancelMars(a:SO)(F:Fin n→ΧiMars): (compassPiMars p a) ∘ ((compassPiMars p a⁻¹) ∘ F)=F:=by
 funext i; simp only [Function.comp_apply]; rw [←sailMulMars, mul_inv_cancel,sailOneMars]
lemma MissionInvMars (a:SO)(v:SpherePulseMars (p:=p) (Y:=Y) a):SpherePulseMars (p:=p) (Y:=Y) a⁻¹:=by
 intro n F x hx; have h:=v n (compassPiMars p a⁻¹ ∘ F) (motionMoonMars a⁻¹ x) (NSF.Points.move_in _ hx)
 rw[PiFlowCancelMars,← WindyMissionMars,mul_inv_cancel,show motionMoonMars 1 x=x from calend_oneMars x] at h; exact h.symm
include H G
lemma ArcWitnessMars (K:Ortho.Skew)(s:ℝ):SpherePulseMars (p:=p) (Y:=Y) (Angles.rise K s):=by
 intro n F x hx; let f (u:ℝ):= TerraMars p Y (compassPiMars p (Angles.rise K u) ∘ F) (motionMoonMars (Angles.rise K u) x); have h(u):HasDerivAt f 0 u:=VenusRiseMars H G u x hx F K
 change f s= _; rw [is_const_of_deriv_eq_zero (fun s=>(h s).differentiableAt) (fun s=>(h s).deriv) s 0]; unfold f; rw [show Angles.rise K 0=1 from Subtype.ext (YM.Work.A13.oneParameter_zero _)]; exact sphereOneMars _ _ x hx
lemma VitaPiiotMars (s:SO): SpherePulseMars (p:=p) (Y:=Y) s:= SO_compute (p:=SpherePulseMars (p:=p) (Y:=Y)) _ (ArcWitnessMars H G) sphereOneMars missionMulMars MissionInvMars
omit H G
-- sign normalization
variable (p)
lemma LedgerBridgeMars (g:SO)(x): compassPiMars p g x= let K:=p.path.caller four; K.c (ledger p.dawn.d four g (K.c.symm x)):=rfl
lemma PiContinueMars (A:ΧiMars): Continuous (fun s:SO=> FreightMars ((compassPiMars p) s A)):=by
 apply continuous_pi; intro i; let K:=p.path.caller four; let Z: grainMars→ₗ[ℂ]ℂ:=LinearMap.proj (φ:=fun _ : SpeckMars=> ℂ) i
 exact Stage.continu p.dawn.d (K.c.symm A) (Z ∘ₗ FreightMars.toLinearMap ∘ₗ K.c.toLinearMap)
lemma PiProperMoon (s:Signed)(h: signBit s=false)(x:ΧiMars): compassPiMars p (Stage.signMot s h) x=spinFrame four s x:=by
 let A:=p.path.caller four
 exact (p.path.costly₁ s h four (A.c.symm x)).trans (congrArg (spinFrame four s) (A.c.apply_symm_apply x))
lemma shadePiMoon (s : SO) (x:ΧiMars): compassPiMars p s (Calibration.shade four x)=Calibration.shade four (compassPiMars p s x):=by
 let A:=p.path.caller four
 obtain ⟨x,rfl⟩:=A.c.surjective x
 rw[←A.charge]; change A.c (ledger _ _ _ (A.c.symm _))=Calibration.shade _ (A.c (ledger p.dawn.d four s (A.c.symm (A.c x))))
 rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply,← Stage.shade_moves, A.charge]
lemma PiiotLieFeelMars (s:Signed)(K:Ortho.Skew)(v:ΧiMars):spinFrame four s (p.path.pi K four v)=p.path.pi (conjS s.ortho K) four (spinFrame four s v):=by
 let F:=p.path.caller four; obtain ⟨v,rfl⟩:= F.c.surjective v
 rw[← F.h, show p.path.pi K four (F.c v) = _ from p.path.turns K four v, ← F.h, show p.path.pi _ four (F.c _) = _ from p.path.turns (conjS s.ortho K) four _]; exact congrArg F.c (sooner p.dawn.d K s v).symm
noncomputable def HueTurnsMars (s: Ortho): SO→* SO where
 toFun g:=⟨s*g.val*s⁻¹,Stage.controls s _ g.property⟩
 map_one':= Subtype.ext (by simp)
 map_mul' x y:=Subtype.ext (by simp [mul_assoc])
lemma HueBudgetMars (s:Ortho)(K:Ortho.Skew)(t):HueTurnsMars s (Angles.rise K t)=Angles.rise (conjS s K) t:=Subtype.ext (Stage.conjugates s K t)
lemma DutyPiiotMars (s:Signed) (a:SO)(v:ΧiMars): spinFrame four s (compassPiMars p a v)= compassPiMars p (HueTurnsMars s.ortho a) (spinFrame four s v):=by
 let U:= (compassPiMars p).comp (HueTurnsMars s.ortho)
 apply LinearMap.congr_fun (show spinFrame four s ∘ₗ compassPiMars p a=U a ∘ₗ spinFrame four s from ?_) v
 refine @Stage.follows ΧiMars ΧiMars _ _ _ _ _ _ (fun Ω=> p.path.pi Ω four) U (fun Ω => p.path.pi (conjS s.ortho Ω) four) (fun u a t=>sailPiMars p a u t) ?_ (spinFrame four s) (fun u=>LinearMap.ext fun i=> PiiotLieFeelMars p s u i) a
 intro K b t; unfold U; simp only [MonoidHom.comp_apply,HueBudgetMars]; exact sailPiMars p _ _ t
lemma DayFlavorMars (s:SO)(V: Flavor)(v): compassPiMars p s (flavors four V v)= flavors four V (compassPiMars p s v):=by
 symm; apply LinearMap.congr_fun (show flavors four V ∘ₗ (compassPiMars p s)= (compassPiMars p s) ∘ₗ flavors four V from ?_) v
 apply @Stage.follows ΧiMars ΧiMars _ _ _ _ _ _ (fun Ω=>p.path.pi Ω four) _ (fun Ω=>p.path.pi Ω four) (fun a b t=>sailPiMars p b a t) (fun a b t=>sailPiMars p b a t) (flavors _ _) (fun u=> LinearMap.ext (fun x=> (((p.path.paid u).guard p.clarity.canny).moon V four x).symm))
#print axioms VitaPiiotMars
#print axioms DutyPiiotMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
