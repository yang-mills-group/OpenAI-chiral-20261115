import GaugeFieldConstruction.MarkaMars
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff FourierTransform InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
variable {n:ℕ} (k:Fin n) (a:Axis)
variable (F:Fin n→ΧiMars)
-- U5 smooth representative
noncomputable def TerraMars :Points n→ℂ:= (springMars p Y F).choose
local notation "Q"=>TerraMars p Y
lemma TerraSm : ContDiffOn ℝ ∞ (Q F) (conf n):=(springMars p Y F).choose_spec.1
lemma TerraAt (x:Points n)(hx:x∈conf n):ContDiffAt ℝ ∞ (Q F) x:=(TerraSm p Y F x hx).contDiffAt ((conf_open _).mem_nhds hx)
lemma TerraWide : EqOn (Q F) (WallMars Y F) (generic n):=(springMars p Y F).choose_spec.2
lemma BillingMars (x:Test n): S.fee n (Calibration.lift four ∘ F) x=x.applyTo (Q F):=by
 rw[Y.price]; apply integral_congr_ae; filter_upwards[rooted_genericQc n] with i t; exact congr_arg _ (TerraWide p Y F t).symm
lemma pieceLMars (b:Fin n)(x:ΧiMars) : S.fee n (Calibration.lift four ∘ update F b x)=S.spot (Calibration.lift four ∘ F) b (Calibration.lift four x):=by
 rw[spot_cost]; congr 1; ext1 i; by_cases h:i=b<;>simp[h]
lemma stratLMars (x:ΧiMars): S.fee (n+1) (Calibration.lift four ∘ Fathom.add x F)= S.tagged (Calibration.lift four ∘ F) (Calibration.lift four x):=by
 rw[tagged_cost]; congr 1; ext1 i; refine Fin.cases ?_ (fun j=>rfl) i; rfl
-- identities licensed on tests
lemma translationMars (i:Axis)(b:Bulb)(t:Test n)(h:b.Works t k):
    - (tilt (direction k i) t).applyTo (Q F)=∑ a:Axis,(lace t (LED b a) (h.cared a)).applyTo (TerraMars p Y (Fathom.add (p.J a i) F)):=by
 let W:=Calibration.lift four ∘ F
 have v:=p.price i (F k) W k t b h
 simp_rw [←BillingMars,stratLMars] -- tune simp_rw
 have T:update W k (Calibration.lift four (F k))=W:=update_eq_self .. -- tune syntactic
 simp_rw [spot_cost,T,Fathom.pays] at v; exact v
noncomputable def TrowMars (p:Ticket u C):Ortho.Skew→ₗ[ℝ] (End ℂ ΧiMars):= C.Y four p.dawn.tect
lemma angularMars (Ω:Ortho.Skew)(b:Bulb)(t: Test n)(h:b.Works t k): t.applyTo (Q (update F k (TrowMars p Ω (F k))))=
    ∑ a:Axis,∑ j:Axis,(testcut (Payroll.desk k Ω) t b h.cared a j).applyTo (TerraMars p Y (Fathom.add (p.J a j) F)):=by
 rw [←BillingMars,pieceLMars]; simp_rw [←BillingMars, stratLMars]
 let W:=Calibration.lift four ∘ F; have v:= C.decree four Ω p.dawn.tect (F k) n W k t b h
 have T:update W k (Calibration.lift four (F k))=W:=update_eq_self ..
 rw[T] at v; exact v
-- poly paid assembled later from purchases
lemma currentMars (t:Test n)(v:Points n): t.applyTo (D v (Q F))= - (tilt v t).applyTo (Q F):=by
 have hi: ContinuousOn (D v (Q F)) (conf n):=fun i ii=> (dSmooth (m:=∞) (TerraAt p Y F i ii) v (by simp)).continuousAt.continuousWithinAt
 unfold YM.Test.applyTo; simp_rw[tilt_pays]
 have he:Integrable (fun y=>fderiv ℝ t y v*TerraMars p Y F y):=by
    have hz:=(tilt v t).smearing (TerraSm p Y F).continuousOn
    simp_rw[tilt_pays] at hz; exact hz
 exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable he (t.smearing hi) (t.smearing (TerraSm p Y F).continuousOn) (fun i _=>diffT t i) (fun i j=> (TerraAt p Y F i (t.tsupport_subset j)).differentiableAt (by simp))
lemma divMars (b:Axis)(x:Points n)(hx:x∈conf n): (∑ j:Axis,D (direction k j) (Q (update F k (p.J j b))) x)=0:=by
 let K(y:Points n)(j:Axis):=D (direction k j) (Q (update F k (p.J j b))) y
 have he (j:Axis):ContinuousOn (fun y=> K y j) (conf n):=fun i ii=> (dSmooth (m:=∞) (TerraAt p Y _ i ii) _ (by simp)).continuousAt.continuousWithinAt
 refine (YM.Test.weak_null (continuousOn_finsetSum Finset.univ (fun j _=>he j))).mp ?_ hx -- sum types
 intro t; unfold YM.Test.applyTo; simp_rw [Finset.mul_sum]; rw [integral_finsetSum _ (fun j _=>t.smearing (he j))]
 change (∑ j:Axis,t.applyTo (D _ (Q (update F k (p.J j b)))))=0
 simp_rw[currentMars,←BillingMars,pieceLMars]
 have hv:= LinearMap.congr_fun (p.conservation (Calibration.lift four ∘ F) k b) t; simp only[LinearMap.sum_apply,Fathom.pays] at hv; exact hv
#print axioms translationMars
#print axioms angularMars
#print axioms divMars
end YM.GaugeFieldConstruction.Ember.Volumetric
