import GaugeFieldConstruction.AnubisMars
/-!
 # billing actual wall via references and mint. conservation through each derivative or witness. no conditions yet on equality to selected characters.
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
variable (p:Ticket u C)(Y:AreaQc S)
local notation "T"=> BellTableMars p Y
local notation "M"=> TerraMars p Y
namespace FirstPackMars
-- authoritative Wall price extension multilinear via Test. Need all-germ. simple eq with echelons
lemma gownAddMars (F:Fin n→ΧiMars)(i:Fin n)(x z:ΧiMars): EqOn (M (update F i (x+z))) (fun p=> M (update F i x) p + M (update F i z) p) (conf n):=by
 apply echelonsM (conf n) (Subset.refl _) (conf_open n) _ _ (TerraSm p Y _).continuousOn ((TerraSm p Y _).continuousOn.add (TerraSm p Y _).continuousOn)
 intro t h; change _= t.applyTo (fun p=> M (update F i x) p+ M (update F i z) p); rw [show (t.applyTo (fun p=> M (update F i x) p+ M (update F i z) p))= t.applyTo (M (update F i x))+ t.applyTo (M (update F i z)) from ?_] -- tries matches lhs
 · simp_rw [← BillingMars,pieceLMars,map_add]; rfl
 unfold YM.Test.applyTo; simp_rw [mul_add]; rw [integral_add (t.smearing (TerraSm _ _ _).continuousOn) (t.smearing (TerraSm _ _ _).continuousOn)]
lemma gownScaleMars (F:Fin n→ΧiMars)(i:Fin n)(x:ℂ)(z:ΧiMars): EqOn (M (update F i (x • z))) (fun p=> x*M (update F i z) p) (conf n):=by
 apply echelonsM (conf n) (Subset.refl _) (conf_open n) _ _ (TerraSm p Y _).continuousOn (continuousOn_const.mul (TerraSm p Y _).continuousOn)
 intro t v; change _= t.applyTo (fun p=> x*M (update F i z) p); rw [show t.applyTo (fun i'=>x*M (update F i z) i')=x*t.applyTo (M (update F i z)) from ?_]
 · simp_rw [← BillingMars,pieceLMars,map_smul]; rfl
 unfold YM.Test.applyTo; rw[←integral_const_mul]; congr 1; ext1 i; ring -- binder shadow
noncomputable def linearGownMoon (x:Points n)(h:x∈conf n) : MultilinearMap ℂ (fun _ : Fin n => ΧiMars) ℂ where
 toFun v:= TerraMars p Y v x
 map_update_add' {t} v i a b:=by rw [show t=instDecidableEqFin n from Subsingleton.elim ..]; exact gownAddMars p Y v i a b h
 map_update_smul' {t} v i a b:=by rw [show t=instDecidableEqFin n from Subsingleton.elim ..]; exact gownScaleMars p Y v i a b h
-- derivative gown at Conf. Need lemma manifest update, sign.
lemma cloakDAddMars {E G:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup G][NormedSpace ℝ G](l:List E)(F f:E→G)(U:Set E)(u:IsOpen U)(a:ContDiffOn ℝ ∞ F U)(b:ContDiffOn ℝ ∞ f U): EqOn (PoolDMars l (F+f)) (PoolDMars l F+ PoolDMars l f) U:=by
 induction l with
 | nil=> exact fun i _=>rfl
 | cons i l h=>
    intro x hx
    rw[poolHeadMars,GermD i (h.eventuallyEq_of_mem (u.mem_nhds hx)),Analysis.D, fderiv_add]; rfl
    · exact (poolSmMars l _ _ ((a _ hx).contDiffAt (u.mem_nhds hx))).differentiableAt (by simp)
    exact (poolSmMars l _ _ ((b _ hx).contDiffAt (u.mem_nhds hx))).differentiableAt (by simp)
noncomputable def cloakMMars (x:Points n)(h:x∈conf n)(l:List (Points n)): MultilinearMap ℂ (fun _ : Fin n => ΧiMars) ℂ where
 toFun v:= PoolDMars l (M v) x
 map_update_add' {t} v i a b:= by
    have he:t=instDecidableEqFin n:=Subsingleton.elim ..; subst t
    let F:=M (update v i a); let G:=M (update v i b); have ht:M (update v i (a+b))=ᶠ[𝓝 x] F+G:= EqOn.eventuallyEq_of_mem (gownAddMars p Y v i a b) ((conf_open _).mem_nhds h)
    exact ((pool_germMars x l _ (F+G) ht).self_of_nhds).trans ((cloakDAddMars l F G _ (conf_open _) (TerraSm p Y _) (TerraSm p Y _)) h)
 map_update_smul' {t} v i a b:= by
    have he:t=instDecidableEqFin n:=Subsingleton.elim ..; subst t
    let F:=M (update v i b); let A:= a • ContinuousLinearMap.id ℝ ℂ; have ht: M (update v i (a • b))=ᶠ[𝓝 x] A ∘ F:= EqOn.eventuallyEq_of_mem (gownScaleMars p Y v i a b) ((conf_open _).mem_nhds h)
    exact ((pool_germMars x l _ _ ht).self_of_nhds).trans (poolConvertMars A F _ (conf_open _) (TerraSm p Y _) l x h)
noncomputable def BillLinearMoon (x:Points (n+1))(h:x∈conf (n+1))(d:NSF.Caps n)(v:LabelsMars d)(l:List CompassMars): ΧiMars→ₗ[ℂ] ℂ:= (cloakMMars p Y x h (((l.map (fun i=> ((0:Fin (n+1)),i))) ++ ((τGuideMars v).map CloverHMars)).map guideDirMars)).toLinearMap (Fin.cons 0 (τCoreMars v)) 0
lemma billLinearApplyMars (x:Points (n+1))(h:x∈conf _)(d:NSF.Caps n)(v:LabelsMars d)(l:List CompassMars)(A:ΧiMars): BillLinearMoon p Y x h d v l A= BillHeadMoon p Y v l A x:=by rw [BillLinearMoon,MultilinearMap.toLinearMap_apply,Fin.update_cons_zero]; rfl
-- Mint ANY grade with trail T. 
noncomputable def valueUnoMars : ΧiMars→ₗ[ℂ] (MariaMars→ℂ):= (UniTagMars.exists_rightInverse_of_surjective UniRichMars).choose
lemma valueUnoAtMars (x:ΧiMars): UniTagMars (valueUnoMars x)=x:= LinearMap.congr_fun ((UniTagMars.exists_rightInverse_of_surjective UniRichMars).choose_spec) x
noncomputable def mintUnoMars (d:ℕ)(l:TrailsMars d): ΧiMars→ₗ[ℂ] FlyerMars d:=∑ i:MariaMars,((LinearMap.proj i).comp valueUnoMars).smulRight (coneOneMars d (IndexMars d (i,l)))
lemma mintCoinMars (x:Points (n+1))(h:x∈conf _)(d:NSF.Caps n)(v:LabelsMars d)(b:ℕ)(l:TrailsMars b)(A:ΧiMars):
    (T).read x (Fin.cons (PostMars b (mintUnoMars b l A)) (TiesMars d v)) = BillHeadMoon p Y v (unfoldTrailsMars l) A x:=by
 let Z: FlyerMars b→ₗ[ℂ] ℂ:= (T).injectFront (TiesMars d v) x b
 let F:=BillLinearMoon p Y x h d v (unfoldTrailsMars l)
 rw[←billLinearApplyMars _ _ _ h]; change Z (mintUnoMars b l A)=F A; conv_rhs=> rw[←valueUnoAtMars A,UniAtMars,map_sum]
 rw[mintUnoMars,LinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro i r
 simp only [LinearMap.smulRight_apply,LinearMap.comp_apply,LinearMap.proj_apply,map_smul]; congr 1 -- tune
 change (T).read x (Fin.cons _ (TiesMars d v))=BillLinearMoon _ _ _ _ _ _ _ _
 rw [billLinearApplyMars,ArcBillMoon p Y, show ChaseMars b (IndexMars b (i,l))=(i,l) from (IndexMars b).symm_apply_apply _] -- tune
#print axioms mintCoinMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
