import GaugeFieldConstruction.CasquetteMars
/-!
 # complete quotient orientation. Physical fields proof later
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
-- without conservation
variable (p Y)
lemma uplinkMars {d e:ℕ}(h:d≤e)(A:FlyerMars d)(x:A ∈ (T).null d) : ΛRiseMars h A ∈ (T).null e:=by
 refine ((T).criterion e (ΛRiseMars h A)).mpr ?_; intro n i p' hp; change (T).read p' _=0; rw [doorsαMoon] -- does not match
 exact ((T).criterion d A|>.mp x) n i p' hp
lemma inclinMars (d:ℕ)(A:FlyerMars d)(x:A ∈ (T).null d)(a:CompassMars) :ΛSlopeMars d a A ∈ (T).null (d+1):=by
 refine ((T).criterion _ (ΛSlopeMars d a A)).mpr ?_; intro n i p' hp
 have he:((fun y=>(BellTableMars p Y).read y (Fin.cons (PostMars d A) i))=ᶠ[𝓝 p'] (fun _=> 0)):= EqOn.eventuallyEq_of_mem (((T).criterion d A|>.mp x) n i) ((conf_open _).mem_nhds hp)
 rw [guidePriceMars p Y _ _ _ hp,GermD _ he]; simp [Analysis.D]
noncomputable def arcRiseMars {d e:ℕ}(h:d≤e): (T).Field d →ₗ[ℂ] (T).Field e:= ((T).null d).liftQ (((T).project e).comp (ΛRiseMars h)) (fun i z=>by
    exact (Submodule.Quotient.mk_eq_zero _).mpr (uplinkMars p Y h i z))
noncomputable def arcTiltMars (d) (a:CompassMars): (T).Field d →ₗ[ℂ] (T).Field (d+1):= ((T).null d).liftQ (((T).project (d+1)).comp (ΛSlopeMars d a)) (fun i z=>by exact (Submodule.Quotient.mk_eq_zero _).mpr (inclinMars p Y d i z a))
noncomputable def DictumMars : NSF.DiffPlan T where
    rise := arcRiseMars p Y
    deriv d i:=arcTiltMars p Y d (i,false)
variable {p Y}
-- quotient. handy head projection read
variable (H:FirstPackMars p Y)
include H
lemma AcostMoon {x:Points (n+1)}(hx:x∈conf _)(a:ℕ)(v:ΡeaderMars.Ref a)(w:Fin n→ΡeaderMars.Token) :
    (T).useAt T x (Fin.cons ⟨a,(T).project a v⟩ ((T).classTokens ∘ w))=(T).read x (Fin.cons (PostMars a v) w):= (T).through (SymHallMars H) _ w hx
omit H in
lemma LiftQtyMars (w:Fin n→(T).Tag): ∃ p':Fin n→ΡeaderMars.Token, w=(T).classTokens ∘ p':=by
    choose V H' using fun i=>(T).onto (w i).1 (w i).2; refine ⟨fun i=>⟨(w i).1,V i⟩,funext (fun i=>?_)⟩; change w i=⟨(w i).1,(T).project (w i).1 (V i)⟩; rw[H' i]
lemma DictRiseMars : (DictumMars p Y).Inclusions T where
    kernels {d} {e} h B {n} x hx w:=by
       obtain ⟨A,rfl⟩:= (T).onto _ B; obtain ⟨q,rfl⟩:=LiftQtyMars w -- rfl direction
       change (T).useAt T x (Fin.cons ⟨_,(T).project _ (ΛRiseMars h A)⟩ _) = _
       rw [AcostMoon H hx, AcostMoon H hx]; exact doorsαMoon ..
lemma DictTiltMars : (DictumMars p Y).Derivatives T where
    kernels d a B {n} x hx w:=by
       obtain ⟨A,rfl⟩:=(T).onto _ B; obtain ⟨q,rfl⟩:= LiftQtyMars w
       change (T).useAt T x (Fin.cons ⟨_,(T).project _ (ΛSlopeMars d (a,false) A)⟩ _) = _; rw[AcostMoon H hx, guidePriceMars p Y _ _ _ hx]; exact GermD _ (((conf_open _).eventually_mem hx).mono (fun y t=>(AcostMoon H t d A q).symm)) -- tune inner
omit H
lemma ΛFrameLum {d e:ℕ}(f:LabelMars d→LabelMars e)(x: FlyerMars d): star (ΛTransportMars f x)= ΛTransportMars f (star x):=by
 have ht(i:LabelMars d): star (coneOneMars e (f i))= coneOneMars e (f i):=by ext1 a; by_cases h:a=f i <;> simp[coneOneMars,h]
 unfold ΛTransportMars; rw [LinearMap.sum_apply,LinearMap.sum_apply, star_sum]; apply sum_congr rfl; intro i p'; simp only [LinearMap.smulRight_apply,LinearMap.proj_apply, star_smul,ht]; rfl
lemma ΛOrbitLum {d e:ℕ}(s:Signed)(f:LabelMars d→ LabelMars e)(g:LabelMars d→LabelMars e)(h:∀ i,arcActsMars e s (f i)= g (arcActsMars d s i))(x:FlyerMars d):
    writeArcMars e s (ΛTransportMars f x)=ΛTransportMars g (writeArcMars d s x):=by
    change ((writeArcMars e s).comp (ΛTransportMars f)) x=((ΛTransportMars g).comp (writeArcMars d s)) x
    rw [lumMars,lumMars]; apply sum_congr rfl; intro i p'; rw [LinearMap.comp_apply,LinearMap.comp_apply,ΛTAtMars,coneOneMars, writeArcOneMars, h]; change _=x i • _; rw [writeArcOneMars,ΛTAtMars]
lemma riseLumMars {d e:ℕ}(s:Signed) (h:d≤e)(i:LabelMars d) : arcActsMars e s (liftLaMars h i)=liftLaMars h (arcActsMars d s i):=by
 simp only [arcActsMars,liftLaMars,ChaseMars, Function.comp_apply,Equiv.symm_apply_apply]; rfl
lemma tiltLumMars (d s) (a:CompassMars)(i:LabelMars d): arcActsMars (d+1) s (pushLaMars a i)=pushLaMars (revolveMars s a) (arcActsMars d s i):=by
    simp only [arcActsMars, Function.comp_apply,pushLaMars,ChaseMars,Equiv.symm_apply_apply]; congr 1
    apply Prod.ext (by rfl); apply congrArg (fun v=> (⟨_,v⟩:TrailsMars (d+1))) -- tune binder metav
    ext1 j; refine Fin.cases ?_ (fun i=>?_) j <;> rfl
-- actual negative counterpart quotient.
include H
lemma arcπMoonMars {d:ℕ}(a : Axis)(A: FlyerMars d): (T).project (d+1) (ΛSlopeMars d (a,true) A)= - (T).project (d+1) (ΛSlopeMars d (a,false) A):=by
    rw [←map_neg]; apply (T).field_ext (SymHallMars H); intro n q x hx; obtain ⟨w,rfl⟩:=LiftQtyMars q
    rw [AcostMoon H hx,AcostMoon H hx]; let B:=ΛSlopeMars d (a,false) A
    change _=(T).read x (Fin.cons (PostMars (d+1) (-B)) w); rw [show (T).read x (Fin.cons (PostMars (d+1) (-B)) w)= -((T).read x (Fin.cons (PostMars _ B) w)) from (((T).injectFront w x _).map_neg (ΛSlopeMars d (a,false) A))]; unfold B; rw[guidePriceMars _ _ _ _ _ hx,guidePriceMars _ _ _ _ _ hx]; unfold D; exact map_neg (fderiv ℝ _ x) (direction 0 a)
lemma MonsMars {d:ℕ}(a:Axis)(s:Signed)(A: FlyerMars d): ∑ j:Axis,(s.matrix j a : ℂ) • ((T).project _ (ΛSlopeMars d (j,false) A)) = (T).project _ (ΛSlopeMars d (revolveMars s (a,false)) A):=by
 rw [Finset.sum_eq_single (s.perm a)]
 · rw[Signed.matrix_at]; cases h:s.flip a
   · simp [revolveMars, h]
   simp [revolveMars,h]; exact (arcπMoonMars H (s.perm a) A).symm
 · intro i _ e; simp [Signed.matrix_at,Ne.symm e]
 simp
lemma DictRollMars: (DictumMars p Y).Orientation (BellSpinMars H) where
 realInc h x:=by
    obtain ⟨y,rfl⟩:= (T).onto _ x; exact congrArg ((T).project _) (ΛFrameLum (liftLaMars h) y)
 realDer d a B:=by
    obtain ⟨y,rfl⟩:= (T).onto _ B; exact congrArg ((T).project _) (ΛFrameLum _ y)
 mirrorInc h s x:=by
    obtain ⟨y,rfl⟩:= (T).onto _ x; exact congrArg ((T).project _) (ΛOrbitLum s (liftLaMars h) _ (riseLumMars s h) y)
 mirrorDer d b s B:=by
    obtain ⟨y,rfl⟩:= (T).onto _ B
    exact (congrArg ((T).project _) (ΛOrbitLum s (pushLaMars (b,false)) _ (tiltLumMars d s (b,false)) y)).trans (MonsMars H b s (writeArcMars d s y)).symm
#print axioms DictRollMars
#print axioms DictTiltMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
