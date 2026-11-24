import GaugeFieldConstruction.KatoaMars
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
def windLMars (s:Signed):Points n→L[ℝ]Points n:= LinearMap.toContinuousLinearMap { toFun:= fun x=> points fun i=>s.ortho.motion (x i), map_add':=fun x y=> PiLp.ext fun i=>s.ortho.motion.map_add _ _,map_smul':=fun x y=> PiLp.ext fun i=>s.ortho.motion.map_smul _ _ }
lemma windAtMars (s:Signed)(x:Points n): windLMars s x=NSF.Points.move s.ortho x:=rfl
lemma windBasisMars (s:Signed)(a:Axis):Ortho.move s.ortho (YM.basis a)=if s.flip a then -(YM.basis (s.perm a)) else YM.basis (s.perm a) :=by
 apply PiLp.ext; intro i; obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [Signed.ortho_move]
 by_cases e:i=a
 · subst i; cases v:s.flip a <;> simp [v]
 cases v:s.flip a <;> cases u:s.flip i<;>simp [e,v,u]
lemma windDirMars (s:Signed)(i:Fin n)(a:CompassMars): guideDirMars (i,revolveMars s a)=windLMars s (guideDirMars (i,a)):=by
 have h(b:Axis):windLMars s (direction i b)=if s.flip b then -(direction i (s.perm b)) else direction i (s.perm b):=by
    ext1 j; change Ortho.move s.ortho _= _; cases p:s.flip b <;> by_cases q:j=i <;> simp [p,q,direction,windBasisMars] <;> exact s.ortho.motion.map_zero
 unfold guideDirMars revolveMars; cases p:a.2<;> cases q:s.flip a.1<;>simp[p,q,h]
-- associate lists under signed supports, all sectors
abbrev wispsMars (s:Signed){d:NSF.Caps n}(ρ:LabelsMars d): LabelsMars d:= fun i=>arcActsMars _ s (ρ i)
lemma WispCoreMars (s:Signed)(d:NSF.Caps n)(ρ:LabelsMars d): τCoreMars (wispsMars s ρ)=spinFrame four s ∘ τCoreMars ρ:=by
 ext1 i; unfold τCoreMars maskMars; simp [wispsMars,arcActsMars,coreActsMars,MActsAtMars]
lemma WispSchedMars (s:Signed)(d:NSF.Caps n)(ρ:LabelsMars d): (τGuideMars (wispsMars s ρ)).map guideDirMars=((τGuideMars ρ).map guideDirMars).map (windLMars s):=by
 rw [PayTurnsMars,payGuideMars]
 congr! 2; ext1 i; unfold maskMars; simp only [wispsMars,arcActsMars, Function.comp_apply, Equiv.symm_apply_apply]; rw [payRailsMars,payRailsMars,List.map_ofFn]; congr 1; exact funext fun j=> windDirMars s i _
-- buckle. mirror signs and translation
variable (H:FirstPackMars p Y)
include H
lemma windPriceMars (s:Signed)(d:NSF.Caps n)(ρ:LabelsMars d)(x:Points n)(h:x∈conf n): ChartPriceMars p Y (wispsMars s ρ) (NSF.Points.move s.ortho x)=ChartPriceMars p Y ρ x:=by
 let k:= windLMars (n:=n) s; let F:=M (spinFrame four s ∘ τCoreMars ρ); unfold ChartPriceMars ΓPriceMars; rw [WispCoreMars, WispSchedMars]
 exact (MirrorPoolMars (M (τCoreMars ρ)) F k k (TerraSm p Y _) (fun i e=>NSF.Points.move_in _ e) (fun i e=> (H.spin s _ i e).symm) (fun i=>k.hasFDerivAt) _ x h).symm
lemma WindTableMars (s:Signed)(d:NSF.Caps n)(v:ChartVuMars d)(x:Points n)(h:x∈conf n): (T).value d (NSF.Points.move s.ortho x) (fun i=> writeArcMars (d i) s (v i))=(T).value d x v:=by
 rw [TaxApplyMars,TaxApplyMars]; symm
 let E:Equiv.Perm (LabelsMars d):= Equiv.piCongrRight (fun i=> SunArcMars (d i) s)
 refine Fintype.sum_equiv E _ _ fun i=> ?_; rw [show E i=wispsMars s i from rfl, windPriceMars H s d i x h]; congr 1; apply prod_congr rfl; intro j _; change v j _= v j (arcActsMars _ s⁻¹ (arcActsMars _ s (i j))); rw[ArcPairMars]
lemma spawnMars (d:NSF.Caps n)(ρ:LabelsMars d)(x:Points n)(h:x∈conf n): ChartPriceMars p Y ρ x=star (ChartPriceMars p Y ρ x):=by
 let C:= Complex.conjCLE.toContinuousLinearMap; let F:= M (τCoreMars ρ); let l:=(τGuideMars ρ).map guideDirMars
 have he:F=ᶠ[𝓝 x] C ∘ F:= ((conf_open _).eventually_mem h).mono (fun i e=>by
    have he:= H.shade (τCoreMars ρ) i e; rw [show Calibration.shade four ∘ τCoreMars ρ= τCoreMars ρ from funext (fun i=>MFixedMars _)] at he; exact he)
 exact ((pool_germMars x l F (C ∘ F) he).self_of_nhds).trans (poolConvertMars C F _ (conf_open n) (TerraSm p Y _) l x h)
lemma BarTableMars (d:NSF.Caps n)(v:ChartVuMars d)(x:Points n)(hx:x∈conf n): (T).value d x (fun i=> star (v i))=star ((T).value d x v):=by
 rw [TaxApplyMars,TaxApplyMars,star_sum]; refine sum_congr rfl fun i _=>?_
 rw [star_mul', ← spawnMars H d i x hx]; unfold ChartTaxMars; rw [star_prod]; rfl -- tune
lemma BellSpinMars : NSF.Table.RealSpin T where -- tune tag
 mirror s x h w:= WindTableMars H s (fun i=>(w i).1) (fun i=>(w i).2) x h
 real {n} {x} h w:= BarTableMars H (fun i=>(w i).1) (fun i=>(w i).2) x h
lemma acrossMars (s:E4)(d:NSF.Caps n)(ρ:LabelsMars d)(x:Points n)(hx:x∈conf n): ChartPriceMars p Y ρ (NSF.Points.across s x)=ChartPriceMars p Y ρ x:=by
 let I:=ContinuousLinearMap.id ℝ (Points n); let F:=M (τCoreMars ρ); let l:=(τGuideMars ρ).map guideDirMars
 symm; refine (MirrorPoolMars F F (NSF.Points.across s) I (TerraSm _ _ _) (fun i h=> NSF.Points.across_in _ h) (fun i e=>(H.even _ _ _ e).symm) (fun x=> I.hasFDerivAt.add_const (points fun _=> s)) l x hx).trans ?_
 rw [show l.map I=l from l.map_id]; rfl
lemma CrossTableMars (d:NSF.Caps n)(v:ChartVuMars d)(x:Points n)(hx:x∈conf n)(s:E4): (T).value d (NSF.Points.across s x) v=(T).value d x v:=by rw[TaxApplyMars,TaxApplyMars]; simp_rw [acrossMars H _ _ _ _ hx]
lemma TableHomoMars : NSF.Table.Homogeneous T := fun n x e s w=> CrossTableMars H (fun i=>(w i).1) (fun i=>(w i).2) x e s
#print axioms BellSpinMars
#print axioms TableHomoMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
