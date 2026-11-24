import GaugeFieldConstruction.GrottoMars
import GaugeFieldConstruction.StyriaRel.YM.Euclid.Stress
/-!
 # complete formal derivative rows. Keep c and monomial prices explicit

 Thick complex reference grade d indexed by *all* derivatives ≤d from the purchased four frame. Use sign oriented directions, so permutation needs no scalar cost (derivative of mirrored slot represented by a negative-axis coupon). Extra null masks disappear automatically by NSF analog of YM.Euclid.Null. Always contains EI four rows. These do NOT inherit engineering dimensions as degrees.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
noncomputable def UrBMars:= Module.finBasis ℂ ΧiMars
abbrev SpeckMars:=Fin (Module.finrank ℂ ΧiMars)
private noncomputable def whiteCore (i:SpeckMars×Bool):ΧiMars:= if i.2 then (I*2⁻¹:ℂ) • (UrBMars i.1 - shade _ (UrBMars i.1)) else ( (2:ℂ)⁻¹) • (UrBMars i.1 + shade _ (UrBMars i.1))
private lemma whiteAt (i:SpeckMars×Bool):shade four (whiteCore i)=whiteCore i:=by
 unfold whiteCore; split
 · rw [map_smulₛₗ, map_sub,Calibration.clear]; rw[show Cauchy.Conj.bar _= -(I*(2:ℂ)⁻¹) from ?_, neg_smul,← smul_neg,neg_sub]
   change starRingEnd ℂ _=_; simp [map_ofNat] -- tune
 rw [map_smulₛₗ,map_add,Calibration.clear, add_comm (((Calibration.shade _) _)), show Cauchy.Conj.bar _=(2:ℂ)⁻¹ from ?_]; change starRingEnd ℂ _=_; simp [map_ofNat]
abbrev MariaMars:= Option (Signed×SpeckMars×Bool)
noncomputable def MCoreMars: MariaMars→ ΧiMars
 | none=> Empire.one four
 | some i=> spinFrame four i.1 (whiteCore i.2)
lemma MFixedMars (m:MariaMars): shade four (MCoreMars m)=MCoreMars m:=by
 cases m with
 | none=>
    change shade four (one four)=one four
    -- name
    simp [Empire.one,Calibration.shade]; exact ⟨rfl,rfl⟩
 | some m=> exact (comp_s _ _).trans (congrArg _ (whiteAt _))
def MActsMars (s:Signed) : MariaMars→MariaMars:=Option.map (fun i=> (s*i.1,i.2))
lemma MActsAtMars (s:Signed) (m:MariaMars): MCoreMars (MActsMars s m)=spinFrame four s (MCoreMars m):=by
 cases m with
 | none=> exact (sends_1 four s).symm
 | some m=> rw [show MCoreMars (MActsMars s (some m))= _ from rfl]; change spinFrame _ (s*m.1) _=_; rw[map_mul]; rfl
noncomputable def UniTagMars : (MariaMars→ℂ)→ₗ[ℂ] ΧiMars:= ∑ i:MariaMars,(LinearMap.proj i).smulRight (MCoreMars i)
lemma UniAtMars (m:MariaMars→ℂ): UniTagMars m=∑ i:MariaMars, m i • MCoreMars i:=by unfold UniTagMars; rw [LinearMap.sum_apply]; rfl
lemma UniSingleMars (m:MariaMars): UniTagMars (Pi.single m 1)=MCoreMars m:=by
 rw[UniAtMars,sum_eq_single m]
 · simp
 · intro i hi hr; rw [Pi.single_eq_of_ne hr]; simp
 simp
lemma UniRichMars : LinearMap.range UniTagMars=⊤:=by
 apply eq_top_iff.mpr; rw[← UrBMars.span_eq, Submodule.span_le]; rintro x ⟨i,rfl⟩
 have he(b:Bool):whiteCore (i,b)∈ LinearMap.range UniTagMars:=by
    refine ⟨Pi.single (some (1,i,b):MariaMars) 1,(UniSingleMars _).trans ?_⟩; change spinFrame _ 1 _= _; rw [map_one]; rfl
 have hp : UrBMars i= whiteCore (i,false) - I • whiteCore (i,true):=by
    simp only [whiteCore,Bool.false_eq_true,↓reduceIte]
    rw [smul_smul,←mul_assoc,I_mul_I,neg_mul,neg_smul,sub_neg_eq_add, one_mul,←smul_add]
    let x:=UrBMars i; let y:=Calibration.shade four x
    rw [show x+y+(x-y)=(2:ℂ) • x from by rw [show (2:ℂ)=1+1 by norm_num,add_smul,one_smul]; abel, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] -- tune
 exact hp ▸ (LinearMap.range UniTagMars).sub_mem (he false) ((LinearMap.range UniTagMars).smul_mem I (he true)) -- tune pp orientation

-- direction may ±
abbrev CompassMars:= Axis × Bool
def revolveMars (s:Signed) (a:CompassMars):CompassMars:=(s.perm a.1, s.flip a.1^^a.2)
abbrev TrailsMars (d:ℕ): Type:=Sigma (fun i:Fin (d+1)=> Fin i.val→CompassMars)
abbrev ΦCodexMars (d:ℕ):=MariaMars×TrailsMars d
abbrev LabelMars (d:ℕ):= Fin (Fintype.card (ΦCodexMars d))
abbrev FlyerMars (d:ℕ):=LabelMars d→ ℂ
noncomputable def IndexMars (d):= Fintype.equivFin (ΦCodexMars d)
def coreActsMars (d:ℕ)(s:Signed)(i:ΦCodexMars d):ΦCodexMars d:=(MActsMars s i.1,⟨i.2.1,revolveMars s ∘ i.2.2⟩)
lemma coreOneMars (d:ℕ)(i:ΦCodexMars d): coreActsMars d 1 i=i:=by
 rcases i with ⟨m,j,v⟩
 have ht:MActsMars 1 m=m:=by cases m <;> simp [MActsMars]
 refine Prod.ext ht ?_; apply congrArg (fun v=> (⟨j,v⟩: TrailsMars d)); change revolveMars 1 ∘ v=v; ext1 x; simp [revolveMars]
lemma coreMulMars (d:ℕ)(i:ΦCodexMars d) (s k:Signed): coreActsMars d (s*k) i=coreActsMars d s (coreActsMars d k i):=by
 rcases i with ⟨m,j,v⟩; have he:MActsMars (s*k) m=MActsMars s (MActsMars k m):=by cases m <;> simp [MActsMars,mul_assoc]
 apply Prod.ext he; apply congrArg (fun v=> ((⟨j,v⟩: TrailsMars d))); change revolveMars (s*k) ∘ v=revolveMars s ∘ revolveMars k ∘ v; ext1 x; simp [revolveMars]
noncomputable def arcActsMars (d)(s:Signed): LabelMars d→ LabelMars d:= IndexMars d ∘ coreActsMars d s ∘ (IndexMars d).symm
lemma ArcOneMars (d)(i:LabelMars d): arcActsMars d 1 i=i:=by simp [arcActsMars,coreOneMars]
lemma ArcMulMars (d)(i:LabelMars d)(s k): arcActsMars d (s*k) i=arcActsMars d s (arcActsMars d k i):=by simp [arcActsMars, coreMulMars]
lemma ArcPairMars (d)(i:LabelMars d)(s:Signed):arcActsMars d s⁻¹ (arcActsMars d s i)=i:=by rw[←ArcMulMars,inv_mul_cancel,ArcOneMars]
noncomputable def SunArcMars (d)(s:Signed):Equiv.Perm (LabelMars d):= { toFun:=arcActsMars d s, invFun:=arcActsMars d s⁻¹,left_inv:=fun i=>ArcPairMars d i s,right_inv:=fun i=> by rw [←ArcMulMars,mul_inv_cancel,ArcOneMars] }
noncomputable def writeArcMars (d)(s:Signed):Module.End ℂ (FlyerMars d):= LinearMap.pi (fun i=> LinearMap.proj (arcActsMars d s⁻¹ i))
lemma writeArcOneMars (d s i): writeArcMars d s (Pi.single i 1)=Pi.single (arcActsMars d s i) 1:=by
 ext1 j; change (Pi.single i 1:FlyerMars d) (arcActsMars d s⁻¹ j) = _; by_cases h:j=arcActsMars d s i
 · subst j; rw[ArcPairMars]; simp -- tune
 rw[Pi.single_eq_of_ne h,Pi.single_eq_of_ne]; intro g; apply h; rw [←g,←ArcMulMars,mul_inv_cancel,ArcOneMars]
def TrailBlankMars (d:ℕ):TrailsMars d:= ⟨0,Fin.elim0⟩
noncomputable def arcBlankMars (d):LabelMars d:=IndexMars d (none,TrailBlankMars d)
lemma arcStillMars (d)(s:Signed): arcActsMars d s (arcBlankMars d)=arcBlankMars d:=by
 simp only [arcBlankMars,arcActsMars, Function.comp_apply, Equiv.symm_apply_apply]; congr 1; refine Prod.ext rfl ?_; exact congrArg (fun v=> ((⟨0,v⟩:TrailsMars d))) (funext (fun i=>Fin.elim0 (i))) -- tune
-- NSF.Register
noncomputable def ΡeaderMars: NSF.Register Unit.unit where
 dim d:= Fintype.card (ΦCodexMars d)
 scalar d:= Pi.single (arcBlankMars d) 1
 mirrorGroup:=writeArcMars
 bar_scalar d:=by ext1 i; by_cases h:i=arcBlankMars d <;> simp [h]
 mirror_scalar s d:= by rw [writeArcOneMars,arcStillMars]
 mirror_mul s k d v:=by ext1 i; change v (arcActsMars d (s*k)⁻¹ i)= v _; rw[mul_inv_rev,ArcMulMars] -- tune
 mirror_one d v:=by ext1 i; change v (arcActsMars d 1⁻¹ i)= _; rw[inv_one,ArcOneMars]
 star_mirror s d v:=rfl
#print axioms UniRichMars
#print axioms ΡeaderMars
end YM.GaugeFieldConstruction.Ember.Volumetric
