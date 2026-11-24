import GaugeFieldConstruction.SagansMars
/-!
 # every grade grows a law. Choose throughall order. 
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
variable (W:Fin n→ (BellTableMars p Y).Tag)(x:Points (n+1))(χ:Bulb)(h: BreatherMars χ 0 x)
variable (H:FirstPackMars p Y)
noncomputable abbrev RiseCapMoon (a:ℕ)(Ω:Ortho.Skew)(A:(BellTableMars p Y).Field a):Prop:= EpochLunaMars a A ∧ ∃ B,FortuneMars a Ω A B
-- module linear via lemma add.deriv
variable {Ω:Ortho.Skew}{a:ℕ}
lemma FortAddMars {A B F G: (BellTableMars p Y).Field a}(e: FortuneMars a Ω A F)(g: FortuneMars a Ω B G): FortuneMars a Ω (A+B) (F+G):=by
 intro n D w x χ h; let W:=highQtyMars p Y w
 rw[← rankPulseApplyMars _ _ χ h,← LunaPriceMars,map_add,map_add, LunaPriceMars, LunaPriceMars, rankPulseApplyMars,rankPulseApplyMars,e n D w x χ h,g n D w x χ h]
lemma FortScaleMars {A F: (BellTableMars p Y).Field a}(c:ℂ)(e: FortuneMars a Ω A F):FortuneMars a Ω (c • A) (c • F):=by
 intro n D w x χ h; rw[←rankPulseApplyMars _ _ χ h,←LunaPriceMars,map_smul,map_smul,LunaPriceMars,rankPulseApplyMars,e _ _ _ _ _ h]
lemma EpochAddMars {A B: (BellTableMars p Y).Field a}(e:EpochLunaMars a A)(g:EpochLunaMars a B): EpochLunaMars a (A+B):=by
 intro n D w x χ h i; rw[←rankFluxApplyMars _ _ χ h,←LunaPriceMars]; unfold riseUpsMars; rw[map_add,map_add,map_add,LunaPriceMars, LunaPriceMars,rankFluxApplyMars,rankFluxApplyMars,e _ _ _ _ _ h,g _ _ _ _ _ h]
lemma EpochScaleMars (c:ℂ){A: (BellTableMars p Y).Field a}(e:EpochLunaMars a A): EpochLunaMars a (c • A):=by
 intro n D w x χ h i; rw [←rankFluxApplyMars _ _ χ h,←LunaPriceMars]; unfold riseUpsMars; rw[map_smul,map_smul,map_smul,LunaPriceMars, rankFluxApplyMars,e _ _ _ _ _ h]
include H
noncomputable def ChapelMars (Ω:Ortho.Skew)(a:ℕ):Submodule ℂ ((BellTableMars p Y).Field a) where
 carrier:={A| RiseCapMoon a Ω A}
 zero_mem':=by
    have he:=equityMars H a (none:MariaMars); let X:= spinBegMoon H a Ω (none:MariaMars)
    have ht:= EpochScaleMars 0 he; rw[zero_smul] at ht; refine ⟨ht,0,?_⟩; have hx:= FortScaleMars 0 X; simpa only[zero_smul] using hx
 add_mem':=fun {i j} (h:RiseCapMoon a Ω i) (v:RiseCapMoon a Ω j)=> ⟨EpochAddMars h.1 v.1,(by obtain ⟨t,ht⟩:=h.2; obtain ⟨z,hz⟩:=v.2; exact ⟨_,FortAddMars ht hz⟩)⟩
 smul_mem':=fun c i (h:RiseCapMoon a Ω i)=> ⟨EpochScaleMars c h.1,(by obtain ⟨t,ht⟩:=h.2; exact ⟨_,FortScaleMars c ht⟩)⟩
lemma pushMarsQ (Ω:Ortho.Skew)(a:ℕ)(i:CompassMars)(A:(BellTableMars p Y).Field a)(x:A∈ ChapelMars H Ω a): arcTiltMars p Y a i A ∈ ChapelMars H Ω (a+1):=by
 change RiseCapMoon a Ω A at x; obtain ⟨p',B,v⟩:=x
 have ht:=TraverseSpinMoon H i.1 Ω A B p' v
 have he : riseUpsMars i.1 A∈ChapelMars H Ω (a+1):= ⟨TraverseMoonMars H i.1 A p', _,ht⟩
 rcases i with ⟨i,j|j⟩ -- rcases syntax wrong
 · exact he
 rw [show arcTiltMars p Y a (i,true) A= -riseUpsMars i A from ?_]; exact (ChapelMars H Ω (a+1)).neg_mem he
 obtain ⟨A,rfl⟩:= (BellTableMars p Y).onto a A; exact arcπMoonMars H i A
lemma ChapelCurrentMars (Ω:Ortho.Skew)(d:ℕ)(v:MariaMars)(l:TrailsMars d):
    (BellTableMars p Y).project d (coneOneMars d (IndexMars d (v,l))) ∈ ChapelMars H Ω d:=by
 have he d : (BellTableMars p Y).project d (coneOneMars d (IndexMars d (v,TrailBlankMars d))) ∈ ChapelMars H Ω d:=by rw [←MonetArcMars H]; exact ⟨equityMars H d v,_,spinBegMoon H d Ω v⟩
 induction d with
 | zero=>
    obtain ⟨j,t⟩:=l; have ht:j=0:=@Subsingleton.elim (Fin 1) _ j (0:Fin (0+1)); subst j; rw [show ((⟨(0:Fin 1),t⟩:TrailsMars 0))=TrailBlankMars 0 from congrArg (fun v=> (⟨(0:Fin 1),v⟩:TrailsMars 0)) (funext (fun i=>Fin.elim0 i))]; exact he _
 | succ d ih=>
    obtain ⟨j,t⟩:=l; induction j using Fin.cases with
    | zero=> rw [show Sigma.mk _ t=TrailBlankMars (d+1) from congrArg (fun v=>(⟨0,v⟩:TrailsMars (d+1))) (funext (fun i=>Fin.elim0 i))]; exact he _
    | succ j=>
       let W:=Fin.tail (n:=j.val) t; let l0:TrailsMars d:=⟨j,W⟩
       have ht:= pushMarsQ H Ω d (t (0: Fin (j.val+1))) _ (ih l0)
       change (BellTableMars p Y).project _ (ΛTransportMars (pushLaMars (t (0: Fin (j.val+1)))) (coneOneMars d (IndexMars d (v,l0))))∈_ at ht; rw [ΛTAtMars, pushLaMars, show ChaseMars d (IndexMars d (v,l0))=(v,l0) from (IndexMars d).symm_apply_apply _,show pushLlMars (t (0: Fin (j.val+1))) l0=(Sigma.mk (β:=fun i:Fin (d+2)=> Fin i.val→CompassMars) j.succ t) from ?_] at ht; exact ht
       exact congrArg (fun v=>(⟨j.succ,v⟩:TrailsMars (d+1))) (Fin.cons_self_tail t)
lemma ChapelCompleteMars (Ω:Ortho.Skew)(d:ℕ) (A:(BellTableMars p Y).Field d):RiseCapMoon d Ω A:=by
 obtain ⟨A,rfl⟩:=(BellTableMars p Y).onto d A; change _∈ ChapelMars H Ω d; -- presentation using Lum
 have he: ((BellTableMars p Y).project d) A= ∑ i: LabelMars d,A i • ((BellTableMars p Y).project d (coneOneMars d i)):= lumMars ((BellTableMars p Y).project d) A
 rw [he]; apply Submodule.sum_mem; intro i h; apply Submodule.smul_mem; obtain ⟨⟨v,l⟩,rfl⟩:= (IndexMars d).surjective i; exact ChapelCurrentMars H Ω d v l
#print axioms ChapelCompleteMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
