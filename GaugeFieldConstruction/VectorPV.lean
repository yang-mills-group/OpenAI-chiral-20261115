import GaugeFieldConstruction.SunfireCell
import GaugeFieldConstruction.Cop
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Ember Ember.Volumetric Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset Mink RawBank Cell
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU -- tune names
-- grade-3 price axes are genuinely the unshifted B_i vector slots of the coupled Weyl matter symbols.
abbrev CogPV:= UV three
abbrev IdWitPV:= Matter.FlavorIndex
-- coordinates.Complex; Eu signs apply properly.
noncomputable def FslotPV(d:Floor)(m:IdWitPV):UF d→ₗ[ℂ] UV d:= LinearMap.inr ℂ _ _ ∘ₗ LinearMap.inr ℂ _ _ ∘ₗ LinearMap.inl ℂ _ _ ∘ₗ LinearMap.single _ (fun _=> UF d) m
noncomputable abbrev SpinSlot3 (m:IdWitPV)(a:Axis):CogPV:= FslotPV three m ((DeckF three).issue (ket a))
noncomputable abbrev SpinSlot4 (m:IdWitPV)(a:Axis):ΧiMars:= FslotPV four m ((DeckF four).issue (ket (Sum.inl a)))
lemma vValPV (i : Axis) : ((DeckF three).issue (ket i)).val=Row.B i:= Mint.paid_at .. -- notation
lemma riseInPV (d:Floor)(m:IdWitPV) {F:UF d}(i:IdWitPV): ((FslotPV d m) F).2.2.1 i= if m=i then F else 0:=by change (Pi.single m F : IdWitPV→UF d) i =_; by_cases h:m=i <;> simp only [h,Pi.single_apply,eq_self,↓reduceDIte, ↓reduceIte,eq_mp_eq_cast,cast_eq] <;> simp_all [eq_comm]
private lemma rollZeroGPV : Subsingleton (UG three):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _)) -- H tune
private lemma rollZeroXPV : Subsingleton (UX three):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _))
lemma vFramePV (s:Signed)(m:IdWitPV)(a:Axis)(h:signBit s=false): spinFrame three s (SpinSlot3 m a)=pay (s.flip a) (SpinSlot3 m (s.perm a)):=by
 let k:UF three:=(DeckF three).issue (ket a); let u:= (DeckF three).issue (ket (s.perm a))
 have ht : (Calibration.matter three).moves s k=pay (s.flip a) u:=by
    let D:=DeckF three; let Q:= (Calibration.matter three); rw [show Q.moves s k=D.issue (Cell.beacon D.label s (ket a)) from Eq.symm (Mint.respect D Q.toCarries s _)]
    unfold Cell.beacon; rw [on_ket]; change D.issue (pay ((signBit s).xor (s.flip a)) _)= _; rw [h, Bool.false_xor]; cases s.flip a <;> simp only[pay_false,pay_true,map_neg];
    all_goals rfl -- may none
 have hu d: Calibration.rev s d=d:=by simp [Calibration.rev,h]
 suffices spinFrame three s (FslotPV three m k)=FslotPV three m ((Calibration.matter three).moves s k) by rw [show spinFrame three s (SpinSlot3 m a) = _ from this,ht]; cases s.flip a <;> first|rfl|exact map_neg ..
 apply Prod.ext
 · rfl
 apply Prod.ext
 · haveI:= rollZeroGPV; exact Subsingleton.elim ..
 refine Prod.ext (funext fun v=>?_) (funext fun v=>?_) -- types
 · rw [tuneF, hu,riseInPV,riseInPV]; split_ifs <;> simp
 haveI:=rollZeroXPV; exact Subsingleton.elim ..
lemma lectPV {Z:Type*}[AddCommGroup Z][Module ℂ Z](F G:CogPV→ₗ[ℂ]Z)(g:F (one three)=G (one three))(p:∀ i a,F (SpinSlot3 i a)=G (SpinSlot3 i a)): F=G:=by
 let S(i):= FslotPV three i
 have e i (x:UF three):F (S i x)=G (S i x):=by
    obtain ⟨j,rfl⟩:=(DeckF three).supply x
    exact LinearMap.congr_fun (ket_ext (p i) : F ∘ₗ S i ∘ₗ (DeckF three).issue=G ∘ₗ S i ∘ₗ (DeckF three).issue) j
 apply LinearMap.ext; intro x
 let A:= x.2.2.1
 have hx:x=x.1 • (one three)+ ∑ i:IdWitPV, S i (A i):=by
    apply Prod.ext
    · simp only [Prod.fst_add,Prod.fst_smul]; have h : (∑ i:IdWitPV,S i (A i)).1=0:=by
        change readOne three (∑ i, S i (A i))=0; rw [map_sum]; exact Finset.sum_eq_zero (fun i _=>rfl)
      rw [h]; simp [one]
    apply Prod.ext
    · haveI:=rollZeroGPV; exact Subsingleton.elim ..
    refine Prod.ext (funext fun b=>?_) (funext fun b=>?_)
    · let Q : CogPV→ₗ[ℂ] UF three:= (LinearMap.proj (R:=ℂ) b) ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _
      change A b=Q (_+∑ i:IdWitPV,_); rw [map_add,map_sum,Q.map_smul,show Q (one three)=0 from rfl,smul_zero,zero_add,sum_eq_single b]
      · rw [show Q (S b (A b))=_ from riseInPV three b b, if_pos rfl] -- tune
      · intro i _ h; rw [show Q (S i _)=_ from riseInPV three i b]; rw [if_neg h]
      simp
    haveI:=rollZeroXPV; exact Subsingleton.elim ..
 nth_rw 1 [hx]; rw [show G x= G (x.1 • one three+∑ i:IdWitPV,S i (A i)) from congrArg G hx,map_add,map_add,map_sum,map_sum,map_smul,map_smul,g]; simp_rw[e]
#print axioms vFramePV
end YM.GaugeFieldConstruction.Stage
end
