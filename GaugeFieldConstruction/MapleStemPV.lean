import GaugeFieldConstruction.VectorPV
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
noncomputable def LowIncPV: CogPV→ₗ[ℂ] ΧiMars where
  toFun v:=(v.1,⟨_,(show SG three≤ SG four from bot_le) v.2.1.property⟩,(fun j=>⟨_, (show SF three ≤ SF four from le_sup_left) (v.2.2.1 j).property⟩),(fun j=>⟨_, (show SX three≤ SX four from bot_le) (v.2.2.2 j).property⟩)) -- tune syntax
  map_add' x y:=rfl; map_smul' x y:=rfl
lemma LowFivePV (x:CogPV): Calibration.lift four (LowIncPV x)= Calibration.lift three x:=rfl
lemma RegisterLowPV(a:Axis)(f:IdWitPV): LowIncPV (SpinSlot3 f a)=SpinSlot4 f a:=by
 apply Calibration.inject four
 rw [LowFivePV]; apply Prod.ext; · rfl
 apply Prod.ext
 · apply Subtype.ext; rfl
 refine Prod.ext (funext fun i=>?_) (funext fun i=>Subtype.ext ?_)
 · apply Subtype.ext
   change ((FslotPV three f ((DeckF three).issue _)).2.2.1 i).val=((FslotPV four f ((DeckF four).issue _)).2.2.1 i).val; rw[riseInPV,riseInPV]
   by_cases v:i=f
   · subst i; rw[if_pos rfl,if_pos rfl,Mint.paid_at,Mint.paid_at]; rfl
   rw[if_neg (Ne.symm v),if_neg (Ne.symm v)]; rfl
 rfl
open Mink
private lemma PanAxisPV (L:Lorentz)(i:Axis): rhoFL L ((DeckF four).issue (ket (Sum.inl i)))= ∑ j, PilotCellL.sheet L j i • (DeckF four).issue (ket (Sum.inl j)):=by
 rw [Angles.jewelL]
 suffices m: rideL FlavorScopeL L (ket (Sum.inl i)) = ∑ j, (PilotCellL.sheet L) j i • ket (Sum.inl j) by rw [m]; erw [map_sum]; exact Finset.sum_congr rfl (fun _ _=> map_smul _ _ _)
 -- inst inertia
 ext1 j
 rw [show rideL _ _ =_ from (@rfl _ (codeL (FlavorScopeL.sheet L))),onL]
 erw [Finsupp.finsetSum_apply]
 change Sum Axis _ at j
 cases j with
 | inl a =>
    rw [sum_eq_single a]; simp [FlavorScopeL,Meridian.sail,Finsupp.smul_apply,ket]; exact Eq.symm (Finsupp.single_eq_same)
    · intro b _ k; simp [Finsupp.smul_apply,ket,Finsupp.single_apply,k]; exact Finsupp.single_eq_of_ne (fun x=> k (Sum.inl.inj x.symm))
    simp
 | inr a =>
    change 0= _; simp only [Finsupp.smul_apply,ket,Finsupp.single_apply]; simp; symm; exact sum_eq_zero (fun i _=> Finsupp.single_eq_of_ne (Ne.symm Sum.inl_ne_inr))
lemma ScopeLegPV (p:Lorentz)(i:Axis)(x:IdWitPV):ledgerL All p (SpinSlot4 x i)= ∑ j:Axis,(σVecL p j i) • SpinSlot4 x j:=by
 change TagL _ _ (FslotPV four x _) = _
 have H(y:UF four):TagL All p (FslotPV four x y) = FslotPV four x (rhoFL p y):=by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · simp only[takeGL]; change rhoGL p 0=0; simp
    refine Prod.ext (funext fun i=>?_) (funext fun i=>?_) -- tune
    · simp only [takeFL]; rw[riseInPV,riseInPV]; change rhoFL p (if x=i then y else 0) = _; split_ifs <;>simp
    haveI : Subsingleton (UX four):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _)); exact Subsingleton.elim ..
 rw[H,PanAxisPV,map_sum]; simp_rw[map_smul]; rfl
lemma ScaleOnePV(p:Lorentz) : ledgerL All p (LowIncPV (one three))=LowIncPV (one three):=by
 apply Prod.ext
 · rfl
 apply Prod.ext
 · change rhoGL p 0=0; simp
 refine Prod.ext (funext fun i=>?_) (funext fun i=>?_) -- tune
 · change rhoFL p 0=0; simp
 haveI : Subsingleton (UX four):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _)); exact Subsingleton.elim ..
#print axioms ScopeLegPV
end YM.GaugeFieldConstruction.Stage
end
