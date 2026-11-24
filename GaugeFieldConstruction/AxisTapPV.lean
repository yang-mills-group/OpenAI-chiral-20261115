import GaugeFieldConstruction.MapleStemPV
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
set_option linter.unusedVariables false
-- Algebra of proper signed frames.Center. enough determine vector action under every Lorentz screen on PH stamps. Matrix units D.M.
noncomputable def FlagPV (a b:Axis) : Module.End ℂ CogPV:= 1 - spinFrame three ((Signed.mirror a)*(Signed.mirror b))
lemma FlagUnitPV(a b:Axis): FlagPV a b (one three)=0:=by rw [FlagPV,LinearMap.sub_apply,sends_1]; exact sub_self _
lemma FlagSensPV(a b:Axis)(u:a≠b)(m:IdWitPV)(i:Axis): FlagPV a b (SpinSlot3 m i)= if a=i ∨ b=i then (2:ℂ) • SpinSlot3 m i else 0 :=by
 unfold FlagPV
 rw [LinearMap.sub_apply,Module.End.one_apply, vFramePV _ _ _ (by rw [signBit_mul]; simp)]
 simp only [Signed.mul_perm_apply]; change _-pay ((Signed.mirror a * Signed.mirror b).flip i) (SpinSlot3 m i)= _
 by_cases p:a=i<;>by_cases h:b=i
 · exact (u (p.trans h.symm)).elim
 · simp only[Signed.mul_flip]; simp [Signed.mirror, *]; rw [two_smul]
 · simp only[Signed.mul_flip]; simp [Signed.mirror, *]; rw [two_smul]
 simp only[Signed.mul_flip]; simp [Signed.mirror, *] -- tune
private lemma otherAxisPV (j:Axis):∃ p:Axis×Axis,p.1≠p.2 ∧ j≠p.1 ∧j≠p.2:=by fin_cases j<;> decide
noncomputable abbrev IronPV (j:Axis): Module.End ℂ CogPV:= (4:ℂ)⁻¹ • (FlagPV j (otherAxisPV j).choose.1 * FlagPV j (otherAxisPV j).choose.2)
lemma IronPortPV (i j:Axis)(m:IdWitPV): IronPV i (SpinSlot3 m j) = if i=j then SpinSlot3 m j else 0:=by
 obtain ⟨x,y,w⟩:=(otherAxisPV i).choose_spec; unfold IronPV; rw [LinearMap.smul_apply,Module.End.mul_apply,FlagSensPV _ _ w]; split_ifs with p q q
 · rw[map_smul,FlagSensPV _ _ y,if_pos (Or.inl q),smul_smul,smul_smul]; norm_num
 · have v:=p.resolve_left q; rw [map_smul,FlagSensPV _ _ y,if_neg (show ¬ _ from fun e=>x ((e.resolve_left q).trans v.symm))]; simp
 · exact (p (Or.inl q)).elim
 simp
lemma IronOnePV(i:Axis): IronPV i (one three)=0:=by rw [IronPV,LinearMap.smul_apply, Module.End.mul_apply, FlagUnitPV,map_zero,smul_zero]
noncomputable def WorkHPV (i j:Axis): Module.End ℂ CogPV:=pay ((Count.sw i j).flip i) (spinFrame three (Count.sw i j) * IronPV i)
private lemma pay_applyPV (u:Bool)(v : Module.End ℂ CogPV) (x:CogPV):(pay u v) x=pay u (v x):=by cases u<;> rfl
lemma WorkPortPV (i j a:Axis)(m:IdWitPV): WorkHPV i j (SpinSlot3 m a)=if i=a then SpinSlot3 m j else 0:=by
 unfold WorkHPV; rw [pay_applyPV,Module.End.mul_apply,IronPortPV]
 by_cases p:i=a
 · subst a; rw [if_pos rfl, if_pos rfl,vFramePV _ _ _ (Count.sw_pos i j),Count.sw_apply, pay_pay]
 rw [if_neg p,if_neg p,map_zero,pay_zero]
lemma WorkOnePV(i j:Axis):WorkHPV i j (one three)=0:=by rw [WorkHPV,pay_applyPV,Module.End.mul_apply, IronOnePV,map_zero,pay_zero]
-- thus
noncomputable def ForecastLPV (U:Lorentz):Module.End ℂ CogPV:= 1 + ∑ i:Axis,∑ j:Axis,(σVecL U j i - (if j=i then 1 else 0)) • WorkHPV i j
lemma FogOnePV (U:Lorentz): ForecastLPV U (one three)=one three:=by unfold ForecastLPV; simp only [LinearMap.add_apply, LinearMap.sum_apply,LinearMap.smul_apply, WorkOnePV]; simp
lemma FogTaxesPV (U:Lorentz)(m:IdWitPV)(i:Axis): ForecastLPV U (SpinSlot3 m i) = ∑ j:Axis, σVecL U j i • SpinSlot3 m j:=by
 unfold ForecastLPV; simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply, WorkPortPV, Module.End.one_apply]; rw [sum_eq_single i]
 · simp only[ite_true, sub_smul, sum_sub_distrib]; rw [show (∑ x: Axis,(if x=i then (1:ℂ) else 0) • SpinSlot3 m x)=SpinSlot3 m i from ?_]; abel -- placeholder
   rw [sum_eq_single i]; simp; · intro _ _ p; rw[if_neg p,zero_smul];
   simp
 · intro a _ p; simp [p]
 simp
#print axioms FogTaxesPV
end YM.GaugeFieldConstruction.Stage
end
