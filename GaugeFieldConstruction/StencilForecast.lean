import GaugeFieldConstruction.AxisTapPV
import GaugeFieldConstruction.StencilPivot
/-!
 # Lorentz resource for all-pairs parity. Forecast after *establishing the correspondence of all orientations*.
 Uses only even-signBit (proper) pay at birth for SO ⇒ proper Lor. Anti-linear flips pay Hermiticity.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Ember Ember.Volumetric Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset Mink RawBank Cell
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff InnerProductSpace Classical
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable (V:Axis→ CogPV)
abbrev looksVectorSt (V:Axis→ CogPV):Prop := ∀ R:Signed, ∀ i:Axis, signBit R=false→ spinFrame three R (V i)=pay (R.flip i) (V (R.perm i))
variable (H:looksVectorSt V)
include H
lemma flagWakeSt (a b i:Axis)(u:a≠b): FlagPV a b (V i)= if a=i ∨ b=i then (2:ℂ) • V i else 0 :=by
 unfold FlagPV
 rw [LinearMap.sub_apply,Module.End.one_apply,H _ _ (by rw [signBit_mul]; simp)]
 simp only [Signed.mul_perm_apply]; change _-pay ((Signed.mirror a * Signed.mirror b).flip i) (V i)=_
 by_cases p:a=i<;>by_cases h:b=i
 · exact (u (p.trans h.symm)).elim
 · simp only[Signed.mul_flip]; simp [Signed.mirror, *]; rw [two_smul]
 · simp only[Signed.mul_flip]; simp [Signed.mirror, *]; rw [two_smul]
 simp only[Signed.mul_flip]; simp [Signed.mirror, *]
omit H in
private lemma otherAxisSt (j:Axis):∃ a b:Axis, a≠b ∧ j≠a ∧j≠b:=by fin_cases j<;> decide
omit H in
private lemma vote_eq_st (j a b:Axis) (p:a≠b)(q:j≠a)(t:j≠b):IronPV j=(4:ℂ)⁻¹ • (FlagPV j a * FlagPV j b):=by
 apply lectPV
 · rw [IronOnePV,LinearMap.smul_apply,Module.End.mul_apply,FlagUnitPV,map_zero,smul_zero]
 intro m i; rw [IronPortPV, LinearMap.smul_apply,Module.End.mul_apply,FlagSensPV _ _ t]; by_cases h:j=i
 · rw [if_pos h,if_pos (Or.inl h),map_smul,FlagSensPV _ _ q,if_pos (Or.inl h),smul_smul,smul_smul]; norm_num
 rw [if_neg h]; split_ifs with v
 · rw [map_smul,FlagSensPV _ _ q,if_neg (fun w=>p ((w.resolve_left h).trans (v.resolve_left h).symm)),smul_zero,smul_zero]
 simp
lemma ironWakeSt (i j:Axis): IronPV i (V j) = if i=j then V j else 0:=by
 obtain ⟨a,b,x,y,w⟩:= otherAxisSt i; rw [vote_eq_st _ _ _ x y w,LinearMap.smul_apply,Module.End.mul_apply,flagWakeSt V H _ _ _ w]; split_ifs with p q q
 · rw[map_smul,flagWakeSt _ H _ _ _ y,if_pos (Or.inl q),smul_smul,smul_smul]; norm_num
 · have v:=p.resolve_left q; rw [map_smul,flagWakeSt _ H _ _ _ y,if_neg (show ¬ _ from fun e=>x ((e.resolve_left q).trans v.symm))]; simp
 · exact (p (Or.inl q)).elim
 simp
omit H in
private lemma payApply_st (u:Bool)(v:Module.End ℂ CogPV)(x:CogPV):(pay u v) x=pay u (v x):=by cases u<;> rfl
lemma WorkVector_st(i j a:Axis):WorkHPV i j (V a)= if i=a then V j else 0:=by
 unfold WorkHPV; rw [payApply_st,Module.End.mul_apply,ironWakeSt V H]
 by_cases p:i=a
 · subst a; rw [if_pos rfl, if_pos rfl,H _ _ (Count.sw_pos i j),Count.sw_apply,pay_pay]
 rw [if_neg p,if_neg p,map_zero,pay_zero]
-- Lor readout
lemma properVector_st (U:Lorentz)(i:Axis): ForecastLPV U (V i)= ∑ j:Axis, σVecL U j i • V j:=by
 unfold ForecastLPV; simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply, WorkVector_st _ H, Module.End.one_apply]; rw [sum_eq_single i]
 · simp only[ite_true, sub_smul, sum_sub_distrib]; rw [show (∑ x: Axis,(if x=i then (1:ℂ) else 0) • V x)=V i from ?_]; abel
   rw [sum_eq_single i]; simp; · intro _ _ p; rw[if_neg p,zero_smul];
   simp
 · intro a _ p; simp [p]
 simp
#print axioms properVector_st
end YM.GaugeFieldConstruction.Stage
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset YM.Boundary
open Mink FirstPackMars NSF.Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
variable {n m:ℕ} (p:Ticket u C)(Z:CloudsL)
private lemma basis_sum (x:E4) : (∑ i : Axis, x i • basis i)=x:=by simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using (EuclideanSpace.basisFun Axis ℝ).sum_repr x
lemma push_price_st (g:Mink.Poincare)(a:Axis)(f:Test4): ΦpaySt a (Joint.push g f)=∑ b:Axis, costΛ g.Λ⁻¹ b a • Joint.push g (ΦpaySt b f):=by
 let H:E4→E4:= (g⁻¹:Poincare).sends
 let L:E4→L[ℝ] E4:= Lorentz.act g.Λ⁻¹
 ext1 x
 have ht:↑(Joint.push g f) = (fun x:E4=> f (H x)):= funext (fun y=>Joint.push_at ..)
 have hu:fderiv ℝ (fun x:E4=> f (H x)) x = (fderiv ℝ f (H x)).comp L:= HasFDerivAt.fderiv (((f.smooth 1).differentiable (by norm_num) (H x)).hasFDerivAt.comp x (show HasFDerivAt H L x from (L.hasFDerivAt.add_const (g⁻¹:Poincare).b)))
 rw [ΦpaySt,ΦsΛKnownL,ht,hu,ContinuousLinearMap.comp_apply]; simp only [-- functionapplication
      _root_.sum_apply,_root_.smul_apply,Joint.push_at]
 calc
   fderiv ℝ f (H x) (L (basis a)) = (fderiv ℝ f (H x)) (∑ i:Axis, L (basis a) i • basis i):=congrArg _ (basis_sum _).symm
   _ = _ :=by rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul]; change _= costΛ _ _ _ • ΦshiftΛ (basis i) f (H x); rw [costΛ,ΦsΛKnownL,Complex.coe_smul]
#print axioms push_price_st
local notation "Y" => SurfRimL Z
variable {W:Surface (SurfRimL Z)} {X:Wightman (SurfRimL Z)} {H:(SurfRimL Z).RealSpin} (D:SurfCheckL Z)
variable (c:X.Realizes (W:=W) (SurfCheckL.VesselPL p D) H)
variable (g:Poincare) (J: Axis→Test4→ₗ[ℂ] Module.End ℂ X.operators.domain) (z:ℂ)
include c
abbrev properCurrentSt (J: Axis→Test4→ₗ[ℂ] Module.End ℂ X.operators.domain):Prop:= ∀ (g:Mink.Poincare) (b:Axis) (f:Test4), DragΛL X c g (J b f)=∑ a:Axis,costΛ g.Λ⁻¹ b a • J a (Joint.push g f)
lemma diveScalarSt (f:Test4)(h:properCurrentSt p Z D c J) : DragΛL X c g (z • ∑ b:Axis, J b (ΦpaySt b f)) = z • ∑ b:Axis, J b (ΦpaySt b (Joint.push g f)):= by
 let A (b:Axis) := J b (ΦpaySt b f); let u:= LocalActΛL X c g; let T:= LocalActΛL X c g⁻¹
 calc
    _ = z • ∑ b:Axis, DragΛL X c g (A b) :=by
        apply LinearMap.ext; intro x; simp only [DragΛL,A,LinearMap.comp_apply, LinearMap.sum_apply,LinearMap.smul_apply,map_smul,map_sum]
    _ = _ :=by
         unfold A; simp_rw [h,push_price_st, map_sum,map_smul]; exact congrArg (z • ·) (sum_comm)
#print axioms diveScalarSt
end YM.GaugeFieldConstruction.Ember.Volumetric
end
