import GaugeFieldConstruction.Oracles
/-
# Real form. Operator array. Use bars even on ℂ-named fields. Do not replace by naive
 ℂ coordinate restriction.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 12400
noncomputable section
namespace YM.GaugeFieldConstruction.Sunpath
open Calibration Raw Filter Module LinearMap Function Cauchy Conj Ortho Ember Complex
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate Classical
variable {A B : Type*} [AddCommGroup A][AddCommGroup B][Module ℂ A][Module ℂ B][Module ℝ A][Module ℝ B][IsScalarTower ℝ ℂ A][IsScalarTower ℝ ℂ B]
-- restrictSmul lacks lemmas
def crystalPV (τ : A →ₛₗ[bar] A) : A →ₗ[ℝ] A where
 toFun:=τ
 map_add':= map_add _
 map_smul' a x:=by
    have he (x:A): a • x=(a:ℂ) • x:= ((IsScalarTower.algebraMap_smul ℂ a x)).symm
    change τ (a • x)=a • τ x; rw [he,he _]; rw [LinearMap.map_smulₛₗ]; simp [bar]

def RayPV (τ : A →ₛₗ[bar] A) : Submodule ℝ A:= ker (crystalPV τ-LinearMap.id)
lemma heightPV (τ : A →ₛₗ[bar] A) (i:A): i∈RayPV τ ↔ τ i=i:= Iff.trans LinearMap.mem_ker sub_eq_zero
variable (τ:A→ₛₗ[bar] A)(h: Function.Involutive τ)
include h in
private theorem αpv (i : A) : (1/2:ℂ) • (i+τ i)∈ RayPV τ:= by
 rw [heightPV,LinearMap.map_smulₛₗ,map_add,h,add_comm]; congr; rw[map_div₀,map_one,map_ofNat]
include h in
private theorem βpv (i:A): (-I/2) • (i-τ i)∈ RayPV τ:= by
 rw [heightPV,LinearMap.map_smulₛₗ,map_sub,h,show τ i-i = -(i-τ i) from (neg_sub _ _).symm,smul_neg, ← neg_smul]; congr 1; rw [map_div₀,map_neg, show bar I= -I from conj_I,map_ofNat]; ring
-- equiv
private def surgePV : RayPV τ × RayPV τ →ₗ[ℝ] A where
 toFun p:=p.1.val+I • p.2.val
 map_add' x y:= by change x.1.val+y.1.val+I • (x.2.val+y.2.val)=_; rw [smul_add]; abel
 map_smul' r p:=by
   change r • p.1.val+I • (r • p.2.val)=r • (p.1.val+I • p.2.val); rw[smul_add]; congr 1
   rw [← IsScalarTower.algebraMap_smul ℂ r (p.2.val),← IsScalarTower.algebraMap_smul ℂ r (I • p.2.val)]; exact smul_comm ..
def lampPV : (RayPV τ × RayPV τ) ≃ₗ[ℝ] A := LinearEquiv.ofBijective (surgePV τ) (by
 constructor
 · apply LinearMap.ker_eq_bot.mp; rw[LinearMap.ker_eq_bot']; intro v hv
   let x:=v.1.val; let y:=v.2.val
   change x+I • y=0 at hv; have Hx : τ x=x:= (heightPV τ _).mp v.1.property
   have Hy : τ y=y:= (heightPV τ _).mp v.2.property
   have he := congr_arg τ hv; rw[map_add,LinearMap.map_smulₛₗ,Hx,Hy,map_zero, show bar I= -I from conj_I, neg_smul, ←sub_eq_add_neg] at he
   have h0 : x=I • y:= sub_eq_zero.mp he
   rw [←h0,← two_smul ℂ x] at hv; have hz:= (smul_eq_zero.mp hv).resolve_left (by norm_num)
   rw [hz] at h0
   exact Prod.ext (Subtype.ext hz) (Subtype.ext ((smul_eq_zero.mp h0.symm).resolve_left I_ne_zero))
 intro v
 refine ⟨(⟨_,αpv τ h v⟩,⟨_,βpv τ h v⟩),?_⟩
 change _+ I • ((-I/2) • (v-τ v))=v
 rw [smul_smul,show I*(-I/2)=1/2 by rw [←mul_div_assoc,mul_neg,I_mul_I,neg_neg],←smul_add, show v+τ v+(v-τ v)=v+v by abel, ← two_smul ℂ v, smul_smul]
 norm_num)
include h
lemma peakPV [Module.Finite ℂ A] : finrank ℝ (RayPV τ)=finrank ℂ A:= by
 letI : Module.Finite ℝ A:= Module.Finite.trans ℂ A
 haveI : Module.Finite ℝ ↥(RayPV τ):= inferInstance
 have H:=(lampPV τ h).finrank_eq
 rw [Module.finrank_prod,←Module.finrank_mul_finrank ℝ ℂ A, show finrank ℝ ℂ=2 from Complex.finrank_real_complex] at H
 omega
variable (L:A→ₗ[ℂ] B) (u:∀ x∈ LinearMap.ker L, τ x∈ LinearMap.ker L)
-- if restricted money probes don't directly compute real structure in target, infer image R rank from complex rank by stable kernel
omit h in
def RadialPV : RayPV τ →ₗ[ℝ] B:= (L.restrictScalars ℝ) ∘ₗ (RayPV τ).subtype
include u
theorem trailRankPV [Module.Finite ℂ A] : finrank ℝ (LinearMap.range (RadialPV τ L))=finrank ℂ (LinearMap.range L):= by
 classical
 let g : LinearMap.ker L→ₛₗ[bar] LinearMap.ker L:= (τ ∘ₛₗ (LinearMap.ker L).subtype).codRestrict _ (fun x=>u x.val x.property)
 have hg: Function.Involutive g:=fun i=>Subtype.ext (h i.val)
 let R:= LinearMap.ker (RadialPV τ L)
 let X : RayPV g≃ₗ[ℝ] R:=
     { toFun:=fun x=>⟨⟨x.val.val,(heightPV τ _).2 (congr_arg Subtype.val ((heightPV g _).1 x.property))⟩, x.val.property⟩
       invFun:=fun y=>⟨⟨y.val.val,y.property⟩,(heightPV g _).2 (Subtype.ext ((heightPV τ _).1 y.val.property))⟩
       map_add' := fun _ _=>rfl
       map_smul' := fun _ _=>rfl
       left_inv:=fun x=> rfl
       right_inv:=fun x=> rfl }
 letI : Module.Finite ℝ A:= Module.Finite.trans ℂ A
 haveI : Module.Finite ℝ ↥(RayPV τ):= inferInstance
 have hx:= LinearMap.finrank_range_add_finrank_ker (RadialPV τ L)
 change finrank ℝ (LinearMap.range (RadialPV τ L))+finrank ℝ R=_ at hx; rw[peakPV τ h, ← X.finrank_eq, peakPV g hg] at hx; exact Nat.add_right_cancel (hx.trans (LinearMap.finrank_range_add_finrank_ker L).symm)
 -- tuner
end YM.GaugeFieldConstruction.Sunpath
