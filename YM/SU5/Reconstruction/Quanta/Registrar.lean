import YM.SU5.Reconstruction.Quanta.Printer
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
set_option linter.unusedVariables false -- h₁, V etc
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)


-- Form extends linear & marker system. Use positive horizon and Calendar. Mixed parity measured per-component, reflected pairing both
open Garret
local notation "Pₓ" => price Y H V G C j χ
local notation "Ω"=> oneAt Y H V G j (C j) χ
variable (s:ℕ)(j':Axis) (z:ℤ)
variable {b t:Bool} {S:Finset Cover} {f:Family (tent Y H)} {J:Calibration}
open Heat
local notation "Z"=> Heat.gaugeShift Λ.block z
local notation "F₊"=> poleForm (tent Y H) j' Z
noncomputable def studio(J:Calibration)(j':Axis) (z:ℤ)(b:Bool) : Submodule ℂ (Family J) where
 carrier:= {f|∃ S, InTest J true S b f∧ Tower.region j' z J.ℓ S}
 zero_mem' := ⟨∅,InTest.zero,by simp [Tower.region]⟩
 add_mem' := by
    rintro x y ⟨S,u,h⟩ ⟨T,q,t⟩; refine ⟨S∪T, (u.mono Finset.subset_union_left).add (q.mono Finset.subset_union_right),fun i e=>(Finset.mem_union.mp e).elim (h i) (t i)⟩
 smul_mem' := by rintro i x ⟨S,q,t⟩; exact ⟨S,InTest.smul _ q,t⟩
local notation "St" b:max=> studio (tent Y H) j' Z b
lemma studio_p (x:St b):∃ S, InTest (tent Y H) true S b x.val∧ Tower.region j' Z ((tent Y H).ℓ) S:= x.property
variable (x y: studio (tent Y H) j' (Heat.gaugeShift Λ.block z) b)
lemma officeTest:InTest (tent Y H) true (reflectedBox j' Z (Classical.choose (studio_p Y H j' z x)) ∪ (Classical.choose (studio_p Y H j' z y))) false (F₊ b x.val y.val):=NorthTapes.statement j' Z (studio_p Y H j' z x).choose_spec.1 (studio_p Y H j' z y).choose_spec.1
variable (b) in
noncomputable def atelierGram : (St b)→ₗ⋆[ℂ] (St b)→ₗ[ℂ] ℂ where
 toFun x:= {
      toFun:=fun y=> Pₓ s false (F₊ b x.val y.val)
      map_add':=fun y f=>by change Pₓ s false (F₊ b x.val (y.val+f.val))=_; unfold poleForm; rw [mul_add, smul_add]; exact price_add Y H V G C j χ s (officeTest Y H j' z x y) (officeTest Y H j' z x f)
      map_smul':=fun c y=>by change Pₓ s false (F₊ b x.val (c • y.val))=_; unfold poleForm; rw [Algebra.mul_smul_comm,smul_comm]; exact price_smul Y H V G C j χ s (officeTest Y H j' z x y) c }
 map_add' a b':= LinearMap.ext fun f=>by
    change Pₓ s false (F₊ b (a.val+b'.val) f.val)=_+_; unfold poleForm; rw [mirror_plus,add_mul,smul_add]; exact price_add Y H V G C j χ s (officeTest Y H j' z a f) (officeTest Y H j' z b' f)
 map_smul' c a:= LinearMap.ext fun f=>by change Pₓ s false (F₊ b (c • a.val) f.val)= (star c) • _; unfold poleForm; rw [mirror_scale,Algebra.smul_mul_assoc,smul_comm]; exact price_smul Y H V G C j χ s (officeTest Y H j' z a f) _
local notation "L"=>atelierGram Y H V G C j χ s j' z
lemma atelier_positive : 0 ≤ L b x x:=price_aligned Y H V G C j χ s j' z (studio_p Y H j' z x).choose_spec.1 (studio_p Y H j' z x).choose_spec.2
/-- ALL grades at once. Use `Frame` components explicitly to measure each separate request, e.g. even‐odd mixed terms (regulator agrees with zero at those). -/
noncomputable def superpose : ((St false) × (St true)) →ₗ⋆[ℂ] ((St false) × (St true))→ₗ[ℂ] ℂ where
 toFun x:= LinearMap.coprod (L false x.1) (L true x.2)
 map_add' x y:= LinearMap.ext fun t=>by
    change L false (x.1+y.1) t.1 + L true (x.2+y.2) t.2=_; simp only [map_add, LinearMap.coprod_apply,LinearMap.add_apply]; abel
 map_smul' r x:= LinearMap.ext fun t=> by
    change L false (r • x.1) t.1 + L true (r • x.2) t.2 = _; simp only [map_smulₛₗ, LinearMap.coprod_apply,LinearMap.smul_apply]; rw [smul_add]
local notation "Sum" => superpose Y H V G C j χ s j' z
lemma onParity (x y: (St false) × (St true)): Sum x y=L false x.1 y.1 + L true x.2 y.2:=rfl
lemma superposition {X:Type*}[Fintype X](f:X→ (St false) × (St true)): (Matrix.of fun i j'=> Sum (f i) (f j')).PosSemidef:= Tower.halfSpaceKernel Sum (fun x=>add_nonneg (atelier_positive Y H V G C j χ s j' z x.1) (atelier_positive Y H V G C j χ s j' z x.2)) f
-- off diagonal actual parity, in price only after ensuring it's the odd mark sector
lemma offParity {e:Bool} (y: studio (tent Y H) j' (Heat.gaugeShift Λ.block z) e)(z':b≠e):
    let F:= F₊ b x.val y.val
    let S:= (reflectedBox j' (Heat.gaugeShift Λ.block z) ((studio_p Y H j' z x).choose)) ∪ ((studio_p Y H j' z y).choose)
    InTest K true S true F ∧ Pₓ s true F=0 :=by -- Pₓ typo, includes true first capital
 intro F S; refine ⟨?_,rfl⟩
 have hx: Bool.xor b e=true:=by cases b<;>cases e<;>first|rfl|contradiction
 have hp:InTest K true S (Bool.xor b e) (F₊ b x.val y.val):= InTest.smul _ (InTest.mul (((axial K j' Z (studio_p Y H j' z x).choose_spec.1)).mono Finset.subset_union_left) ((studio_p Y H j' z y).choose_spec.1.mono Finset.subset_union_right))
 rw [hx] at hp; exact hp
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.superposition
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.offParity
