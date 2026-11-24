import GaugeFieldConstruction.Depot
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
/-!
# IFT for moving quadratic probes in the section argument
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Sailing
open Function Filter Module
open scoped Topology
variable {A:Type*} (l :Filter A)

section
variable {U:Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
local notation "T" => U →L[ℝ] U
local notation "B" => U→L[ℝ] T
private lemma fare {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (g:Y→L[ℝ]U) (P:Y→L[ℝ] T) (Q:Y→L[ℝ] B) (u:Y)
    (p:A→Y) (w:g u=0) (v:P u=ContinuousLinearMap.id ℝ U) (h:Tendsto p l (𝓝 u)): ∃ f:A→U,Tendsto f l (𝓝 0) ∧ ∀ᶠ n in l,g (p n)+P (p n) (f n)+Q (p n) (f n) (f n)=0:= by
  let F (x:Y×U):= g x.1+P x.1 x.2+Q x.1 x.2 x.2
  let V:Y×U:=(u,0)
  let I:=ContinuousLinearMap.fst ℝ Y U
  let J:=ContinuousLinearMap.snd ℝ Y U
  have hx:= (g.comp I).hasStrictFDerivAt (x:=V)
  let K:=Q.comp I
  have H:= (P.comp I).hasStrictFDerivAt (x:=V)
  have b:= J.hasStrictFDerivAt (x:=V)
  have hr:= HasStrictFDerivAt.clm_apply (c:= ⇑K) K.hasStrictFDerivAt b
  have hv:= HasStrictFDerivAt.clm_apply (c := (fun x=> K x (J x))) hr b
  have hp :=hx.add (HasStrictFDerivAt.clm_apply (c:=fun x=>P (I x)) H b)
  have hpB : ∃ M: Y×U→L[ℝ] U, HasStrictFDerivAt F M V ∧ M.comp (ContinuousLinearMap.inr ℝ Y U)=ContinuousLinearMap.id ℝ U:=by
    refine ⟨_,hp.add hv,?_⟩
    apply ContinuousLinearMap.ext; intro x; simp [J,I,V,K, v]
  obtain ⟨M,m,c⟩:=hpB
  have hu : (M.comp (ContinuousLinearMap.inr ℝ Y U)).IsInvertible:= by rw [c]; exact ⟨ContinuousLinearEquiv.refl _ _,rfl⟩
  let f:=m.implicitFunctionOfProdDomain hu
  refine ⟨fun x=> f (p x), m.tendsto_implicitFunctionOfProdDomain hu |>.comp h,?_⟩
  have hm :=m.eventually_apply_implicitFunctionOfProdDomain hu
  exact (h.eventually hm).mono fun i hi=> hi.trans (show F V=0 by simp [F,V,w])

variable [FiniteDimensional ℝ U]
private lemma kite (p:A→U) (Tt:A→ U→ₗ[ℝ]U) (Q:A→ U→ₗ[ℝ]U→ₗ[ℝ]U) (Z:U→ₗ[ℝ]U→ₗ[ℝ]U) (h:Dips ℝ l p 0) (b:Dips ℝ l Tt LinearMap.id) (c:Dips ℝ l Q Z): ∃ f:A→U,Dips ℝ l f 0 ∧ ∀ᶠ n in l,p n+Tt n (f n)+Q n (f n) (f n)=0:= by
  let L₁: (U→ₗ[ℝ] U)→ₗ[ℝ] (T):= LinearMap.toContinuousLinearMap.toLinearMap
  let J₁: (U→ₗ[ℝ] U→ₗ[ℝ] U) →ₗ[ℝ] (B):= LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ ((LinearMap.llcomp ℝ U (U→ₗ[ℝ] U) (T)) L₁)
  let k i: U × (T)×(B):= (p i,L₁ (Tt i),J₁ (Q i))
  let u:U×(T)×(B):= (0,L₁ LinearMap.id,J₁ Z)
  have h:Tendsto k l (𝓝 u):=by
    have hb := (angel (F:=ℝ) _ _).mp h
    have ht:= (angel (F:=ℝ) _ _).mp (show Dips ℝ l (fun i=>L₁ (Tt i)) _ from maps b L₁)
    have hp:= (angel (F:=ℝ) (fun i=>J₁ (Q i)) (J₁ Z)).mp (show Dips ℝ l (fun i=>J₁ (Q i)) _ from maps c J₁)
    exact hb.prodMk_nhds (ht.prodMk_nhds hp)
  let P : (U×(T)×(B))→L[ℝ] ((T)×(B)):= ContinuousLinearMap.snd ℝ U _
  let V : (U×(T)×(B)) →L[ℝ] U:=ContinuousLinearMap.fst ..
  obtain ⟨t,ht,hp⟩:=fare l V ((ContinuousLinearMap.fst ℝ (T) (B)).comp P) ((ContinuousLinearMap.snd ℝ (T) (B)).comp P) u k rfl rfl h
  exact ⟨t,(angel ..).mpr ht,hp⟩
end
variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [Module.Finite ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [Module.Finite ℝ Y]
lemma realization (B:X→ₗ[ℝ]Y) (T:A→ X→ₗ[ℝ]Y) (U:X→ₗ[ℝ]X→ₗ[ℝ]Y) (Z:A→X→ₗ[ℝ]X→ₗ[ℝ]Y) (x:A→Y) (w: Surjective B) (b : ∀ i,Dips ℝ l (fun k=> T k i) (B i)) (p : ∀ i j,Dips ℝ l (fun k=> Z k i j) (U i j)) (u:Dips ℝ l x 0): ∃ φ:A→X,Dips ℝ l φ 0 ∧ ∀ᶠ i in l,x i+T i (φ i)+Z i (φ i) (φ i)=0 := by
  let E3:=EuclideanSpace ℝ (Fin (Module.finrank ℝ Y))
  let g:= pixels ℝ Y; obtain ⟨K,hK⟩:= B.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr w)
  let V : E3→ₗ[ℝ]X := K ∘ₗ g.symm.toLinearMap
  have hi : (g.toLinearMap ∘ₗ B ∘ₗ V) = LinearMap.id:=by apply LinearMap.ext; intro x; change g (B (K (g.symm x)))=x; rw [show B (K (g.symm x))=g.symm x from LinearMap.congr_fun hK _]; rw [g.apply_symm_apply]
  let a k:= g.toLinearMap ∘ₗ T k ∘ₗ V
  have h : Dips ℝ l a LinearMap.id:= by
    rw [← hi]; exact dotted fun i=> maps (b (V i)) g.toLinearMap
  let t (K:X→ₗ[ℝ]X→ₗ[ℝ]Y): E3→ₗ[ℝ] E3→ₗ[ℝ] E3:=(K.compl₁₂ V V).compr₂ g.toLinearMap
  have he:Dips ℝ l (fun k=> t (Z k)) (t U):= dotted (fun i=> dotted fun j=> maps (p (V i) (V j)) g.toLinearMap)
  have hb := maps u g.toLinearMap; rw [g.toLinearMap.map_zero] at hb
  obtain ⟨i,h,e⟩:= kite (U:=E3) l (fun k=>g (x k)) a (fun k=> t (Z k)) (t U) hb h he
  refine ⟨fun k=> V (i k),?_, e.mono fun k hk=>?_⟩
  · rw [← V.map_zero]; exact maps h V
  apply g.injective; simp only [map_zero,map_add]; exact hk
end YM.GaugeFieldConstruction.Fathom.Sailing
