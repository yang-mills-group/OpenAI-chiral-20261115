import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Survey. Pointwise probe limits against moving scale. Finite dimensional inference.

 Avoid giving a new normed instance to field-label types here; all convergence assertions via arbitrary linear tests. Rank and inversion lemmas work via coordinates. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Sailing
open Function Filter Module Metric
open scoped Topology BigOperators
variable (F : Type*) [NontriviallyNormedField F] {A X Y U B : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable (p : Filter A)
def Dips (x : A→X) (z : X): Prop := ∀ g : X →ₗ[F] F,Tendsto (fun k => g (x k)) p (𝓝 (g z))
variable {F p}
lemma fixed (z : X): Dips F p (fun _=>z) z:= fun f=> tendsto_const_nhds
lemma maps {x : A→ X} {z} (h:Dips F p x z) (g : X→ₗ[F]Y) : Dips F p (fun i=>g (x i)) (g z) :=fun f=>h (f ∘ₗ g)
lemma chip {x : A→X} {z} (h:Dips F p x z) {r : A→F} {s} (v:Tendsto r p (𝓝 s)):Dips F p (fun i=> r i • x i) (s • z) := fun f=> by simp only [map_smul,smul_eq_mul]; exact v.mul (h f)
lemma plus {x y : A→X} {u v} (h:Dips F p x u) (k:Dips F p y v) : Dips F p (fun i=>x i+y i) (u+v) := fun f=> by simpa using! (h f).add (k f)
lemma dif {x y : A→X} {u v} (h:Dips F p x u) (k:Dips F p y v) : Dips F p (fun i=>x i-y i) (u-v) := fun f=> by simpa using! (h f).sub (k f)
lemma gathers (I : Finset U) {x : U→ A→X} {z:U→X} (h : ∀ i∈I,Dips F p (x i) (z i)): Dips F p (fun k =>∑ i∈I,x i k) (∑ i∈I,z i) := fun f=> by simp_rw [map_sum]; exact tendsto_finsetSum _ (fun i v=> h i v f)
lemma constant {x : A→X} {y z} (u:Dips F p x z) (h:x=ᶠ[p] y) : Dips F p y z:= fun f=> Tendsto.congr' (h.mono fun i e=> congr_arg f e) (u f)
lemma narrowed (a : Filter A) {x : A→X} {z} (h:Dips F p x z) (u : a≤p): Dips F a x z:= fun g => (h g).mono_left u
lemma subs {q : Filter U} {x : A→X} {z} (h:Dips F p x z) (u : U→ A) (v:Tendsto u q p) : Dips F q (fun i=>x (u i)) z:= fun g=> (h g).comp v

-- pure modules
def Separates (P : X →ₗ[F] U→F): Prop := Injective P
lemma detect (P: X→ₗ[F] U→F) : Separates P ↔ ∀ x,(∀ i,P x i=0) → x=0:= by
  rw [Separates,← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; exact ⟨fun h x i=>h x (funext i),fun h x i=>h x fun a=>congr_fun i a⟩
abbrev feel (P:X→ₗ[F] U→F) (i:U): X→ₗ[F] F:=LinearMap.proj i ∘ₗ P

section
variable [FiniteDimensional F X]
lemma replaces (P:X→ₗ[F] U→F) (u:Injective P): Submodule.span F (Set.range (feel P))= ⊤:= by
  classical
  apply Submodule.span_eq_top_of_ne_zero
  intro z h; have H :∃ i,P z i≠0:= by by_contra! e; exact h ((detect P).mp u z e)
  obtain ⟨i,v⟩:=H; exact ⟨_,⟨i,rfl⟩,v⟩
lemma truth {x : A→ X} {z} (P:X→ₗ[F] U→ F) (u:Injective P) (h : ∀ i,Tendsto (fun k=> P (x k) i) p (𝓝 (P z i))) : Dips F p x z:= by
  classical
  intro f
  have V :f ∈ Submodule.span F (Set.range (feel P)):= replaces P u ▸ Submodule.mem_top
  refine Submodule.span_induction (p:=fun f _=> Tendsto (fun k=> f (x k)) p (𝓝 (f z))) (fun a w=> Set.mem_range.mp w |>.elim (fun i hi=> hi ▸ h i)) ?_ ?_ ?_ V
  · exact tendsto_const_nhds
  · intro a b _ _ v w; exact v.add w
  intro a b _ v; exact (tendsto_const_nhds (x:=a)).mul v

lemma individual [p.NeBot] {x : A→ X} {y z} (v : Dips F p x z) (w : Dips F p x y) : z=y := by
  let B:=Module.finBasis F X
  apply B.equivFun.injective; ext1 i; exact tendsto_nhds_unique (v (B.coord i)) (w (B.coord i))
lemma angel [CompleteSpace F] [NormedAddCommGroup B] [NormedSpace F B] [FiniteDimensional F B] (x:A→B) (z:B) : Dips F p x z↔Tendsto x p (𝓝 z):= by -- X unused remove
  let C:=Module.finBasis F B
  let e := C.equivFun
  refine ⟨fun v=> ?_,fun v g=>g.continuous_of_finiteDimensional.continuousAt.tendsto.comp v⟩
  have he: Tendsto (fun k=> e (x k)) p (𝓝 (e z)) := tendsto_pi_nhds.mpr fun i=> v (C.coord i)
  have h:= e.symm.toContinuousLinearEquiv.continuous.continuousAt.tendsto.comp he
  simpa [Function.comp_def, ContinuousLinearEquiv.continuous] using h -- adjust

-- Chips. build combinations turning varying projections into near-identity

variable (p F) in
def Scores (P : X →ₗ[F] U→F) (l : A→ X→ₗ[F] U→F): Prop:= ∀ i x, Tendsto (fun k=> l k x i) p (𝓝 (P x i))

variable {P : X→ₗ[F] U→F} (u:Injective P) {l : A→ X→ₗ[F] U→F} (v:Scores F p P l) -- binder order
include u
private lemma barge (f : X→ₗ[F] F) : ∃ Q : (U→F)→ₗ[F]F, Q ∘ₗ P=f ∧ ∀ (g:A→(U→F)) (z:U→F), (∀ i,Tendsto (fun k=>g k i) p (𝓝 (z i))) → Tendsto (fun k=>Q (g k)) p (𝓝 (Q z)):= by
  have h : f∈ Submodule.span F (Set.range (feel P)):=replaces P u ▸ Submodule.mem_top
  refine Submodule.span_induction (p:=fun f _=>∃ Q : (U→F)→ₗ[F]F,Q ∘ₗ P=f ∧ ∀ (g:A→ (U→F)) (z:U→F), (∀ i,Tendsto (fun k=> g k i) p (𝓝 (z i))) → Tendsto (fun k=>Q (g k)) p (𝓝 (Q z))) ?_ ?_ ?_ ?_ h -- annotate Prop
  · rintro a ⟨i,rfl⟩; exact ⟨LinearMap.proj i,rfl,fun g z v=>v i⟩
  · exact ⟨0,by simp,fun _ _ _=> tendsto_const_nhds⟩
  · rintro a b _ _ ⟨Q,rfl,h⟩ ⟨Y,rfl,u⟩; exact ⟨Q+Y,by rw [LinearMap.add_comp],fun g z v=> (h g z v).add (u g z v)⟩
  rintro c b _ ⟨Q,rfl,h⟩; exact ⟨c • Q,by rw [LinearMap.smul_comp],fun g z v=> Tendsto.mul (tendsto_const_nhds (x:=c)) (h g z v)⟩
variable [CompleteSpace F]
-- fit lemma from Dash-style. Complete field to gives Ring units.
omit u in
private lemma at_operator {E : Type*} [NormedAddCommGroup E] [NormedSpace F E] [FiniteDimensional F E] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace F Z]
    [FiniteDimensional F Z] (l : A→ E →L[F] Z) (v:E→L[F]Z) (h:∀ i,Tendsto (fun k=> l k i) p (𝓝 (v i))) : Tendsto l p (𝓝 v):= by -- unused u remove
  let B:=Module.finBasis F E
  let I:=Fin (Module.finrank F E)
  let f : (I→ Z)→ₗ[F] (E→L[F] Z):= LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ (B.constr F).toLinearMap
  have e (w:E→L[F]Z): f (fun i=>w (B i))=w:= ContinuousLinearMap.coe_injective (B.ext fun i=>B.constr_basis ..)
  let z i:= fun k:I=> l i (B k)
  let x k:=v (B k)
  have H:Tendsto (fun i=>f (z i)) p (𝓝 (f x)):= f.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (show ∀ k:I,Tendsto (fun i=> z i k) p (𝓝 (x k)) from fun i=>h _))
  simp_rw [x,z,e] at H; rw [show f x=v from e v] at H; exact H
include v
lemma insight : (∀ᶠ k in p,Injective (l k)) ∧ ∀ (x : A→X) (z:X), (∀ i,Tendsto (fun k=> l k (x k) i) p (𝓝 (P z i)))→Dips F p x z:= by
  classical
  let B:=Module.finBasis F X
  let I:=Fin (Module.finrank F X)
  let e:= B.equivFun
  choose Q h H using fun i:I=> barge (p:=p) u (LinearMap.proj i ∘ₗ e.toLinearMap)
  let q:= LinearMap.pi Q
  have he (v : X): q (P v)=e v:= funext fun i=>LinearMap.congr_fun (h i) v
  have hp (g:A→(U→F)) (z:U→F) (w:∀ i,Tendsto (fun k=> g k i) p (𝓝 (z i))) : Tendsto (fun k=> q (g k)) p (𝓝 (q z)):=tendsto_pi_nhds.mpr fun i=> H i g z w
  let Z k : (I→F)→L[F] I→ F:= LinearMap.toContinuousLinearMap (q ∘ₗ l k ∘ₗ e.symm.toLinearMap)
  let id : (I→F)→L[F] I→F:=1
  have hz : Tendsto Z p (𝓝 id):= by
    apply at_operator Z id; intro i
    have hv:= hp (fun k=> l k (e.symm i)) _ (fun j=> v j (e.symm i))
    rw [he,e.apply_symm_apply] at hv; exact hv
  have hi : IsUnit id:=isUnit_one
  have hm :∀ᶠ k in p, IsUnit (Z k):= hz.eventually (Units.isOpen.mem_nhds (show id∈Set.range Units.val from hi))
  let Y k:= Ring.inverse (Z k)
  have hx : Tendsto Y p (𝓝 id) := by
    have h : Tendsto Y p (𝓝 (Ring.inverse id)):= (NormedRing.inverse_continuousAt (1 : (((I→F)→L[F] I→ F)ˣ))).tendsto.comp hz
    rwa [show Ring.inverse id=id from Ring.inverse_one _] at h -- check
  have HZ : ∀ᶠ k in p, ∀ v:X,Y k (q (l k v))=e v:= hm.mono fun i r x=> by
    have H : (Y i)*(Z i)=1 := Ring.inverse_mul_cancel _ r
    rw [← show Z i (e x)=q (l i x) from by change q (l i (e.symm (e x)))=_; rw [e.symm_apply_apply],← ContinuousLinearMap.mul_apply,H]; rfl
  constructor
  · refine HZ.mono (fun i h x y e'=>e.injective ?_); rw [← h,← h,e']
  intro x z w
  have ht:= hp (fun k=> l k (x k)) _ w; rw [he] at ht
  have he : Tendsto (fun k=> e (x k)) p (𝓝 (e z)):= ((show Continuous fun x: ((I→F) →L[F] I → F) × (I→ F)=> x.1 x.2 from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hx.prodMk_nhds ht)).congr' (HZ.mono (fun i h=> h _))
  intro g
  have h := (g ∘ₗ e.symm.toLinearMap).continuous_of_finiteDimensional.continuousAt.tendsto.comp he
  simpa [Function.comp_def] using h
end
end YM.GaugeFieldConstruction.Fathom.Sailing
