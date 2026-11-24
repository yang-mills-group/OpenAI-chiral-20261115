import YM.SU5.Reconstruction.Trap.Invoice
import YM.SU5.Reconstruction.Trap.TapeFar
import YM.SU5.Reconstruction.Trap.Nerve
/-!
# Picket in the Reconstruction setup. same character.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open CrossedFrame
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
variable (j j' : Axis) (hv:j'≠j)
local notation "N" i:max => flank i 0
local notation "Globe" => (N j ∩ N j')
local notation "L" i:max=> lowland i 0
local notation "Tea" => (L j ∩ L j')
noncomputable def onceLens (U:Set RSpace)(b:U⊆N j): Ds U →ₗ[ℂ] G₀ j:= (Os j).comp (Submodule.inclusion (domain_mono Y H G b))
local notation "Lens" i:max=> onceLens Y H V G C a χ i
include hv in
private lemma lens_far (t:C₀ j=⊤)(M:Picket.Paces j' (S₀ j))(x: Set RSpace)(u:x⊆N j)(z:Bool)(h:N j∩sideLand j' 0 z⊆ x): DenseRange (onceLens Y H V G C a χ j x u):=by
 apply (picked_far Y H V G j (C j) (w j) j' hv t M 0 z).mono; rintro v ⟨z,rfl⟩; exact ⟨Submodule.inclusion (domain_mono Y H G h) z,rfl⟩
-- include hv needed (Lean default autoImplicit false does not include)
local notation "Sg" i:max=> (Ds (N i))
include hv in
lemma back_high : mirrorE j 0 '' Tea ⊆ N j ∩ L j':=by
 rintro _ ⟨x,⟨h1,h2⟩,rfl⟩; constructor
 · change 0≤ mirrorE j 0 x j; unfold mirrorE; rw [if_pos rfl]; linarith [ (show x j≤0 from h1)]
 change mirrorE j 0 x j' ≤ 0; rw [mirrorE,if_neg hv]; exact h2
include hv in
lemma forward_low : mirrorE j 0 '' (N j ∩ L j') ⊆ Tea:=by
 rintro _ ⟨x,⟨h1,h2⟩,rfl⟩; constructor
 · change mirrorE j 0 x j≤ 0; rw [mirrorE, if_pos rfl]; linarith [ (show 0≤ x j from h1)]
 change mirrorE j 0 x j' ≤ 0; rw [mirrorE,if_neg hv]; exact h2
noncomputable def flipLens (U:Set RSpace)(b:mirrorE j 0 '' U⊆ N j) (f: Ds U) : G₀ j := (Os j) ⟨(θ j) f.val, domain_mono Y H G b (mirror_support Y H G j f.val f.property)⟩
local notation "FL" i:max=> flipLens Y H V G C a χ i
include hv
lemma flip_high (U:Set RSpace)(b:mirrorE j 0 '' U ⊆ N j)(t:C₀ j=⊤)(M:Picket.Paces j' (S₀ j))(h: Tea ⊆ U): DenseRange (flipLens Y H V G C a χ j U b):=by
 apply (lens_far Y H V G C a χ j j' hv t M _ inter_subset_left false (Set.Subset.refl _)).mono -- specify
 rintro _ ⟨x,rfl⟩; let f:= x.val; have v:(θ j) f ∈ Ds U:= domain_mono Y H G ((forward_low j j' hv).trans h) (mirror_support Y H G j f x.property)
 refine ⟨⟨_,v⟩,?_⟩; apply congrArg (Os j); apply Subtype.ext; exact mirror_twice ..
lemma low_ready : mirrorE j' 0 '' Tea⊆ N j':= by rw [Set.inter_comm]; exact (back_high j' j hv.symm).trans inter_subset_left
lemma top_ready : mirrorE j 0 '' Tea ⊆ N j:= (back_high j j' hv).trans inter_subset_left
-- common lenses
abbrev Brigade (S:Hilbert) (W:Clasp S (fort Y H V G.history G.clipped j false (C j) (w j)) (fort Y H V G.history G.clipped j' false (C j') (w j'))) := Faces ((Lens j) Globe inter_subset_left) ((Lens j') Globe inter_subset_right) ((FL j) Tea (top_ready j j' hv)) ((FL j') Tea (low_ready j j' hv)) S W
local notation "Θ"=> osValue Y H V G a (C a) χ
omit hv in
lemma across_charge (x:Sky (tent Y H))(g :(θ j) x ∈ Sg j)(y:Sky (tent Y H))(p:y∈ Sg j)(h:C₀ j=⊤) : ∃ k:x*y ∈ Domain Y H G false Set.univ, inner ℂ ((Os j) ⟨(θ j) x,g⟩) ((Os j) ⟨y,p⟩)= osValue Y H V G a (C a) χ ⟨x*y,k⟩:=by
 let t:=(⟨(θ j) x,domain_loose Y H G _ g⟩:D (N j)); let s:=(⟨y,domain_loose Y H G _ p⟩: D (N j)); have he:= registered_pair Y H V G j (C j) (w j) t s
 have hv:(θ j) t.val * s.val=x*y:= by change (θ j) ((θ j) x)*y=_; rw [mirror_twice]
 have hx:= hv ▸ paired_forever Y H G j t.val s.val t.property s.property -- tune
 refine ⟨hx,?_⟩; change inner ℂ (((Vo j) t).val:J₀ j) (((Vo j) s).val:J₀ j)=_; rw [voice_full Y H V G j (C j) (w j) h,voice_full Y H V G j (C j) (w j) h]; rw [os_across] at he; exact he.trans (congrArg Θ (Subtype.ext hv))
lemma people (t:C₀ j=⊤)(u:C₀ j'=⊤)(p:Picket.Paces j' (S₀ j))(v:Picket.Paces j (S₀ j')): ∃ (S:Hilbert)(W:Clasp S (G₀ j) (G₀ j')), Brigade Y H V G C a χ j j' hv S W := by
 apply CrossedFrame.cert
 · apply lens_far Y H V G C a χ j j' hv t p _ _ true (Set.Subset.refl _)
 · apply lens_far Y H V G C a χ j' j hv.symm u v _ _ true; rw [Set.inter_comm]; exact Set.inter_subset_inter_right _ (Set.Subset.refl _)
 · apply flip_high Y H V G C a χ j j' hv _ _ t p (Set.Subset.refl _)
 · apply flip_high Y H V G C a χ j' j hv.symm _ _ u v; rw [Set.inter_comm]
 intro x y; unfold onceLens flipLens; dsimp only [LinearMap.comp_apply]; -- label implicit coe x nested
 obtain ⟨p,e⟩:= across_charge Y H V G C a χ j x.val (domain_mono Y H G (top_ready j j' hv) (mirror_support Y H G j x.val x.property)) y.val (domain_mono Y H G inter_subset_left y.property) t
 obtain ⟨p,h⟩:= across_charge Y H V G C a χ j' x.val (domain_mono Y H G (low_ready j j' hv) (mirror_support Y H G j' x.val x.property)) y.val (domain_mono Y H G inter_subset_right y.property) u
 exact e.trans h.symm
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
