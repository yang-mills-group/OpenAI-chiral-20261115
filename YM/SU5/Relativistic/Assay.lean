import YM.SU5.Relativistic.Sensitive

/-!
# Test nonfactorization of gauge inputs vs matter in the actual neutral mark itself

Hypothesis to refute: reading *this* mark by factoring the gauge from
matter. This is a statement about the evaluation, including the charged
marginal extension. The linear prediction assigning just products of marginal
means on these same variables can't match, quantitatively. Doesn't need
positivity of the comparison or matching of other statistics, or even to
assume the prediction is consistent on any other marks. Key is gauge symmetry
forcing the pure-matter marginal here to vanish.
-/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
section
variable (K:Calibration)(j:Axis)(p q:Cover)
local notation "ψ"=> remotePair j K p q
lemma visiblePair {S:Finset Cover}{f g:Family K} {wide:Bool}(x:InTest K wide S false f)(y:InTest K wide S false g):
    InTest K wide (reflectedBox j 0 (streetBox K p S) ∪ streetBox K q S) false (remotePair j K p q f g) :=
    ((axial K j 0 (cadTestFull S p ordinate _ _ x)).mono subset_union_left).mul ((cadTestFull S q ordinate _ _ y).mono subset_union_right)

variable {k:ℕ} (S:Finset Cover) (β:Fin k→ Cover) (W: Window.Family)
local notation "L₀"=> Lode K W β S
local notation "Χ"=> Filigree K W β S
local notation "Qφ" f:max g:max=> ψ (f:Family K) (g:Family K)
lemma mixedPredictor
    (μ : Family K→ℂ) (h : ∀ f∈ Lode K W β S,∀ g∈Lode K W β S, μ (remotePair j K p q f g)=0)
    (F : Dome K →ₗ[ℂ] ℂ) (t : ∀ f∈ Lode K W β S,∀ g∈ Lode K W β S,∀ A B:PairsC→ℂ,Coeff false S A → Coeff false S B→∀ x:Dome K,x.val=ψ (scalar K A*f) (scalar K B*g) → F x=μ (ψ (scalar K A) (scalar K B))* μ (ψ f g))
    (a b:Family K)(v:a∈ Filigree K W β S) (u:b∈ Filigree K W β S):∀ x:Dome K, x.val=ψ a b→ F x=0 := by
  have hz{f g:Family K}(h:f∈Χ)(q':g∈Χ): ∃ x:Dome K, x.val=ψ f g:= ⟨⟨ψ f g,(aux_test (visiblePair K j p q (FilTest h|>.widen) (FilTest q' |>.widen)))⟩,rfl⟩
  refine Submodule.span_induction₂ (p:=fun f g _ _=> ∀ x:Dome K,x.val=ψ f g → F x=0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ v u
  · rintro a b ⟨f,A,hf,hA,rfl⟩ ⟨g,B,hg,hB,rfl⟩ x hx
    rw [t f hf g hg A B hA hB x hx,h f hf g hg,mul_zero]
  · intro k c x hx; unfold remotePair at hx; rw [show cad K _ p 0= _ from zeroJourney p,show mirror K j 0 0=0 from ?_,zero_mul] at hx; rw [show x=0 from Subtype.ext hx,map_zero]
    simpa only [star_zero,zero_smul] using mirror_scale K j 0 (F:=1) 0
  · intro a _ x hx; unfold remotePair at hx; rw [show cad K _ q 0= _ from zeroJourney q,mul_zero] at hx; rw [show x=0 from Subtype.ext hx,map_zero]
  · intro a b c f g ω e u x hx; obtain ⟨A,hA⟩:=hz f ω; obtain ⟨B,hB⟩:=hz g ω
    rw [show x=A+B from ?_,map_add,e A hA,u B hB,add_zero]
    apply Subtype.ext; change _=A.val+B.val; rw [hx,hA,hB]; unfold remotePair; rw [cad_part,mirror_plus,add_mul]
  · intro a b c f g ω e u x hx; obtain ⟨A,hA⟩:=hz f g; obtain ⟨B,hB⟩:=hz f ω
    rw [show x=A+B from ?_,map_add,e A hA,u B hB,add_zero]
    apply Subtype.ext; change _=A.val+B.val; rw [hx,hA,hB]; unfold remotePair; rw [cad_part,mul_add]
  · intro z a b pA pB h x q; obtain ⟨A,hA⟩:=hz pA pB; rw [show x=star z • A from ?_,map_smul,h A hA,smul_zero]
    apply Subtype.ext; change _=star z • A.val; rw [q,hA]; unfold remotePair; rw [cad_scale,mirror_scale,Algebra.smul_mul_assoc]
  intro z a b pA pB h x q; obtain ⟨A,hA⟩:=hz pA pB; rw [show x=z • A from ?_,map_smul,h A hA,smul_zero]
  apply Subtype.ext; change _=z • A.val; rw [q,hA]; unfold remotePair; rw [cad_scale,Algebra.mul_smul_comm]
where
 zeroJourney (p:Cover) : cad K ordinate p 0=0:= by simpa only [zero_smul] using cad_scale K p ordinate 1 0
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.mixedPredictor
