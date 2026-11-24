import YM.SU5.Relativistic.MultiMark
import YM.SU5.Selected.Distant

/-!
# Calibrated region semantics on the election
-/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction

open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open SU Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark SelectionAnalysis Set
open Journey Tapestry Tapestry.Altitude PhaseChoice Selected
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable (Λ : Preparation) (l s:ℕ) (S : Finset Cover)
local notation "R" => Journey.reserve Λ l
local notation "g" => Selected.gaugeMesh Λ s
local notation "pʹ" x:max i:max => Selected.gaugePosition Λ s x i

/-- Scale by region functions; identify both workers' collars. -/
lemma gaugeLocation (x:Cover) : Selected.gaugePosition Λ s x = PhaseChoice.location Λ s x := by
  funext i
  unfold PhaseChoice.location gaugePosition gaugeMesh markZ precisionAt
  ring

def collarLower (x:Cover): Axis→ℝ := fun i=> PhaseChoice.location Λ s x i - (Journey.reserve Λ l:ℝ)*Selected.gaugeMesh Λ s
def collarUpper (x:Cover): Axis→ℝ := fun i=> PhaseChoice.location Λ s x i + (Journey.reserve Λ l:ℝ)*Selected.gaugeMesh Λ s

def collar (x:Cover):Set RSpace := Set.Icc (collarLower Λ l s x) (collarUpper Λ l s x)
lemma lower_gauge (x:Cover) (i:Axis) : collarLower Λ l s x i= pʹ x i- R*g:=by unfold collarLower; rw [gaugeLocation]
lemma upper_gauge (x:Cover) (i:Axis) : collarUpper Λ l s x i= pʹ x i+R*g:=by unfold collarUpper; rw [gaugeLocation]
lemma meter_size : 2*(Tapestry.precisionAt Λ s)* Selected.gaugeMesh Λ s=1:= by
  have ht:2*Tapestry.precisionAt Λ s ≠ 0:=mul_ne_zero two_ne_zero (Tapestry.positiveScale ..).ne'
  exact mul_one_div_cancel ht
lemma shield_collar (x:Cover) : Tapestry.shield Λ l s x= handstamp (collar Λ l s x):=by
  ext u
  let F:RSpace:=fun i=> u i / 2
  change (∀ i:Axis, |Tapestry.precisionAt Λ s*u i-(x i:ℝ)| ≤ (R:ℝ)) ↔
    (collarLower Λ l s x ≤ F ∧ F ≤ collarUpper Λ l s x)
  let P:=Tapestry.precisionAt Λ s
  have hx : ∀ i:Axis,
      |P*u i-(x i:ℝ)| ≤ (R:ℝ) ↔ (collarLower Λ l s x i ≤ F i ∧ F i ≤ collarUpper Λ l s x i):=by
    intro i
    have he:2*P*g=1:= meter_size ..
    have ht:0<g:= Selected.gaugeMesh_pos Λ s
    rw [lower_gauge,upper_gauge]; unfold F gaugePosition
    rw [abs_le]; constructor
    · rintro ⟨h,h'⟩; constructor <;> nlinarith only [mul_le_mul_of_nonneg_right h ht.le,mul_le_mul_of_nonneg_right h' ht.le,show 2*P*g*u i=u i by rw [he]; simp]
    rintro ⟨h,h'⟩
    constructor
    · apply le_of_mul_le_mul_right ?_ ht
      nlinarith only [h, show 2*P*g*u i=u i by rw [he]; simp]
    apply le_of_mul_le_mul_right ?_ ht
    nlinarith only [h',show 2*P*g*u i=u i by rw [he]; simp]
  constructor
  · intro h; exact ⟨fun i=> ((hx i).1 (h i)).1,fun i=> ((hx i).1 (h i)).2⟩
  rintro ⟨h,q⟩ i; exact (hx i).2 ⟨h i,q i⟩

/-- A compact physical footprint paying every observation of the support budget. -/
def footprint : Set RSpace := ⋃ x∈ (S:Set Cover), collar Λ l s x
lemma has_footprint : SupportedPhysically Λ l s S (footprint Λ l s S):=by
  intro x h
  rw [shield_collar]; exact Set.preimage_mono (subset_iUnion_of_subset x (subset_iUnion (fun (_: x∈(S:Set Cover))=> collar Λ l s x) h))
lemma covers_footprint (n:ℕ) : footprint Λ l (s+n) (volumeAround Λ l n S) ⊆ footprint Λ l s S:=by
  intro u h
  obtain ⟨x, hx⟩:= Set.mem_iUnion.mp h
  obtain ⟨hx,h⟩:= Set.mem_iUnion.mp hx
  let v:RSpace:=fun i=>2*u i; have he: (fun i:Axis=> v i/2)=u:=by unfold v; ext; ring
  have hs : v∈ Tapestry.shield Λ l (s+n) x:=by rw [shield_collar]; change (fun i:Axis=>v i/2)∈ collar Λ l (s+n) x; rw [he]; exact h
  have ht:= (has_footprint Λ l s S).persists n x hx hs
  change (fun i:Axis=>v i/2) ∈ footprint Λ l s S at ht; rwa [he] at ht
lemma footprint_compact : IsCompact (footprint Λ l s S) := S.finite_toSet.isCompact_biUnion (fun _ _=> isCompact_Icc)
lemma footprint_separation (T : Finset Cover) (i:Axis)(δ:ℝ)(h : PhysicalHush (Λ:=Λ) (l:=l) s i S T δ) (x y : RSpace) (p:x∈ footprint Λ l s S)(q:y∈ footprint Λ l s T):
    x i+δ ≤ y i:=by
  obtain ⟨a,hx⟩:= Set.mem_iUnion.mp p; obtain ⟨hx,y₀⟩:= Set.mem_iUnion.mp hx
  obtain ⟨b,hy⟩:= Set.mem_iUnion.mp q; obtain ⟨hy,y₁⟩:= Set.mem_iUnion.mp hy
  have he : collarUpper Λ l s a i + δ ≤ collarLower Λ l s b i := by
    rw [lower_gauge, upper_gauge]
    exact h.2 0 a hx b hy
  have h₁:= (y₀: x∈ collar Λ l s a).2 i
  have h₂:= (y₁: y∈ collar Λ l s b).1 i
  linarith only [h₁,h₂,he]
lemma footprint_disjoint (T : Finset Cover) (i:Axis)(δ:ℝ)(h : PhysicalHush (Λ:=Λ) (l:=l) s i S T δ) :
    Disjoint (footprint Λ l s S) (footprint Λ l s T):= by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have t := footprint_separation Λ l s S T i δ h x x hx hy
  linarith only [t,h.1]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.footprint_disjoint
