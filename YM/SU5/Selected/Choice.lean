import YM.SU5.Selected.Canton
import YM.SU5.Selected.DoubleLimit
/-!
# Choose a typical phase. Unique joint vacuum at all axes of this law & Hilbert `Birthplace`.

Room constructed with all **future** marks at positive time pooled using the very same transfer
of this law. Later restriction and symmetries needed for attempting relativistic continuum.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

open Localization Canton Companies TopologicalSpace
open scoped ContDiff
local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "P" => pipeline Y H V Q Qc j r C
local notation "uℋ" => basisRoom Y H V Q j r C
local notation "F" => queue Y H V Q Qc j r C
local notation "F₀" => (main (F)) -- default infers? 
variable {χ : CapCharacter Y H V Q Qc j r C} (p : Birthplace Y H V Q Qc j r C χ)
abbrev LoneVac : Prop := bottom Y H V Q Qc j r C p=Submodule.span ℂ {vacuum Y H V Q Qc j r C p}

variable (Z : Horizon Y H V Q Qc j r C) (hz : Law Y H V Q Qc j r C Z)
variable (U : ∀ i, Birthplace Y H V Q Qc j r C (Z.character i))
local notation "Γ" i:max => schematic Y H V Q Qc j r C (Z.character i)
local notation "θ" i:max => bottom Y H V Q Qc j r C (U i)
local notation "x₀" s:max => asLeg Y H V Q Qc j r C s
local notation "η" i:max => (Γ i).bloom (U i)
local notation "λ₀" i:max => vacuum Y H V Q Qc j r C (U i)
local notation "π" i:max => (θ i).starProjection
local notation "κ" s:max x:max => toTest Y H j r s x
local notation "α" i:max => Z.character i
-- before and after lower moments judge. proof irrelevance near complete spaces
private lemma transfer_norms (X' : Hilbert) (p q : Submodule ℂ X') (h : p=q)
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection] (z : X') : ‖p.starProjection z‖=‖q.starProjection z‖ := by subst p; rfl
-- large type helper using turnout
include V Q Qc C
local notation "F'" => efforts Y H V Q Qc j r C -- Υ
lemma prewidth (s : ℕ) (x : F₊ s) : ‖(stationary A F').starProjection (((x₀ s) x).val Ω)‖=‖(N s) (κ s x) Ω‖ := by
  refine (transfer_norms _ _ (R) (turnoff Y H V Q Qc j r C) _).trans ?_
  change ‖π₀ ((prepare Y H V Q Qc j r C s x) Ω)‖ = _
  rw [planted,cap_prepares]
include Z hz U
-- apply `balance` and `narrow`.
lemma priced (x : P) : Integrable (fun i=> ‖(π i) ((η i) x)‖^2) Z.μ ∧
    (∫ i, ‖(π i) ((η i) x)‖^2 ∂Z.μ)=‖(stationary A F').starProjection (x.val Ω)‖^2 :=
  balance (X:=uℋ) (Y:=A) («P»:=P) Ω Z hz (fun i=> Γ i) U (F) (hat_le Y H V Q Qc j r C) x

omit hz in
lemma culmination (s : ℕ) (x : F₊ s) (i : Z.X) :
    inner ℂ (λ₀ i) ((π i) ((η i) ((x₀ s) x))) = (α i) ((M s) (κ s x)) :=
  (stays_is _ _ _ _ (apt_floor Y H V Q Qc j r C (U i))).trans (actual_expect Y H V Q Qc j r C (U i) s x) -- infer

lemma validator (s : ℕ) (x : F₊ s) :
    ∀ᵐ i ∂Z.μ,(π i) ((η i) ((x₀ s) x)) = (α i) ((M s) (κ s x)) • (λ₀ i) := by
  have h := priced Y H V Q Qc j r C Z hz U ((x₀ s) x)
  exact narrow (X:=uℋ) Ω Z hz (fun i=> (U i).H) (fun i=>(π i) ((η i) ((x₀ s) x))) (fun i=> λ₀ i) ((M s) (κ s x)) h.1 (fun i=> vacuum_norm Y H V Q Qc j r C (U i)) (culmination Y H V Q Qc j r C Z U s x) (h.2.trans (congrArg (fun n:ℝ=> n^2) (prewidth Y H V Q Qc j r C s x)))
omit Z hz U in
private lemma represented (g : (P) → Prop) (x : P) (h : ∀ (s : ℕ) (y : F₊ s), g ((x₀ s) y)) : g x := by
  obtain ⟨s,y,hx,e⟩ := leg_available Y H V Q Qc j r C x 0; exact (show x=(x₀ s) y from Subtype.ext e) ▸ h s y
omit Z hz U C V Q Qc in
private lemma span_mem (X' : Type) (H' : X'→Hilbert) (a : X' → ℂ) (f g : ∀ i : X', H' i) (μ : Filter X')
    (t : ∀ᶠ i in μ, f i=a i • g i) : ∀ᶠ i in μ, f i ∈ Submodule.span ℂ {g i} :=
  t.mono fun i v=> Submodule.mem_span_singleton.mpr ⟨_,v.symm⟩
lemma validated (x : P) : ∀ᵐ i ∂Z.μ,(π i) ((η i) x)∈ Submodule.span ℂ {λ₀ i} :=
  represented Y H V Q Qc j r C (fun x=>∀ᵐ i ∂Z.μ,(π i) ((η i) x)∈ Submodule.span ℂ {λ₀ i}) x
    (fun s y=> span_mem Z.X (fun i => (U i).H) _ _ _ _ (validator Y H V Q Qc j r C Z hz U s y))

lemma crowd (t : ℕ→P) (ht : DenseRange t) : ∀ᵐ i ∂Z.μ, LoneVac Y H V Q Qc j r C (U i) := by
  have h := ae_all_iff.mpr fun n => validated Y H V Q Qc j r C Z hz U (t n)
  filter_upwards [h] with i hi
  refine irreducible («A»:= (U i).H) («F»:= (η i) ∘ t) _ _ (apt_floor Y H V Q Qc j r C (U i)) ?_ (fun n=> hi n)
  exact ((Γ i).bloom_dense (U i)).comp ht (continuous_bloom (X:=uℋ) (Y:=A) (P) («B»:= (B)) isClosed_closure (α i) (Γ i) (U i))

omit C hz U Z
-- for all axes at once. `r=false` charges included! will show restriction to neutral etc separately.
variable (C' : ∀ a : Axis,Arena Y H Q.circuit a 0 false)
    (Z' : Horizon Y H V Q Qc j false (C' j)) (hz' : Law Y H V Q Qc j false (C' j) Z')
    (U' : ∀ v i, Birthplace Y H V Q Qc v false (C' v) ((emigrant Y H V Q Qc j false (C' j) Z' v (C' v)).character i))
    {Z₀ : Tapestry.Rack Λ l} {P₁ : Tapestry.Clay Λ l} (T : Tapestry.Exhibition Y H i k I E Z₀ P₁)
local notation "A*" v:max => Arena Y H Q.circuit v 0 false
local notation "L₀" v:max => emigrant Y H V Q Qc j false (C' j) Z' v (C' v)
include C' hz' U' T
lemma typical : ∀ᵐ i ∂Z'.μ, ∀ (v : Axis), LoneVac Y H V Q Qc v false (C' v) (U' v i) := by
  apply ae_all_iff.mpr; intro v
  let P' := pipeline Y H V Q Qc v false (C' v)
  haveI : TopologicalSpace.SeparableSpace (P') := small_pipe Y H V Q Qc v (C' v) T
  exact crowd Y H V Q Qc v false (C' v) (L₀ v) (brought Y H V Q Qc j false (C' j) Z' hz' v (C' v)) (U' v) (denseSeq ↑(P')) (denseRange_denseSeq _)
end YM.CF.Buffered.Afterglow.Tower.Selection
