import YM.SU5.Selected.Gauge
import YM.SU5.Selected.Loewner
/-!
# A C*-algebra of the common slab tower (at this discrete-transverse stage)

It stores the full Entry experiment (including multiplication across s),
and time/spatial stamps and their orientation, ON the same unselected H.
Compression gives not a *-homomorphism but a unital positive linear map
into the ground algebra. Use this to take care with factorization vs
operator product questions. E.g., it is evaluation on the compression of
X*Y (a single operator), not on the product of compressions, that gives a
sector's answer for X*Y!

These algebras are not asserted relativistic (local net generators not
identified, symmetries still limited, spatial translation only claimed on
the meshes, etc.).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 260000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "R" => Aurora Y H V Q j strict C
local notation "ℛ" => groundRoom Y H V Q j strict C
local notation "𝒪" => observable (tent Y H) strict
local notation "π" => (R).orthogonalProjectionOnto
local notation "ω" => floorV Y H Q.circuit j 0 strict C
local notation "Ω" => seat0 Y H V Q j strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝒳" t:max => cap Y H V t Q Qt j strict C
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "β" s:max f:max p:max => boxOp Y H V s Q Qt j strict C _ f p
local notation "U" v:max => ((ladder Y H V Q.circuit j 0 strict C).crew v).play
local notation "Λ₀" => timeMesh Λ
local notation "v₀" s:max n:max => whenly (timeMesh Λ) s n
local notation "τ" x:max => advance Y H V Q.circuit j 0 strict C x

section closure
open scoped Pointwise

/-- Stamp submonoid can be represented without choosing a common ordering. -/
def breezes : Set ((Ark.Ht Y H Q.circuit j 0 strict C).Op) :=
  {x | ∃ (a : Trans j) (z : MeshClock.marks (timeMesh Λ)), x=(U a) z}
def objects : Set ((Ark.Ht Y H Q.circuit j 0 strict C).Op) :=
  {x | ∃ (s w : ℕ) (f : Entry Y H s j strict w) (p : 0 < w), x=boxOp Y H V s Q Qt j strict C w f p}
def driveAlgebra : StarSubalgebra ℂ ((Ark.Ht Y H Q.circuit j 0 strict C).Op) :=
  (StarAlgebra.adjoin ℂ (objects Y H V Q Qt j strict C ∪ breezes Y H V Q j strict C)).topologicalClosure
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "Xα" => breezes Y H V Q j strict C
local notation "Bα" => objects Y H V Q Qt j strict C
local notation "Z" => Bα ∪ Xα

instance drive_closed : IsClosed (𝔅 : Set (A).Op) := isClosed_closure
-- StarSubalgebra.cstarAlgebra automatically with this?
instance drive_starordered : StarOrderedRing (𝔅) := SelectionAnalysis.subtypeOrder _
instance display_starordered : StarOrderedRing (𝔄) := SelectionAnalysis.subtypeOrder _

variable {v z : (Ark.Ht Y H Q.circuit j 0 strict C).Op}
lemma object_at {w : ℕ} (f : Entry Y H s j strict w) (p : 0 < w) : β s f p ∈ objects Y H V Q Qt j strict C := ⟨s,w,f,p,rfl⟩
lemma object_in_drive {w : ℕ} (f : Entry Y H s j strict w) (p : 0 < w) :
    β s f p ∈ driveAlgebra Y H V Q Qt j strict C := StarSubalgebra.le_topologicalClosure (StarAlgebra.adjoin ℂ Z)
      (StarAlgebra.mem_adjoin_of_mem ℂ (Or.inl (object_at Y H V s Q Qt j strict C f p))) -- check Z notation

lemma rotated_in (x : Trans j) (z : marks (timeMesh Λ)) :
    (U x) z ∈ driveAlgebra Y H V Q Qt j strict C := StarSubalgebra.le_topologicalClosure (StarAlgebra.adjoin ℂ Z)
      (StarAlgebra.mem_adjoin_of_mem ℂ (Set.mem_union_right Bα (show _ ∈ Xα from ⟨x,z,rfl⟩)))
lemma heated_in (s n : ℕ) : advance Y H V Q.circuit j 0 strict C (whenly (timeMesh Λ) s n)
    ∈ driveAlgebra Y H V Q Qt j strict C := by
  rcases Nat.eq_zero_or_pos n with rfl|p
  · rw [when_zero, advance_source]; exact (𝔅).one_mem
  rw [← ticket_birth Y H V s Q Qt j strict C n p]
  exact object_in_drive Y H V s Q Qt j strict C _ p
lemma clock_at {v : ℝ≥0} (h : v ∈ times (timeMesh Λ)) : τ v ∈ driveAlgebra Y H V Q Qt j strict C := by
  obtain ⟨s,t,rfl⟩ := MeshClock.split _ h; exact heated_in Y H V Q Qt j strict C s t

lemma objects_mul (p : v ∈ Bα) (u : z ∈ Bα) : v*z ∈ objects Y H V Q Qt j strict C := by
  obtain ⟨s,w,f,k,rfl⟩ := p; obtain ⟨t,x,g,q,rfl⟩ := u
  rw [refined_box Y H V s Q Qt j strict C w f k _ (le_max_left s t),
    refined_box Y H V t Q Qt j strict C x g q _ (le_max_right s t),
    ContinuousLinearMap.mul_def, edit_comp]
  apply object_at
lemma objects_star (p : z ∈ Bα) : star z ∈ objects Y H V Q Qt j strict C := by
  obtain ⟨s,w,f,h,rfl⟩ := p
  change (β s f h).adjoint ∈ _; rw [respects]; apply object_at
lemma breeze_star (p : z ∈ Xα) : star z ∈ breezes Y H V Q j strict C := by
  obtain ⟨x,k,rfl⟩ := p
  exact ⟨x,-k,Germ.Players.neg_adjoint _ _⟩ -- arg order
lemma breeze_fixes (p : z ∈ Xα) (x : ℛ) : z x.val = x.val := by
  obtain ⟨b,i,rfl⟩ := p; obtain ⟨s,t,rfl⟩ := notch_exists Λ₀ i
  rw [on_ladder]
  exact ((Vacancy.formal Y H V s Q j strict C _).1 (((Submodule.mem_iInf _).mp x.property) s)).2 b t
lemma steadies (p : z ∈ Submonoid.closure Xα) (x : ℛ) : z x.val = x.val := by
  induction p using Submonoid.closure_induction with
  | one => rfl
  | mem x p => exact breeze_fixes Y H V Q j strict C p _
  | mul _ _ _ _ p q => rw [ContinuousLinearMap.mul_apply, q, p]
include V Q Qt
lemma winds (p : v ∈ Xα) (q : z ∈ Bα) : ∃ x ∈ objects Y H V Q Qt j strict C, v*z=x*v := by
  obtain ⟨x,z',rfl⟩ := p; obtain ⟨t,i,rfl⟩ := notch_exists Λ₀ z'
  obtain ⟨s,w,f,p,rfl⟩ := q
  rw [refined_box Y H V s Q Qt j strict C w f p _ (le_max_left s t), ← notch_up Λ₀ t _ (le_max_right s t)]
  refine ⟨_, ?_, (show _ = _ from shape_across Y H V (max s t) Q Qt j strict C _ (furnished Y H s Q j strict w f (max s t) (le_max_left s t)) (Nat.mul_pos (pow_pos Λ.R.L.property _) p) x (castor Λ₀ t (max s t) i))⟩
  apply object_at
-- note include Q implicit record

/-- In this lemma any *word as operator* in the generated submonoid has only
one residual slab, unless no input boxes have been used, and a spatial stamp
fixing the joint ground. In particular true even when input resolutions vary. -/
theorem normal_form (h : v ∈ Submonoid.closure (Z ∪ star Z)) :
    ∃ x : (A).Op, x ∈ Submonoid.closure Xα ∧ (v = x ∨ ∃ a, a ∈ Bα ∧ v = a*x) := by
  induction h using Submonoid.closure_induction_left with
  | one => exact ⟨1,Submonoid.one_mem _, Or.inl rfl⟩
  | mul_left x p v z t =>
    have ht : x ∈ Z := by -- Z local notation? v=z etc
      rcases p with p|p; · exact p
      change star x ∈ Z at p
      rcases p with p|p
      · exact Or.inl (star_star x ▸ objects_star Y H V Q Qt j strict C p)
      exact Or.inr (star_star x ▸ breeze_star Y H V Q j strict C p)
    obtain ⟨k,p,h⟩ := t
    rcases ht with ht|ht
    · refine ⟨k,p, Or.inr ?_⟩; rcases h with rfl|⟨a,q,rfl⟩
      · exact ⟨x,ht,rfl⟩
      exact ⟨x*a,objects_mul Y H V Q Qt j strict C ht q,(mul_assoc ..).symm⟩
    refine ⟨x*k,Submonoid.mul_mem _ (Submonoid.subset_closure ht) p,?_⟩
    rcases h with rfl|⟨w,p,rfl⟩
    · exact Or.inl rfl
    obtain ⟨a,q,u⟩ := winds Y H V Q Qt j strict C ht p
    exact Or.inr ⟨a,q, (mul_assoc x w _).symm.trans ((congrArg (· * k) u).trans (mul_assoc a x _))⟩

abbrev compress : (A).Op →L[ℂ] (groundRoom Y H V Q j strict C).Op := SelectionAnalysis.squeeze (R)
local notation "W₀" => compress Y H V Q j strict C
lemma compress_entry {w : ℕ} (f : Entry Y H s j strict w) (p : 0 < w) : W₀ (β s f p) = (𝒳 s) (actorLabel Y H s j strict f.val) := (cap_of_entry Y H V s Q Qt j strict C f p).symm
lemma compress_basis (p : z ∈ Submonoid.closure (Z ∪ star Z)) : W₀ z ∈ 𝔄 := by
  obtain ⟨x,u,d⟩ := normal_form Y H V Q Qt j strict C p
  have hf := steadies Y H V Q j strict C u
  rcases d with rfl|⟨a,⟨s,w,f,e,rfl⟩,rfl⟩
  · rw [show W₀ z=1 from ?_]
    · exact (𝔄).one_mem
    ext1 x; change π (z x.val)=x
    rw [hf x,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [show W₀ ((β s f e)*x)= W₀ (β s f e) from ?_, compress_entry]
  · apply cap_displayed
  ext1 z; change π ((β s f e) (x z.val)) = π ((β s f e) z.val); rw [hf z]

lemma compress_in (h : v ∈ 𝔅) : W₀ v ∈ 𝔄 := by
  have ht {u} (p : u ∈ StarAlgebra.adjoin ℂ Z) : W₀ u ∈ 𝔄 := by
    let W := Submodule.comap (W₀).toLinearMap (𝔄).toSubalgebra.toSubmodule
    have hp : (StarAlgebra.adjoin ℂ Z).toSubalgebra.toSubmodule ≤ W := by
      rw [StarAlgebra.adjoin_eq_span]
      exact Submodule.span_le.mpr fun z p => compress_basis Y H V Q Qt j strict C p
    exact hp p
  exact closure_minimal (s:=(StarAlgebra.adjoin ℂ Z : Set (A).Op))
    (fun _ e => ht e) ((displayClosed Y H V Q Qt j strict C).preimage (W₀).continuous) h

def reduceToDisplay : (driveAlgebra Y H V Q Qt j strict C) →L[ℂ] (displayAlgebra Y H V Q Qt j strict C) :=
  ((W₀).comp (𝔅).toSubalgebra.toSubmodule.subtypeL).codRestrict (𝔄).toSubalgebra.toSubmodule
    (fun i => compress_in Y H V Q Qt j strict C i.property)
local notation "W₁" => reduceToDisplay Y H V Q Qt j strict C
lemma reduce_val (x : 𝔅) : (W₁ x).val=(π).comp (x.val.comp (R).subtypeL) := rfl
lemma reduce_origin : W₁ 1 = 1 := Subtype.ext (SelectionAnalysis.squeeze_one _)
lemma reduce_nonneg {x : 𝔅} (p : 0 ≤ x) : 0 ≤ W₁ x := by
  -- inherited Loewner
  exact SelectionAnalysis.squeeze_nn (R) (x:=x.val) p
lemma reduce_mean (x : 𝔅) : inner ℂ Ω ((W₁ x).val Ω) = inner ℂ ω (x.val ω) := by
  change inner ℂ Ω (π (x.val ω)) = _; rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]; rfl

/-- All caps are reductions of actual positive slab placements (positive *time*, not signs). -/
lemma cap_has_source (x : Beacon K strict) : instrument Y H V Q Qt j strict C x ∈
    Set.range (fun z : 𝔅 => (W₁ z).val) := by
  let X := Classical.choice (anyporch Y H x.1 j strict x.2)
  exact ⟨⟨_,object_in_drive Y H V x.1 Q Qt j strict C X.fwd X.pos⟩, (onAny Y H V x.1 Q Qt j strict C X).symm⟩

/-- Temporal and even transverse stamps on the drive algebra. -/
def shiftStamp (x : Trans j) (d : marks (timeMesh Λ)) : 𝔅 := ⟨(U x) d,rotated_in Y H V Q Qt j strict C x d⟩
def heatStamp (n : ℕ) : 𝔅 := ⟨advance Y H V Q.circuit j 0 strict C (whenly (timeMesh Λ) s n), heated_in Y H V Q Qt j strict C _ _⟩

def entrance {w : ℕ} (F : Entry Y H s j strict w) (p : 0 < w) : 𝔅 :=
  ⟨β s F p,object_in_drive Y H V s Q Qt j strict C F p⟩
end closure
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.normal_form
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.reduceToDisplay
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.reduce_mean
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.reduce_nonneg
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.drive_starordered
