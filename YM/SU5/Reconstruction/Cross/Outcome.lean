import YM.SU5.Reconstruction.Cross.Separated
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
/-! CP-B Bool contour price attached to THE chosen separated stencil and specifically that Shelf. -/
open _root_.YM.SelectionAnalysis Vacancy.Average
section
variable (S : Bool → Finset Cover) (F : Bool → Marks (tent Y H) false)
local notation "Θ" => Marks (tent Y H) false
local notation "L" => [false,true]
local notation "Λ₀" => timeMesh Λ
local notation "Z" t:max=> fun i:Bool=> upGrade Y H s Q false (F i) t
local notation "U" x:max=> silhouette Λ l s (S x)
variable (P : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
local notation "C₁" k:max=> Selected.displacement Y H V Q Qt j false C c k (P k)
local notation "Ψ" t:max k:max=> electedAtlas Y H V Q Qt t k (P k) (C₁ k)
local notation "ζ" v:max=> gridChart Μ v
local notation "Π₄"=> commonR Y H V Q Qt s j C c F [false,true] P
local notation "f₀"=> F false*F true
local notation "Πw"=> (Eχ s) (F false* F true)

-- This is a bill, specialized to even marks, including non-neutral when appropriate.
-- Keep geometry fixed and high-lifted with the physical prescription!
def ObservedPaid (δ k:ℝ) :Prop:=   ∀ᶠ t in atTop,∃ (g:∀ i:Axis,∀ x:Bool,Gate Y H t i (upGrade Y H s Q false (F x) t)) (X:Set (Bool→Axis→ℝ)),
     Π₄ 0=Πw ∧ X∈𝓝 (0 : Bool → Axis→ℝ) ∧ X⊆ arenaRegion Y H Q s F [false,true] ∧ IsOpen X ∧
     -- keep spatial support
     (∀ w∈X,∀ x∈ U false,∀ y∈ U true,∀ i,x i+w false i+δ/2 ≤ y i+w true i) ∧
     (∀ w∈X,k< ‖Π₄ w‖) ∧
     (∀ i:Axis, (∃ lo:ℤ, Leaves Y H t i (Z t) (g i) lo [false,true]) ∧ (∀ w∈X,(∀ x,(g i x).within_ (w x)) ∧ Π₄ w=(Ψ t i) (Z t) (g i) L w) ∧ ∀ v:Bool→seeMesh Μ, ζ v∈X→ Π₄ (ζ v) =rawTrace Y H V Q Qt t i (P i) (C₁ i) (Z t) (g i) [false,true] v) ∧
     -- carry positive-width contour price to real times in that axis (with shifts). cost at EACH axis simultaneously, true Mink cigar, not point field.
     ∀ᶠ w : (Bool→Axis→ℝ)×(Bool→ℝ) in 𝓝 (0,0),w.1∈X ∧ ∀ i:Axis,k<‖edgeArrival Y H V Q Qt t i (P i) (C₁ i) (Z t) (g i) [false,true] w‖

end
variable (j' : Axis) -- axis of Exceeds produced; j axis of election
variable (P : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
local notation "C₁" k:max=> Selected.displacement Y H V Q Qt j false C c k (P k)
variable (t : Marks (tent Y H) true) (z : SU.Slot) (X': Finset Cover) (o:Cover) (n w: ℕ) (p q:Cover) (δ:ℝ)

noncomputable def pairBounds (V:Calibration) (X:Finset Cover) (a:Axis) (p q:Cover) (x:Bool) := if x then rightCell V q X else leftCell a V p X
noncomputable def expressesPair (f: Marks (tent Y H) true) (a:Axis) (p q:Cover) (x:Bool) : Marks (tent Y H) false:= if x then bosonLabel K (relocateWorld Y H true q f) else bosonLabel K (Selected.mirrorInMarks Y H a true (relocateWorld Y H true p f))

def carried : Prop :=
     Exceeds Y H V s Q Qt j' (P j') (C₁ j') δ t z X' o n w p q ∧ ObservedPaid Y H V Q Qt s j C c (pairBounds (tent Y H) X' j' p q) (expressesPair Y H t j' p q) P δ (1/33) -- output axes all
lemma important (v:Exceeds Y H V s Q Qt j' (P j') (C₁ j') δ t z X' o n w p q)
    (h : ThresholdInteraction Y H V s Q Qt j' (P j') X' (C₁ j') t z o n w) : carried Y H V Q Qt s j C c j' P t z X' o n w p q δ:=by
 refine ⟨v,?_⟩
 let S:=pairBounds (tent Y H) X' j' p q
 let F:=expressesPair Y H t j' p q
 obtain ⟨a,b⟩:= footprint_pair Y H j' X' n w o z _ p q h.witness.link.mark_mem
 apply priced_opens Y H V Q Qt s j C c S F (show 0<δ from (v.shelf.span_positions j').1) (fun i=> ?_) (fun i _ a _ t=> stamp_range (v.shelf.span_positions i) a t) P (1/33) ?_ v.shelf.structured
 · rw [← across_response Y H V s Q Qt j false C c _ j' (P j')]
   have hx:1/32 ≤ ‖response Y H V s Q Qt j' false (P j') (C₁ j') (F false* F true)‖:= v.shelf.consumption
   linarith
 cases i; exact a.widen; exact b.widen
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.important
