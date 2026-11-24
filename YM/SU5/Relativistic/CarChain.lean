import YM.SU5.Relativistic.Docket
/-!
# Timestamped operators (unprojected).
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 280000
set_option synthInstance.maxSize 25000
set_option maxRecDepth 5500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Finset MeasureTheory
open SU Lattice Wilson Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E) (s : ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}
  (Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis) (J: Arena Y H Q.circuit j 0 false) (χ : displayAlgebra Y H V Q Qt j false J →⋆ₐ[ℂ] ℂ)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "Ν" => Slab (timeMesh Λ)
local notation "Ρ" => indoor Y H V Q Qt j false J χ
local notation "𝔅" => driveAlgebra Y H V Q Qt j false J
local notation "ρ" => procession Y H V Q Qt j false J χ
local notation "Ω" => doorstep Y H V Q Qt j false J χ
local notation "A" => (ride Y H V Q Qt j false J χ).E
local notation "S" => turnstile Y H V Q Qt j false J χ
local notation "P₀" t:max x:max p:max => entrance Y H V t Q Qt j false J x p
local notation "B₀" t:max x:max p:max => procession Y H V Q Qt j false J χ (P₀ t x p)
local notation "Qm" u:max => Marks (tent Y H) u
local notation "En" s:max w:max=> Entry Y H s j false w

local notation "U" => spacePos Y H V Q Qt j J χ
local notation "dock" => Docked Y H V s Q Qt j J
section lots
variable {Z:Type*}
/-- order of insertions in non-projected time bracing. Empty consumes nothing.
No axis encoded besides assignment of slab, available on projected chart too. -/
def inRow {M₁:Mesh} (f : Z → Slab M₁) : Stamp M₁ → List Z → Prop
| _, []=> True
| b,i::l=> b ≤ (f i).lower ∧ inRow f (f i).upper l
def bracing {μ:Mesh} {X:Type*} [Monoid X] (B:ℝ≥0→X) (f: Z→Slab μ) (A₁:Z→X) : Stamp μ → List Z→ X
| _, []=> 1
| b,i::l=> B (heatGap b (f i).lower)* A₁ i * bracing B f A₁ (f i).upper l

local notation "κ" t:max x:max => bud Y H V t Q Qt j false J χ x
local notation "δ" z:max x:max => relocate K j z x
variable (f : Z → Slab (timeMesh Λ)) (X : Z → Marks (tent Y H) false) (A₁: Z → driveAlgebra Y H V Q Qt j false J)
local notation "cart" b:max x:max => bracing A f (fun i=> (procession Y H V Q Qt j false J χ) (A₁ i)) b x
local notation "Rv" z:max=> response Y H V s Q Qt j false J χ z
set_option linter.unusedSectionVars false
lemma orderedGroups (l₁:List Z) (g:∀ i∈ l₁, Docked Y H V s Q Qt j J (f i) (X i) (A₁ i)) (b:ℤ) (p:inRow f (notch (timeMesh Λ) s b) l₁):
    ∃ y:Tower.Field Y H s j 0 false, ((bracing A f (fun i=> (procession Y H V Q Qt j false J χ) (A₁ i)) (notch (timeMesh Λ) s b) l₁) Ω)=bud Y H V s Q Qt j false J χ y ∧
        relocate K j b y.val=((l₁.map X).prod: Qm false).val := by
  induction l₁ generalizing b with
  | nil=>
    refine ⟨unity Y H j 0 false s,?_, relocate_unit K j b⟩
    change Ω=_; rw [root]
  | cons i l ih=>
    obtain ⟨r,w,h,t,m,x,hx0,lz⟩:=(g i List.mem_cons_self).certified
    have h₁: b ≤ r:= (stamp_le M s _ _).mp (h.symm ▸ p.1)
    obtain ⟨y,y₁,y₂⟩:= ih (fun i t=> g i (List.Mem.tail _ t)) (r+w) (t.symm ▸ p.2)
    obtain ⟨q,(h':b+(q:ℤ)=r)⟩:∃ q:ℕ,b+(q:ℤ)=r:=⟨(r-b).toNat,by omega⟩
    let Y₀:= tick Y H s j 0 false (2*q) (slabT Y H s j false w x y)
    refine ⟨Y₀, ?_, ?_⟩
    · have he: heatGap (N s b) (f i).lower = whenly M s q:=by rw [← h]; exact heatGap_stamp h' s
      change ((A _)* (procession Y H V Q Qt j false J χ (A₁ i)) * (cart ((f i).upper) l)) Ω= _ -- explicit to avoid
      rw [←lz,he, ContinuousLinearMap.mul_apply, ←t, y₁, ContinuousLinearMap.mul_apply, slotted, ride_ticks]
    unfold Y₀; rw [timed_apply, relocate_sums K j _ _ (field_test Y H s j 0 false (slabT Y H s j false w x y)), h', slab_eq,relocate_mul,relocate_sums K j _ _ (field_test Y H s j 0 false y), hx0, relocate_sums K j _ _ (marksSpec false (X i)).1, add_neg_cancel, relocate_zero K j (marksSpec false (X i)).1,y₂]; rfl
lemma calendarPrice (l₁:List Z)(g:∀ i∈ l₁,Docked Y H V s Q Qt j J (f i) (X i) (A₁ i)) (b:Stamp (timeMesh Λ))(z:Precise s b) (p:inRow f b l₁):
    inner ℂ Ω (((bracing (μ:=timeMesh Λ) A f (fun i=>ρ (A₁ i)) b l₁)) Ω)= response Y H V s Q Qt j false J χ ((l₁.map X).prod) := by
  obtain ⟨b,rfl⟩:=z
  obtain ⟨y,e,u⟩:= orderedGroups Y H V s Q Qt j J χ f X A₁ l₁ g b p
  rw [e,call,← waiting Y H V s Q Qt j false J χ (futureMark Y H s j false y) b]; exact congrArg (response Y H V s Q Qt j false J χ) (Subtype.ext u)
end lots
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.calendarPrice
