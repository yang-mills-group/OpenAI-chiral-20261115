import YM.SU5.Twilight.Directions
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine

/-! Supplement to `Twilight/Directions`: linearity of `viewF`. -/
private lemma linear_of_gram {H : Hilbert} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (f : E → H) (ϕ : E → (E →ₗ[ℂ] ℂ)) (h : ∀ x y, inner ℂ (f x) (f y) = ϕ x y) :
    (∀ x y, f (x+y) = f x + f y) ∧ ∀ (c : ℂ) x, f (c • x) = c • f x := by
  constructor
  · intro x y
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜:=ℂ)]
    simp only [inner_sub_left,inner_add_left,inner_sub_right,inner_add_right,h,map_add]
    ring
  intro c x
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜:=ℂ)]
  simp only [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,h,map_smul,smul_eq_mul]
  ring

variable (P : Spine) (j : Axis) (x : P.Spectrum0 j) (s : ℕ)
local notation "K" => P.calibration
local notation "H" => P.ColorHil j x
local notation "V" => P.viewF j x s

/-- Linear domain (`birthF`). -/
def births : Submodule ℂ P.Test where
  carrier := {f | P.birthF j s f}
  zero_mem' := ⟨⟨0,(enclave K).zero_mem⟩,rfl⟩
  add_mem' := by
    rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨⟨a.val+b.val,(enclave K).add_mem a.property b.property⟩,rfl⟩
  smul_mem' := by
    rintro c _ ⟨a,rfl⟩
    exact ⟨⟨c • a.val,(enclave K).smul_mem a.property c⟩,rfl⟩

local notation "E" => P.births j s

def viewHom : E →ₗ[ℂ] H := by
  let f := fun z : E => P.viewF j x s (f:=z.val) z.property
  let ϕ (z : E) : E →ₗ[ℂ] ℂ :=
    (P.singleState j s x).comp (((LinearMap.mul ℂ P.Test) (P.reflectTest j z.val)).comp (E).subtype)
  have h := linear_of_gram f ϕ <| fun z w => P.released_gram j x s z.property w.property
  exact ⟨⟨f,h.1⟩,h.2⟩

lemma view_sub {f g : P.Test} (p : f ∈ E) (q : g ∈ E) :
    P.viewF j x s (f:=f-g) ((E).sub_mem p q) = P.viewF j x s p - P.viewF j x s q :=
  LinearMap.map_sub (P.viewHom j x s) ⟨f,p⟩ ⟨g,q⟩

-- general sum even for hypotheses only on finite summation set
lemma view_sum {ι : Type*} (F : ι → P.Test) (Y : ι → H) (I : Finset ι)
    (h : ∀ i ∈ I, ∃ p : F i ∈ E, P.viewF j x s p = Y i) :
    ∃ p : ∑ i ∈ I, F i ∈ E, P.viewF j x s p = ∑ i ∈ I, Y i := by
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨(E).zero_mem,map_zero (P.viewHom j x s)⟩
  | @insert i l hi ih =>
    obtain ⟨p,hp⟩ := h i (Finset.mem_insert_self ..)
    obtain ⟨q,hq⟩ := ih fun i w => h i (Finset.mem_insert_of_mem w)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨(E).add_mem p q,
      (LinearMap.map_add (P.viewHom j x s) ⟨F i,p⟩ ⟨∑ i ∈ l, F i,q⟩).trans (congrArg₂ (·+·) hp hq)⟩
lemma view_smul {f : P.Test} (p : f ∈ E) (c : ℂ) :
    P.viewF j x s ((E).smul_mem c p) = c • P.viewF j x s p :=
  LinearMap.map_smul (P.viewHom j x s) c ⟨f,p⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
