import YM.SU5.Selected.HalfSteps
/-!
# A plant over the phase algebra

On the *same* Hilbert space (not yet the disintegrated OS system), regard x future field as
operator $R → H$ out of the joint ground space. Then maps o_u induced by any operator valued
input `snap` on R become entries of a single matrix of reads on the sector. This lift is used
like a Hilbert module but needs only the actual concrete C* representation. Unit, translations
and resolutions explicitly checked where used.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 260000
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

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "θ" s:max => boxOp Y H V s Q Qc j r C
local notation "ι₀" => (R).subtypeL
local notation "J" => (↑(R) →L[ℂ] (A))
local notation "ε₀" => advance Y H V Q.circuit j 0 r C
variable (s : ℕ)
include V Q Qc C
lemma nested_width (w k : ℕ) (x : Entry Y H s j r w) (p : 0 < w) (v : Entry Y H s j r k)
    (q : 0 < k) (h : x.val=v.val) : ((θ s) w x p).comp ι₀ = ((θ s) k v q).comp ι₀ := by
  wlog he : w ≤ k generalizing k w x v
  · exact (this k w v q x p h.symm (by omega)).symm
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le he
  rw [SlabMark.shape_right Y H V s Q Qc j r C w w x p n v (congrArg Subtype.val h.symm),
    ContinuousLinearMap.comp_assoc, behind']

lemma plant_exists (x : F₊ s) : ∃ U : J, ∀ (w : ℕ) (f : Entry Y H s j r w) (p : 0 < w),
    f.val=x → ((θ s) w f p).comp ι₀=U := by
  obtain ⟨w,z,k,rfl⟩ := eachField_enters Y H j r s x
  exact ⟨_, fun _ _ p h => nested_width Y H V Q Qc j r C s _ w _ p z k h⟩

def prepare (x : F₊ s) : J := (plant_exists Y H V Q Qc j r C s x).choose
local notation "L₀" s:max => prepare Y H V Q Qc j r C s
lemma acts_from (w : ℕ) (x : Entry Y H s j r w) (p : 0 < w) : (L₀ s) x.val=((θ s) w x p).comp ι₀:=
  ((plant_exists Y H V Q Qc j r C s x.val).choose_spec w x p rfl).symm

lemma prepare_unit : (L₀ s) (unity Y H j 0 r s)=ι₀:= by
  let x := identity Y H s j r 1
  rw [show (unity Y H j 0 r s)=x.val from rfl, acts_from Y H V Q Qc j r C s 1 x one_pos]
  unfold x; rw [ticket_birth]; exact behind' ..
lemma planted (x : F₊ s) : (L₀ s) x Ω = (φ s) x := by
  obtain ⟨w,z,k,rfl⟩ := eachField_enters Y H j r s x
  rw [acts_from Y H V Q Qc j r C s w z k]
  exact lays ..

omit V Q C Qc
abbrev bornTest (x y : F₊ s) : Test := composed r (dual Y H j r (toTest Y H j r s x)) (toTest Y H j r s y)
-- arith for born
lemma born_add (x y z : F₊ s) : bornTest Y H j r s x (y+z) =
    combined r (bornTest Y H j r s x y) (bornTest Y H j r s x z) := Subtype.ext (mul_add _ _ _)
lemma born_scale (x y : F₊ s) (c : ℂ) : bornTest Y H j r s x (c • y) =
    weighted r (bornTest Y H j r s x y) c := Subtype.ext (Algebra.mul_smul_comm ..)

include V Q Qc C
lemma compute (x y : F₊ s) : ((L₀ s) x).adjoint.comp ((L₀ s) y) = (N s) (bornTest Y H j r s x y) := by
  obtain ⟨w,u,x',rfl⟩ := eachField_enters Y H j r s x
  obtain ⟨v,f,y',rfl⟩ := eachField_enters Y H j r s y
  rw [acts_from Y H V Q Qc j r C s w u x',acts_from Y H V Q Qc j r C s v f y',
      ContinuousLinearMap.adjoint_comp,Submodule.adjoint_subtypeL]
  exact (cap_sandwich Y H V Q Qc j r C s w v u f x' y').symm

lemma compute_caps (x : F₊ s) : (N s) (toTest Y H j r s x) = (π₀).comp ((L₀ s) x) := by
  obtain ⟨w,v,p,rfl⟩ := eachField_enters Y H j r s x
  rw [acts_from Y H V Q Qc j r C s w v p, cap_zero_porch Y H V Q Qc j r C s w v p]
-- slit version of inner arithmetic for linearity; use plant contraction later
lemma realize (x y : F₊ s) (p q : (R)) : inner ℂ ((L₀ s) x p) ((L₀ s) y q) =
    inner ℂ p ((N s) (bornTest Y H j r s x y) q) := by
  rw [← compute Y H V Q Qc j r C s,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]

private lemma inner_add_p (x y z : F₊ s) (p q : (R)) : inner ℂ ((L₀ s) x p) ((L₀ s) (y+z) q) =
    inner ℂ ((L₀ s) x p) ((L₀ s) y q) + inner ℂ ((L₀ s) x p) ((L₀ s) z q) := by
  have h : (N s) (bornTest Y H j r s x (y+z)) =
      (N s) (bornTest Y H j r s x y) + (N s) (bornTest Y H j r s x z) := by rw [born_add]; exact congrArg Subtype.val (read_add Y H V Q Qc j r C s _ _)
  rw [realize,realize,realize, h, ContinuousLinearMap.add_apply,inner_add_right]
private lemma inner_scale_p (x y : F₊ s) (z : ℂ) (p q : (R)) : inner ℂ ((L₀ s) x p) ((L₀ s) (z • y) q) =
    inner ℂ ((L₀ s) x p) (z • ((L₀ s) y q)) := by
  have h : (N s) (bornTest Y H j r s x (z • y)) = z • (N s) (bornTest Y H j r s x y) := by
    rw [born_scale]; exact congrArg Subtype.val (read_scale Y H V Q Qc j r C s _ _)
  rw [inner_smul_right,realize,realize,h,ContinuousLinearMap.smul_apply,inner_smul_right]

lemma plant_high (t : ℕ) (p : s ≤ t) (x : F₊ s) : (L₀ t) (Raise Y H Q.circuit j 0 r s t p x) = (L₀ s) x := by
  obtain ⟨w,v,p',rfl⟩ := eachField_enters Y H j r s x
  rw [acts_from Y H V Q Qc j r C s w v p', SlabMark.refined_box Y H V s Q Qc j r C w v p' t p]
  exact acts_from Y H V Q Qc j r C t _ (furnished Y H s Q j r _ v t p) _ -- tune infer

lemma planting_add (x y : F₊ s) : (L₀ s) (x+y)=(L₀ s) x+(L₀ s) y := by
  ext1 v; apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  let f := L₀ s; let t := f (x+y) v - (f x v + f y v)
  have he (p : F₊ s) : inner ℂ (f p v) t = 0 := by unfold t; rw [inner_sub_right, inner_add_right]; exact sub_eq_zero.mpr (inner_add_p ..)
  change inner ℂ t t = 0
  nth_rw 1 [show t = f (x+y) v - (f x v + f y v) from rfl]
  rw [inner_sub_left,inner_add_left,he,he,he]; ring

lemma planting_scale (x : F₊ s) (z : ℂ) : (L₀ s) (z • x)= z • (L₀ s) x := by
  ext1 v; apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  let f := L₀ s; let t := f (z • x) v - z • f x v
  have he (p : F₊ s) : inner ℂ (f p v) t = 0 := by unfold t; rw [inner_sub_right]; exact sub_eq_zero.mpr (inner_scale_p ..)
  change inner ℂ t t = 0; nth_rw 1 [show t = f (z • x) v - z • f x v from rfl]
  rw [inner_sub_left,inner_smul_left,he,he]; ring

def plants : (F₊ s) →ₗ[ℂ] J :=
  { toFun := prepare Y H V Q Qc j r C s, map_add' x y := planting_add Y H V Q Qc j r C s x y,
    map_smul' z x := planting_scale Y H V Q Qc j r C s x z }
lemma prepare_box (w : ℕ) (x : Entry Y H s j r w) (p : 0 < w) (y : F₊ s) :
    (L₀ s) (slabT Y H s j r w x y) = ((θ s) w x p).comp ((L₀ s) y) := by
  obtain ⟨v,f,h,rfl⟩ := eachField_enters Y H j r s y
  let u := edit Y H s j r w v x f
  have ht : slabT Y H s j r w x f.val = u.val := by apply Subtype.ext; rw [slab_eq]; exact (editor ..).symm
  rw [ht,acts_from Y H V Q Qc j r C s (w+v) u (by omega), acts_from Y H V Q Qc j r C s v f h]
  unfold u; rw [← edit_comp Y H V s Q Qc j r C w v x f p h]; rfl
end YM.CF.Buffered.Afterglow.Tower.Selection
