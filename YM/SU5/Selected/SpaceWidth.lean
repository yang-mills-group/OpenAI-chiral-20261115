import YM.SU5.Selected.PlantLeft
/-! # Spatial shifts, all half-steps fix the ground

Use phase_iso for equality of ground operators after any mesh shift, not just second step of
Fock parity. Gives also `prepare` spatial equivariance. Not claiming CONTINUITY in physical
Euclidean coordinates of the space moves; these results are on marks. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 180000
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

local notation "℘" => Heat.gaugeShift Λ.block
local notation "b₀" => ruler Λ.block
local notation "τ" s:max => tick Y H s j 0 r
local notation "E₊" s:max w:max => Entry Y H s j r w
local notation "ψ" s:max w:max => slabT Y H s j r w
local notation "L₀" s:max => prepare Y H V Q Qc j r C s
local notation "θ" s:max => boxOp Y H V s Q Qc j r C
local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "ι₀" => (R).subtypeL
variable (s : ℕ) (v : Axis) (p : v ≠ j) (x : ℤ)
local notation "N₀" s:max => sailV Y H V s Q.circuit j 0 r v p C
local notation "Z₀" s:max => sail Y H s j 0 r v p

include V Q C p
lemma sail_unit (h : (A)) : (N₀ s) (-x) ((N₀ s) x h) = h := by
  rw [←ContinuousLinearMap.comp_apply,sailV_sum,neg_add_cancel, sailV_source]; rfl
lemma sail_size (h : (A)) : ‖(N₀ s) x h‖=‖h‖ := by
  have he (k : ℤ) (h : (A)) : ‖(N₀ s) k h‖ ≤ ‖h‖ := (((N₀ s) k).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (sailV_small ..))
  refine le_antisymm (he x h) ?_
  have ht := he (-x) ((N₀ s) x h); rwa [sail_unit Y H V Q] at ht
lemma sail_meter (w : (A)) (h : (A)) : inner ℂ ((N₀ s) x w) ((N₀ s) x h)=inner ℂ w h :=
  (LinearMap.norm_map_iff_inner_map_map ((N₀ s) x)).mp (sail_size Y H V Q j r C s v p x) w h
include Qc
lemma sail_ground (h : (R)) : (N₀ s) x h.val = h.val := by
  apply all_voices Y H Q.circuit j 0 r C; intro t y
  let i := max t s; let ht : t ≤ i := le_max_left ..; let hs : s ≤ i := le_max_right ..
  let f := Raise Y H Q.circuit j 0 r t i ht y
  let g := (Z₀ i) (smill Λ s i (-x)) f
  rw [←join_actor Y H V Q.circuit j 0 r C t i ht]
  change inner ℂ ((φ i) f) _=inner ℂ ((φ i) f) _
  rw [←sail_meter Y H V Q j r C s v p (-x) _ ((N₀ s) x h.val), sail_unit Y H V Q j r C s v p,
      sailV_at Y H V s Q.circuit j 0 r v p C (-x) i hs f]
  change inner ℂ ((φ i) g) h.val = _
  rw [←projection_to Y H V Q j r C _ h,←projection_to Y H V Q j r C _ h,←cap_prepares Y H V Q Qc,←cap_prepares Y H V Q Qc]
  have he : liftCap Y H V Q Qc j r C i (toTest Y H j r i g) = liftCap Y H V Q Qc j r C i (toTest Y H j r i f) := by
    have he : toTest Y H j r i g=stepTest Y H v r (smill Λ s i (-x)) (toTest Y H j r i f):=Subtype.ext rfl
    rw [he]; exact stationarity Y H V Q Qc j r C i _ _ v
  rw [show (N i) (toTest Y H j r i g)=(N i) (toTest Y H j r i f) from congrArg Subtype.val he]

omit V Q Qc C

def blown (w : ℕ) (f : E₊ s w) : E₊ s w := by
  refine ⟨(Z₀ s) x f.val,?_⟩
  obtain ⟨S,t,h⟩ := f.property
  exact ⟨address v (℘ x) S,flow_port K v _ t,fun i u => by
    obtain ⟨v0,h0,rfl⟩ := mem_image.mp u; rw [moves, if_neg p.symm]; exact h _ h0⟩

private lemma around (w : ℕ) (f g : E₊ s w) (h : g.val=(Z₀ s) x f.val) (y : F₊ s) :
    (Z₀ s) x ((ψ s w) f y) = (ψ s w) g ((Z₀ s) x y) := by
  apply Subtype.ext
  change chime K v (℘ x) (f.val.val* ((τ s) (2*w) y).val)=g.val.val * ((τ s) (2*w) ((Z₀ s) x y)).val
  rw [h,chime_product,← crossover]
  rfl
include V Q Qc C
lemma sail_width (w : ℕ) (f : E₊ s w) (h : 0 < w) :
    ((N₀ s) x).comp ((θ s) w f h) = ((θ s) w (blown Y H j r s v p x w f) h).comp ((N₀ s) x) := by
  apply test_high Y H V s Q j r C; intro i t y; let z := blown Y H j r s v p x w f
  change (N₀ s) x ((θ s) w f h ((φ i) y))=(θ s) w z h ((N₀ s) x ((φ i) y))
  rw [snatch Y H V s Q Qc j r C _ f _ t, sailV_at Y H V s Q.circuit j 0 r v p C x i t,
    sailV_at Y H V s Q.circuit j 0 r v p C x i t,snatch Y H V s Q Qc j r C w z h t]
  exact congrArg (φ i) (around Y H j r i v p _ _ _ _ (sail_up Y H V s Q.circuit j 0 r v p i t f.val x).symm _)
lemma from_space_μ (y : F₊ s) : ((N₀ s) x).comp ((L₀ s) y)=(L₀ s) ((Z₀ s) x y) := by
  obtain ⟨w,f,h,rfl⟩ := eachField_enters Y H j r s y
  let z := blown Y H j r s v p x w f
  rw [acts_from Y H V Q Qc j r C s w f h,←ContinuousLinearMap.comp_assoc,
    sail_width Y H V Q Qc j r C s v p x w f h, ContinuousLinearMap.comp_assoc,
    show (Z₀ s) x f.val = z.val from rfl, acts_from Y H V Q Qc j r C s w z h,
    show ((N₀ s) x).comp (ι₀) = ι₀ from ContinuousLinearMap.ext (sail_ground Y H V Q Qc j r C s v p x)]
end YM.CF.Buffered.Afterglow.Tower.Selection
