import YM.SU5.Selected.PlantLeft
/-! # All time-shifts on the preparation operator out of the ground

Double-step n means integer width n on SlabMark, in gauge-site physical units dx=16B.
Use odd step n = displacement 8B n. Hence pack two half paddings of this amount: one shift
before the slab and one after. First on the raw lattice F₊ at one level. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 200000
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
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "L₀" s:max => prepare Y H V Q Qc j r C s
local notation "ε₀" => advance Y H V Q.circuit j 0 r C
local notation "θ" s:max => boxOp Y H V s Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "ι₀" => (R).subtypeL
variable (s t : ℕ)

lemma odd_between (S : Finset Cover) {w : ℕ} (h : Between K j 0 (b₀ * w) S) :
    Between K j 0 (b₀ * ((w+t:ℕ):ℤ)) (address j (℘ (t:ℤ)) S) := by
  intro x hx; obtain ⟨u,hv,rfl⟩ := mem_image.mp hx; rw [moves,if_pos rfl]
  have ha : 0 ≤ ℘ (t:ℤ) := by unfold gaugeShift; positivity
  have hb : b₀ * ((w+t:ℕ):ℤ) = b₀*w+4* ℘ (t:ℤ) := by unfold ruler gaugeShift; push_cast; ring
  rw [hb]
  have u' := h u hv; constructor <;> omega

def midTime (w : ℕ) (x : E₊ s w) : E₊ s (w+t) := by
  refine ⟨(τ s) t x.val,?_⟩
  obtain ⟨S,v,e⟩ := x.property
  exact ⟨address j (℘ (t:ℤ)) S,flow_port K j _ v, odd_between Y H j t _ e⟩

private lemma time_join {u v : ℕ} (x : E₊ s v) (z : E₊ s u)
    (p : v+t=u) (q : z.val=(τ s) t x.val) (f : F₊ s) :
    (τ s) t ((ψ s v) x ((τ s) t f)) = (ψ s u) z f := by
  subst u; apply Subtype.ext
  let T (v : F₊ s) := v.val
  have he (k : ℕ) (f : F₊ s) : ((τ s) k f).val=chime K j (℘ (k:ℤ)) f.val := rfl
  have hs (w : ℕ) (x : E₊ s w) (y : F₊ s) : ((ψ s w) x y).val=x.val.val*((τ s) (2*w) y).val:=rfl
  rw [hs, he, hs, chime_product,← he t, ← he t, ← q, tick_tock,tick_tock] -- `he` order first?
  rw [show t+2*v+t=2*(v+t) from by omega]

include V Q Qc C
lemma time_widths (w : ℕ) (x : E₊ s w) (p : 0 < w) :
    ((ρ s) t).comp (((θ s) w x p).comp ((ρ s) t)) =
      (θ s) (w+t) (midTime Y H j r s t w x) (by omega) := by
  let z := midTime Y H j r s t w x
  apply test_high Y H V s Q j r C -- `test_high` using any later
  intro i h f; simp only [ContinuousLinearMap.comp_apply]
  rw [limited_time Y H V s Q.circuit j 0 r C t h f,
    snatch Y H V s Q Qc j r C w x p h, limited_time Y H V s Q.circuit j 0 r C t h,
    snatch Y H V s Q Qc j r C (w+t) (midTime Y H j r s t w x) (by omega) h]
  apply congrArg (φ i); let u := amount Λ s i t
  refine time_join Y H j r i u _ _ (by unfold u amount; rw [mul_add]) ?_ _
  exact (tick_up Y H V s Q.circuit j 0 r i h x.val t).symm

lemma from_time_μ (x : F₊ s) : ((ρ s) t).comp ((L₀ s) x)=(L₀ s) ((τ s) t x) := by
  obtain ⟨w,u,v,rfl⟩ := eachField_enters Y H j r s x
  let z := midTime Y H j r s t w u
  rw [acts_from Y H V Q Qc j r C s w u v, show (τ s) t u.val = z.val from rfl,
    acts_from Y H V Q Qc j r C s (w+t) z (by omega), ←time_widths Y H V Q Qc j r C s t w u v]
  rw [at_every Y H V Q,ContinuousLinearMap.comp_assoc,ContinuousLinearMap.comp_assoc,behind']
end YM.CF.Buffered.Afterglow.Tower.Selection
