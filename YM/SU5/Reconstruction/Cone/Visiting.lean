import YM.SU5.Reconstruction.Cone.Affords
import YM.SU5.Reconstruction.FirstWindows.Sharp
/-!
# A SHARP, single path assertion for the cone price in the Gross estimate before taking states (all elections)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace LightBudget
set_option quotPrecheck false
open SlabMark MeshClock ConePrice SelectionAnalysis Tapestry.Exhibition Tapestry.Altitude
variable {q : Bool} {U W : Set RSpace}
local notation "V₀" => Domain Y H G false
local notation "D" => Domain Y H G true
local notation "Gt" => timeMesh Λ
variable (j : Axis)
local notation "A₀"=> flank j 0
variable {L : Rack Λ l} {B : Clay Λ l} {T : ℕ → ℕ → Tariff} {t : ℕ → Tariff} (Z : Fashion Y H i k I E L B T t)
local notation "J"=> FiniteGaugeDataPoly K
local notation "θ"=> flipMark j K
local notation "kx"=> shop j K
local notation "ky"=> floor j K
local notation "Ms"=> gram j K
local notation "K₁"=> realize Y H Z.toExhibition
local notation "Mn" n:max=> taking Y H (i (G.rows n)) (k (G.columns n))

-- Actual microscopic-history payment; here 'finite' means SZ geometry and regulators at each (i,k). **Not** finite-dimensional test.
-- `beforeRealized` doesn't presume at any epoch taking at chosen stage, but for authorized costs on all heights and
-- uses CP1 `value_along`. The old grant ContextsFor can be reused: pinhole needed to form density at singular stencil.
include V
lemma beforeRealized (x : FiniteGaugeDataPoly (tent Y H)) (u : realize Y H Z.toExhibition x∈ V₀ univ) :
    Tendsto (fun n=> taking Y H (i (G.rows n)) (k (G.columns n)) x.val ) atTop (𝓝 (courseValue Y H V G ⟨K₁ x,u⟩)) := by
   -- no presentation needed
   have he: courseValue Y H V G ⟨K₁ x,u⟩=vistaTake Y H Z.toExhibition x.val := by
     obtain ⟨s,t⟩:= curve.mp x.property
     have h : (⟨realize Y H Z.toExhibition x,u⟩ : V₀ univ)=⟨ticket Y H G s ((vistaFinish Y H s Z.toExhibition) x.val), ticket_loose ..⟩ := Subtype.ext (realize_ticket Y H V G Z.toExhibition s x t)
     rw [h,course_ticket_val]; exact (Exhibition.vistaCall Y H s _ Z.toExhibition t).symm
   rw [he]; exact value_along Y H G Z x
omit V
attribute [local instance] opCStarAlgebra

-- One prescription is to ask this estimate for actual gauges along the SHARP career.
-- All operators bought on the same career, we know support inclusion of their
-- breathing versions at all resolutions. No need the estimate UNIFORM as x,y
-- range over tests; called after fixing them, even slack δ→0 after n→∞.
-- And we can test *ONLY* upon disjoint support products of singlet polynomials (Wide).
structure BoughtAt (r : ℝ) (f : Sky (tent Y H)) (u : FiniteGaugeDataPoly (tent Y H)) : Prop where
  paid : ∃ U W : Set RSpace, U⊆mirrorE j 0 '' flank j r ∧ W ⊆ flank j r ∧
    IsCompact U ∧ IsCompact W ∧ (∀ x∈U,∀ y∈W, x j+2*r ≤ y j) ∧ Disjoint U W ∧ ∃ x y : FiniteGaugeDataPoly (tent Y H),
      x.val∈questions Λ l K true U ∧ y.val∈ questions Λ l K true W ∧
      realize Y H Z.toExhibition x=flipMark j K f ∧ realize Y H Z.toExhibition y=f ∧ x*y=u
include V
lemma buys_pose {r : ℝ} (f : Sky (tent Y H)) (p : 0<r) (v : f∈ D (flank j r)) : ∃ u : FiniteGaugeDataPoly (tent Y H), BoughtAt Y H j Z r f u := by
  obtain ⟨U,W,h₁,h₂,hA,hB,hC,c,d,s,g⟩:= processed Y H G j r f v p
  obtain ⟨x,hx,e⟩:= show (θ f) ∈ K₁ '' {x| x.val ∈ questions Λ l (tent Y H) true U} from by rw [realize_covers Y H V G]; exact hA
  obtain ⟨y,hy,b⟩:= show f ∈ K₁ '' {x| x.val ∈ questions Λ l (tent Y H) true W} from by rw [realize_covers Y H V G]; exact hB
  exact ⟨x*y,⟨U,W,h₁,h₂,c,d,g,s,x,y,hx,hy,e,b,rfl⟩⟩ -- structure extra
include G
lemma pose_calibrated {r : ℝ} {f : Sky (tent Y H)} (u : FiniteGaugeDataPoly (tent Y H)) (h : BoughtAt Y H j Z r f u) :
    K₁ u= Ms f ∧ ∃ U, IsCompact U ∧ u.val ∈ questions Λ l K true U := by
  obtain ⟨U,W,h₁,h₂,a,b,c,d,x,y,hx,hy,e,v,rfl⟩:= h.paid
  refine ⟨by rw [realize_separated Y H V G Z.toExhibition hx hy d,e,v], U∪W,a.union b, Subalgebra.mul_mem _ ?_ ?_⟩
  · exact questions_mono subset_union_left hx
  exact questions_mono subset_union_right hy

-- any rendering works with slack. This check is sufficient *and* necessary for FirstShot on the actual E.
omit V G
-- G unused here

private lemma asymp_order {u v : ℕ→ℝ} {a b : ℝ} (p : Tendsto u atTop (𝓝 a)) (q : Tendsto v atTop (𝓝 b)) :
    (a≤ b) ↔ ∀ δ:ℝ, 0<δ→ ∀ᶠ i in atTop,u i≤ v i+δ:= by
  constructor
  · intro h δ c; exact Filter.Eventually.mono (Filter.Tendsto.eventually_lt p (q.add (tendsto_const_nhds (x:=δ))) (h.trans_lt (lt_add_of_pos_right _ c))) (fun _ d=> d.le) -- tune
  intro h; apply le_of_forall_pos_le_add; intro ε he; exact le_of_tendsto_of_tendsto p (q.add tendsto_const_nhds) (h ε he)

include G
structure VisitPrice (r e : ℝ) : Prop where
  pressure : ∀ (z : placement Λ), coordinates Λ z∈ ConePrice.CostDomain j e →
    ∀ f : Sky (tent Y H), f∈ D (flank j r) → ∀ x y : FiniteGaugeDataPoly (tent Y H), BoughtAt Y H j Z r (kx z f) x → BoughtAt Y H j Z r (ky z f) y→
      ∀ δ:ℝ,0<δ → ∀ᶠ n in atTop, ( (Mn n) x.val ).re ≤ ( (Mn n) y.val ).re+δ
include V
lemma pressure_roots {r e : ℝ} (h : 0<r) : FirstShot Y H V G j r e ↔ VisitPrice Y H G j Z r e := by
  let a_t (y:Sky K) (hy : y∈ V₀ univ) := (courseValue Y H V G ⟨y,hy⟩).re; let b_t (x:J) (n : ℕ) := ((Mn n) x.val).re
  have hZ (f : Sky K) (y : FiniteGaugeDataPoly K) (h : BoughtAt Y H j Z r f y) (v : Ms f ∈ V₀ univ) : Tendsto (b_t y) atTop (𝓝 (a_t (Ms f) v)) := by
    obtain ⟨c,_⟩:= pose_calibrated Y H V G j Z y h
    let u:= beforeRealized Y H V G Z y (c.symm ▸ v)
    have hm (p:K₁ y∈ V₀ univ): (⟨Ms f,v⟩ : V₀ univ)=⟨K₁ y,p⟩:=Subtype.ext c.symm
    unfold a_t; rw [hm (c.symm ▸ v)]; exact Complex.continuous_re.continuousAt.tendsto.comp u
  constructor
  · intro p; refine ⟨fun z b f hx x y h₁ h₂=>?_⟩
    obtain ⟨k₁,k₂⟩:= pressure_coverage Y H V G j z f hx h.le b; let k₁:= domain_loose Y H G _ k₁; let k₂:= domain_loose Y H G _ k₂
    exact (asymp_order (hZ _ x h₁ k₁) (hZ _ y h₂ k₂)).1 (p z b f hx k₁ k₂)
  intro p z b f hx k₁ k₂; obtain ⟨hP,hS⟩ := budget_legs Y H V G j r f z hx b.1.le
  obtain ⟨x,h₁⟩:= buys_pose Y H V G j Z (kx z f) h hP; obtain ⟨y,h₂⟩:= buys_pose Y H V G j Z (ky z f) h hS
  exact (asymp_order (hZ _ x h₁ k₁) (hZ _ y h₂ k₂)).2 (p.pressure z b f hx x y h₁ h₂)
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
