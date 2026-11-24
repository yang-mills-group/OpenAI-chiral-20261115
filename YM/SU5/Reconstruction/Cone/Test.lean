import YM.SU5.Reconstruction.FirstWindows.MovingKets
import YM.SU5.Reconstruction.Cone.AxisCheck
/-!
# Price estimate on the actual Euclidean singlet probes (selected). No continuity
or Lorentz hypotheses. Aimed to consume explicitly pinned real-world estimates or
isolate the missing analytic gap, not redescribe it in terms of Lorentzian conditions.

Reduce cone-continuity and spectrum for the whole indoor to real EU understanding
of two singlet observations, purchasable at any phase level. In 8-grid units, not
asserting necessity of continuity for projects choosing a smaller OS domain instead.
Preserves calibration and the precise chiral tests from CP1 incl residents via `ContextFor`. -/
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
open SlabMark MeshClock ConePrice SelectionAnalysis
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G true
local notation "Gt" => timeMesh Λ
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0

def onlyTime (j : Axis) (z : placement Λ) : placement Λ := Function.update 0 j (z j)
@[simp] theorem quadrant (z : placement Λ) : (onlyTime j z j) = z j := by simp [onlyTime]
@[simp] theorem plaza (z : placement Λ) : atEstate Y H V G.history G.clipped j false C χ (onlyTime j z) =
    (L).E (coordinates Λ z j).toNNReal := by
  unfold atEstate; rw [quadrant, show (fun i:Trans j=> onlyTime j z i.val)=0 from funext (fun i:Trans j=> by unfold onlyTime; rw [Function.update_of_ne i.property]; rfl), Germ.Alliance.raw_zero]; rfl

abbrev shop (j : Axis) (J : Calibration) (z : placement Λ) (w : Sky J) : Sky J :=
   move J z w - move J (onlyTime j z) w
abbrev floor (j : Axis) (J : Calibration) (z : placement Λ) (w : Sky J) : Sky J :=
   w - move J (onlyTime j z) w
abbrev gram (j : Axis) (J : Calibration) (x : Sky J) := flipMark j J x*x
local notation "θ" => flipMark j K
local notation "kx" => shop j K
local notation "ky" => floor j K
local notation "Ms" => gram j K
section sale
variable (r : ℝ)
variable (f : Sky (tent Y H))
variable (z : placement Λ) (v : 0≤ coordinates Λ z j)
include V
lemma budget_base (b : f∈ D (flank j r)) (u : 0≤ coordinates Λ z j) : move K z f∈ D (flank j r) :=
    domain_mono Y H G (even_flank j z (by apply le_add_of_nonneg_right u)) (moving Y H V G z f b)
lemma budget_legs (b : f∈ D (flank j r)) (u : 0≤ coordinates Λ z j) : shop j K z f ∈ D (flank j r) ∧ floor j K z f∈ D (flank j r) := by
  have hv:= budget_base Y H V G j r f (onlyTime j z) b (by simp; exact u); exact ⟨(D _).sub_mem (budget_base Y H V G j r f z b u) hv,(D _).sub_mem b hv⟩
omit V
lemma processed (b : f∈ D (flank j r)) (h : 0<r) :
    ∃ U W : Set RSpace, U ⊆ mirrorE j 0 '' flank j r ∧ W ⊆ flank j r ∧
      θ f ∈ D U ∧ f∈D W ∧ Ms f∈D (U∪W) ∧ IsCompact U ∧ IsCompact W ∧
      Disjoint U W ∧ ∀ x∈U,∀ y∈ W,x j+2*r ≤ y j := by
  obtain ⟨U,c,d,e⟩ := (compact_domain Y H G).1 b; obtain ⟨W,c',d',e'⟩ := (compact_domain Y H G).1 (mirror_support Y H G j f b)
  have hl : ∀ x∈W,∀ y∈U, x j+2*r≤y j := by
    intro x hx y hy; obtain ⟨z,hz,rfl⟩:= d' hx; unfold mirrorE; rw [if_pos rfl]; linarith [show r ≤ _ from (show r≤ z j from hz), show r ≤ y j from d hy]
  have hv : Disjoint W U := Set.disjoint_left.mpr fun x p => fun u => by linarith [hl x p x u]
  exact ⟨W,U,d',d,e',e,domain_mult Y H G e' e hv,c',c,hv,hl⟩

lemma gram_covered (b : f∈ D A₀) : gram j K f∈Domain Y H G false univ :=
  domain_loose Y H G _ (paired_forever Y H G j _ _ b b)
include V
lemma gram_pays (b : f∈ D A₀) (h : gram j K f∈Domain Y H G false univ) :
    (F ⟨gram j K f,h⟩).re = ‖physicalKet Y H V G j C χ ⟨f,b⟩‖^2 := by
  let x:= (⟨f,domain_loose Y H G A₀ b⟩ : Domain Y H G false A₀)
  change Complex.re _ = ‖OSvector Y H V G j C χ x‖^2
  have hv : OSvector Y H V G j C χ x=physicalKet Y H V G j C χ ⟨f,b⟩:=rfl
  rw [show F ⟨gram j K f,h⟩ = inner ℂ (OSvector Y H V G j C χ x) (OSvector Y H V G j C χ x) from (registered_pair Y H V G j C χ x x).symm]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
lemma pressure_test (v : 0≤ coordinates Λ z j) (b : f∈ D A₀)
    (k₁ : Ms (kx z f)∈ Domain Y H G false univ) (k₂ : Ms (ky z f)∈ Domain Y H G false univ) :
    (F ⟨Ms (kx z f),k₁⟩).re ≤ (F ⟨Ms (ky z f),k₂⟩).re ↔
      let t := (coordinates Λ z j).toNNReal
      let x := physicalKet Y H V G j C χ ⟨f,b⟩
      ‖(L).E t (transverse_play (Ω₀) z x)-(L).E t x‖ ≤ ‖x-(L).E t x‖ := by
  let t := (coordinates Λ z j).toNNReal
  let h:= budget_legs Y H V G j 0 f z b v
  rw [gram_pays Y H V G j C χ _ h.1, gram_pays Y H V G j C χ _ h.2, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  let u : 0≤ coordinates Λ (onlyTime j z) j:= by simp; exact v
  let f' := move K (onlyTime j z) f; let b₀:= budget_base Y H V G j 0 f (onlyTime j z) b u
  let p := (⟨move K z f,budget_base Y H V G j 0 f z b v⟩: D (flank j 0)); let w :=(⟨f',b₀⟩: D (flank j 0)); let y := (⟨f,b⟩: D (flank j 0))
  have hu : Π p=(L).E t (transverse_play (Ω₀) z (Π y)):= physical_move Y H V G j C χ f b z v p.property
  have hp : Π w=(L).E t (Π y) := by dsimp only [t]; rw [← plaza]; exact physical_move Y H V G j C χ f b _ u w.property -- defeq?
  change ‖physicalKet Y H V G j C χ (p-w)‖ ≤ ‖physicalKet Y H V G j C χ (y-w)‖ ↔ _
  rw [map_sub,map_sub,hu,hp]
end sale
/-- Selected Euclidean check telling whether translations occupy the whole physical cone by the calibrated price.
No Minkowski objects involved in the check. -/
def TwoShot (r e : ℝ) : Prop :=
  ∀ z : placement Λ, coordinates Λ z ∈ ConePrice.CostDomain j e → ∀ f : Sky (tent Y H), f∈ D (flank j r) →
  ∀ (k₁ : gram j K (shop j K z f)∈ Domain Y H G false univ) (k₂ : gram j K (floor j K z f)∈ Domain Y H G false univ),
    (osValue Y H V G j C χ ⟨gram j K (shop j K z f),k₁⟩).re ≤ (osValue Y H V G j C χ ⟨gram j K (floor j K z f),k₂⟩).re

-- these readings *can* be purchased. even budgeted at arbitrary strictly positive r
-- in sense of prepared product polar legs at any refinement; separate supports (processed).
include V in
lemma pressure_coverage {r e : ℝ} (z : placement Λ) (f : Sky (tent Y H)) (b : f∈ D (flank j r)) (p : 0≤r) (h : coordinates Λ z∈ ConePrice.CostDomain j e) :
    Ms (kx z f)∈ Domain Y H G true univ ∧ Ms (ky z f)∈ Domain Y H G true univ := by
  obtain ⟨a,c⟩ := budget_legs Y H V G j 0 f z (domain_mono Y H G (TimeMesh.flank_mono j p) b) h.1.le
  exact ⟨paired_forever Y H G j _ _ a a,paired_forever Y H G j _ _ c c⟩

lemma price_at_χ {r : ℝ} (p : 0≤r) (e : ℝ) : ConePrice.GridHeat (L) (Ω₀) e ↔ TwoShot Y H V G j C χ r e := by
  constructor
  · intro H₀ z v f b g h; exact (pressure_test Y H V G j C χ f z v.1.le (domain_mono Y H G (TimeMesh.flank_mono j p) b) g h).2 (H₀ z v _)
  intro q z w x; let t:= (coordinates Λ z j).toNNReal
  let E₀(u : J₀):= (L).E t u; let S₀:= transverse_play (Ω₀) z
  let T:={x : J₀ | ‖E₀ (S₀ x)-E₀ x‖≤‖x-E₀ x‖}
  have hE : Continuous E₀:= ((L).E _).continuous; have hT : IsClosed T := isClosed_le (((hE.comp S₀.continuous).sub hE).norm) ((continuous_id.sub hE).norm)
  refine closure_minimal ?_ hT (TimeMesh.dense_flanks Y H V G j C χ r x)
  rintro y ⟨f,h,v,rfl⟩; obtain ⟨g,g'⟩:= pressure_coverage Y H V G j z f h p (show coordinates Λ z∈ ConePrice.CostDomain j e from w)
  let h1 := domain_loose Y H G _ g; let h2:= domain_loose Y H G _ g'
  exact (pressure_test Y H V G j C χ f z w.1.le v h1 h2).1 (q z w f h h1 h2)

/-- Unconditional equivalence. Can read contrapositively too: obstruction anywhere in the
 physical cone of joint momentum or indoor spatial continuity at this grid means failure
 at real physically separated positive times and at as small stamps as one likes. -/
theorem true_spectrum {b e : ℝ} (p : 0≤ b) (v : 0<e) :
    TwoShot Y H V G j C χ b e ↔
      saunters Y H V G.history G.clipped j false C χ=⊤ ∧ ConePrice.Forward (peninsula Y H V G.history G.clipped j false C χ) :=
  (price_at_χ Y H V G j C χ p e).symm.trans <| ConePrice.operator_pressure (L) (daylight (timeMesh Λ)) (Ω₀) (follows_road Y H V G.history G.clipped j false C χ) v
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
