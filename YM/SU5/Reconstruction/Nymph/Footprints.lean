import YM.SU5.Reconstruction.Nymph.Lanes
import YM.SU5.Reconstruction.Nymph.Binding
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
namespace Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false
open SelectionAnalysis OS.Semigroup
variable (iA:Axis) (R : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped iA false (R iA) →⋆ₐ[ℂ] ℂ)
local notation "P" => D false Set.univ
local notation "ν" => marks (dainty Λ)
local notation "c" j:max => displacement Y H V G.history G.clipped iA false (R iA) χ j (R j)
variable (j:Axis)
local notation "A" => indoor Y H V G.history G.clipped j false (R j) (c j)
local notation "Q" => ride Y H V G.history G.clipped j false (R j) (c j)
local notation "Ξ" => atEstate Y H V G.history G.clipped j false (R j) (c j)
local notation "X" => OSvector Y H V G j (R j) (c j)
local notation "T" => flank j 0
local notation "N" => Domain Y H G false (flank j 0)
local notation "V₀" => turnstile Y H V G.history G.clipped j false (R j) (c j)
local notation "B" i:max p:max => stride (tent Y H) i p
local notation "μ" j1:max => osValue Y H V G j1 (R j1) (c j1)
set_option quotPrecheck false
open Submodule InnerProductSpace LightBudget
variable (s: Trans j)
local notation "U" s:max=> (outfit Y H V G iA R χ j).crew s
local notation "L'" s:max=> (U s).lives (indoor Y H V G.history G.clipped j false (R j) (c j))
local notation "Z" s:max=> (L' s)ᗮ
local notation "Π₀" => (saunters Y H V G.history G.clipped j false (R j) (c j)).starProjection
local notation "D₁" s:max=> (eclipse Y H V G iA R χ j s)
local notation "λ₀" s:max=> (fourth Y H V G iA R χ j s)
set_option quotPrecheck false
-- stability of strict lanes under old projectors.
variable (b:ℝ)(x:Bool)
local notation "W" d:max x:max=> (marksLane Y H V G iA R χ j s d x)
local notation "F" d:max x:max=> traceLane Y H V G iA R χ j s d x
lemma priced_shadow : (F b x) ≤ Z s:= by
  apply topologicalClosure_minimal _ _ (isClosed_orthogonal _)
  rw [span_le]; rintro i ⟨d,p,z,t,rfl⟩; rw [shadow]; exact starProjection_apply_mem ..

lemma local_ticket_always (w:Trans j) {z:A} (h:z∈ W b x) : ∀ᶠ i in 𝓝 (0:ν),
    (U w).play i z ∈ W b x := by
  obtain ⟨d,h,f,k,rfl⟩:= h
  have appetite(i:ν)(p:room (d+eject w.val (i:ℝ) s.val) b x) : (U w).play i ((D₁ s) (X f)) ∈ W b x:=by
    -- no shrink representation requirement. shift budget d itself, still certified ticket
    rw [through Y H V G iA R χ j s (shadow_turn Y H V G iA R χ j s w i),owns_play]
    let g:= glimpse Y H G j w i f; let a:= eject w.val (i:ℝ) s.val
    have ht : g.val∈ D false (sideLand s.val (d+a) x) := by
      apply domain_mono Y H G _ (stride_region Y H G w.val i f.val k)
      rintro _ ⟨v,y,rfl⟩; cases x
      · exact add_le_add_left (show v s.val ≤ d from y) _
      exact add_le_add_left (show d ≤ v s.val from y) _
    exact ⟨d+a,p,g,ht,rfl⟩
  by_cases q:s.val=w.val
  · cases x
    · have he:d<b:= h
      filter_upwards [((continuous_const (y:=d)).add continuous_subtype_val |>.tendsto (0:ν) |>.eventually (gt_mem_nhds (show d+(0:ν).val < b by change d+(0:ℝ)<b; simpa using he)))] with i hi; apply appetite; rw [q,eject_at]; exact hi
    have he:b<d:= h
    filter_upwards [((continuous_const (y:=d)).add continuous_subtype_val |>.tendsto (0:ν) |>.eventually (lt_mem_nhds (show b<d+(0:ν).val by change b < d+(0:ℝ); simpa using he)))] with i hi; apply appetite; rw [q,eject_at]; exact hi
  exact Eventually.of_forall fun i=> appetite i (by rw [eject_away w.val _ _ q,add_zero]; exact h)
-- lanes not visible outside. older orbit inside tiny motion.
lemma older_local (w:Trans j) {z:A} (h:z∈ W b x) : ∀ᶠ i in 𝓝 (0:marks (timeMesh Λ)), ((V₀).crew w).play i z∈ W b x:=by
  have he: Continuous (finerNow Λ):=by apply Continuous.subtype_mk (f:=fun z:marks (timeMesh Λ)=>(z:ℝ)) continuous_subtype_val
  have hx:Tendsto (finerNow Λ) (𝓝 0) (𝓝 0):=by simpa using he.tendsto 0
  filter_upwards [hx.eventually (local_ticket_always Y H V G iA R χ j s b x w h)] with i hi
  exact older_stride Y H V G iA R χ j w i ▸ hi
lemma older_rep (w:Trans j) : MapsTo ((V₀).crew w).pi_c (F b x) (F b x):=by
  apply SkyFold.from_spans _ _ (closed_lane ..); intro v h
  exact SkyFold.sector_under_focus (closed_lane ..) _ (here Y H V G iA R χ j s b x h) ((older_local Y H V G iA R χ j s b x w h).mono fun i hv=> here Y H V G iA R χ j s b x hv)
lemma older_lives_on_lane : MapsTo Π₀ (F b x) (F b x) := by
  rw [← stack_projection]; suffices h:∀ v:List (Trans j),MapsTo ((V₀).stackS v) (F b x) (F b x) by apply h
  intro v; induction v with
  | nil=>exact fun v h=>h
  | cons i v ih=> exact fun v h=> older_rep Y H V G iA R χ j s b x i (ih h)

end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
