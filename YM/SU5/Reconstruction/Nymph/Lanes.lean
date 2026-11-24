import YM.SU5.Reconstruction.Nymph.SpaceCost
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
lemma shadow : (D₁ s) = (Z s).starProjection := by
  rw [eclipse, show (1:(A).Op)=(L' s).starProjection+(Z s).starProjection from (id_eq_sum_starProjection_self_orthogonalComplement ..)]
  change _+_ - (L' s).starProjection = _; abel
lemma shadow_heat (t:ℝ≥0) : Commute (D₁ s) ((Q).E t) := by
  unfold eclipse; apply (Commute.one_left _).sub_left
  exact ((U s).commutes_c ((Q).E t) (fun x=> comm_heat Y H V G iA R χ j s x t)).symm
lemma shadow_turn (t: Trans j)(x:ν) : Commute (D₁ s) ((U t).play x) := by
  unfold eclipse; apply (Commute.one_left _).sub_left
  exact ((outfit Y H V G iA R χ j).floatZ t s x 0).symm
lemma shadow_kept : Commute (D₁ s) Π₀ := by
  unfold eclipse; apply (Commute.one_left _).sub_left
  exact ((U s).commutes_c Π₀ (fun i=> (even_preserves Y H V G iA R χ j s i).symm.eq)).symm
lemma through (s:Trans j) {A' : (A).Op}(h : Commute (D₁ s) A') (v : indoor Y H V G.history G.clipped j false (R j) (c j)) : A' ((D₁ s) v) = (D₁ s) (A' v) := congrArg (fun W:(A).Op=> W v) h.symm.eq

-- localization lanes, maybe 0 projection entire; unital not asserted. state spaces.
-- no same-budget promise needed for k and j at once, use separately.
def room (d b:ℝ) (x:Bool) := if x then b < d else d < b
local notation "U'" b:max x:max=> sideLand s.val b x
variable (b:ℝ) (x : Bool)
def marksLane : Set (indoor Y H V G.history G.clipped j false (R j) (c j)):= {i | ∃ (d : ℝ), room d b x ∧∃ f: Domain Y H G false (flank j 0), f.val∈ D false (sideLand s.val d x) ∧ i=(D₁ s) (X f)}
local notation "W" d:max x:max=> (marksLane Y H V G iA R χ j s d x)
noncomputable def traceLane : Submodule ℂ (A) := (span ℂ (W b x)).topologicalClosure
local notation "F" d:max x:max=> traceLane Y H V G iA R χ j s d x
instance livesLane : CompleteSpace (F b x) := isClosed_closure.completeSpace_coe -- tune
@[simp] lemma closed_lane : IsClosed ((F b x) : Set (A)):=isClosed_closure
lemma as_far {d:ℝ}(p:room d b x)(f:N) (h:f.val∈ D false (U' d x)) : (D₁ s) (X f) ∈ W b x:=⟨d,p,f,h,rfl⟩
lemma here : W b x ⊆ (F b x : Set (A)):= fun x p=> le_topologicalClosure _ (subset_span p)
lemma pitch_in_lane {t: Trans j}(v:ν) : MapsTo ((U t).play v) (W b x) (W (b+eject t.val (v:ℝ) s.val) x):=by
  rintro z ⟨d,p,f,h,rfl⟩
  let y:=eject t.val (v:ℝ) s.val
  let g:=glimpse Y H G j t v f
  have hp : room (d+y) (b+y) x := by cases x <;> unfold room at * <;> split_ifs at * <;> linarith -- cost
  have h': g.val∈ D false (sideLand s.val (d+y) x) := by
    apply domain_mono Y H G _ (stride_region Y H G t.val v f.val h)
    rintro _ ⟨w,p,rfl⟩; cases x
    · exact add_le_add_left (show w s.val ≤ d from p) y
    exact add_le_add_left (show d ≤ w s.val from p) y
  refine ⟨d+y,hp,g,h',?_⟩
  change (U t).play v ((D₁ s) _) = _; rw [through Y H V G iA R χ j s (shadow_turn Y H V G iA R χ j s t v),owns_play]
lemma lane_moves {t:Trans j}(v:ν) : MapsTo ((U t).play v) (F b x) (F (b+eject t.val (v:ℝ) s.val) x):=
  SkyFold.from_spans _ _ (closed_lane ..) (fun y h=> here Y H V G iA R χ j s _ x (pitch_in_lane Y H V G iA R χ j s b x v h))
lemma lane_early (p:ν)(v:0 ≤ (p:ℝ)): MapsTo ((Q).E (Real.toNNReal (p:ℝ))) (W b x) (W b x) := by
  rintro y ⟨d,h,f,t,rfl⟩; let u := (Real.toNNReal (p:ℝ))
  let y: N:=⟨(B j p) f.val, pitch_bar Y H G j v f⟩
  change (Q).E u ((D₁ s) (X f)) ∈ _
  rw [through Y H V G iA R χ j s (shadow_heat Y H V G iA R χ j s u),show (Q).E u (X f)= X y from time_even Y H V G iA R χ j p v f]
  refine as_far Y H V G iA R χ j s b x h y ?_
  apply domain_mono Y H G _ (stride_region Y H G j p _ t); rintro _ ⟨w,p',rfl⟩; cases x
  · change w s.val+eject j (p:ℝ) s.val≤ d; rw [eject_away _ _ _ s.property,add_zero]; exact p'
  change d≤ w s.val + eject j (p:ℝ) s.val; rw [eject_away _ _ _ s.property,add_zero]; exact p'

lemma lane_heat (p:ℝ≥0): MapsTo ((Q).E p) (F b x) (F b x):=by
  apply SkyFold.from_spans _ (F b x) (closed_lane ..); intro z h;
  have hp(t:ℝ≥0)(ht:t∈ times (dainty Λ)) : (Q).E t z ∈ F b x:= by
    obtain ⟨i,v,rfl⟩:= MeshClock.split _ ht; let u:ν:= notch (dainty Λ) i (v:ℤ); let a:= whenly (dainty Λ) i v; have he:(u:ℝ)=(a:ℝ):= natural_time ..
    rw [show whenly _ _ _=Real.toNNReal (u:ℝ) by rw [he,Real.toNNReal_coe]]; exact here Y H V G iA R χ j s b x (lane_early Y H V G iA R χ j s b x u (he.symm ▸ a.property) h)
  exact closure_minimal hp ((closed_lane Y H V G iA R χ j s b x).preimage ((Q).continuousE z)) (fills _ p)
-- temporal localization ultra. reducing. use same CONTINUOUS clock as in real time
lemma stays_orth (t:ℝ) : MapsTo ((Q).edge t) (F b x) (F b x) := SkyFold.noexit (Q) (F b x) (lane_heat Y H V G iA R χ j s b x 1) t
lemma side_prices (b:ℝ) : (F b false) ≤ (F b true)ᗮ :=by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _); rw [Submodule.span_le]
  -- rhs orthogonal closures. simplify via orthogonal.span
  intro y hy; obtain ⟨d,hf,f,h,rfl⟩:=hy
  have h₁:(F b true)≤ (Submodule.span ℂ ({(D₁ s) (X f)}:Set (A)))ᗮ:= by
    apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _); rw [Submodule.span_le]; intro y' h'; obtain ⟨e,hq,g,h',rfl⟩:=h'
    let he : d < e := lt_trans (show d<b from hf) (show b<e from hq)
    change _∈ (Submodule.span _ _)ᗮ; apply mem_orthogonal_singleton_iff_inner_right.2 -- name
    have v:(D₁ s) ((D₁ s) (X g))=(D₁ s) (X g):=by rw [shadow, Submodule.starProjection_eq_self_iff.mpr (starProjection_apply_mem ..)]; -- tries wrong occurrence?
    rw [show inner ℂ ((D₁ s) _) _= inner ℂ (X f) ((D₁ s) ((D₁ s) (X g))) from ?_,v]; exact orth_consumed Y H V G iA R χ j s d e he f g h h'
    rw [shadow, inner_starProjection_left_eq_right]
  exact (Submodule.le_orthogonal_orthogonal _).trans (Submodule.orthogonal_le h₁) (Submodule.mem_span_singleton_self _) -- orientation function app fix
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
