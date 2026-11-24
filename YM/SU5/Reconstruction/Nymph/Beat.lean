import YM.SU5.Reconstruction.Nymph.Swoop
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
open Schedule Fixture Compose
variable {α : Type*} (x : α→Sky (tent Y H))
variable (Ρ:Presentable Y H G x)
variable (o : Axis→ List α) (t : Axis→placement Λ)
local notation "δ" => (Axis → marks (dainty Λ))
local notation "Σx" => (α→Axis→ marks (dainty Λ))
local notation "F" => (osValue Y H V G iA (R iA) χ)
local notation "Ω" => (doorstep Y H V G.history G.clipped j false (R j) (c j))
set_option quotPrecheck false
local notation "Φ" => all_steps Y H
variable (p: α→ Axis→ marks (dainty Λ))
noncomputable def wager (t:List α) := (t.map (fun i=>all_steps Y H (p i) (x i))).prod
local notation "W₁" p:max t:max=> wager Y H x p t
lemma wager_step (t:List α)(i:α) : W₁ p (i::t)= Φ (p i) (x i) * W₁ p t:= rfl
lemma wager_perm {s t:List α} (h:s.Perm t) : W₁ p s=W₁ p t := (h.map _).prod_eq
noncomputable def watch (p:Σx)(s:List α) : ℂ := if h:wager Y H x p s ∈ P then (osValue Y H V G iA (R iA) χ) ⟨wager Y H x p s,h⟩ else 0
noncomputable def still (i:α) := polarHalf Y H j (p i) (x i)
local notation "G₀" => Ρ.register
local notation "ω" i:max => (G₀).width i j -- `G₀` notation not atom for .low? parent
local notation "ζ" i:max => (G₀).low i j
local notation "Kₜ" i:max=> (still Y H j x p i)
local notation "Lt" p:max i:max=> p i j+ finerNow Λ (ζ i)
local notation "mx" => stride (tent Y H) j
lemma still_range (i:α) : Kₜ i ∈ D false (strip j (ζ i:ℝ) ((ζ i:ℝ)+(ω i:ℝ))) := polar_range Y H G j _ (x i) _ _ (Ρ.shielded j i)
include V in
lemma issued (i:α) : move K (-(eject j (ζ i))) (Kₜ i)∈ D false (strip j 0 (ω i:ℝ)) := Chambers.register Y H V G (G₀) _ j (fun i=> still_range Y H G j x Ρ p i) i
noncomputable def stage (i:α) := signal Y H V G Ρ.register (fun k=> still Y H j x p k) j (R j) (c j) (fun i=>still_range Y H G j x Ρ p i) i
local notation "S₀" p:max=> stage Y H V G iA R χ j x Ρ p
noncomputable def coin (p:α→Axis→marks (dainty Λ))(v:α→Axis→ℝ): ℝ→ List α→ (indoor Y H V G.history G.clipped j false (R j) (c j)).Op := roll (fun _ s=>(Q).E (Real.toNNReal s)) (stage Y H V G iA R χ j x Ρ p) (fun a=> Ρ.register.start j v a j) (fun a=> Ρ.register.stop j v a j)
local notation "ψ" p:max v:max=> coin Y H V G iA R χ j x Ρ p v

lemma permissions (v:α→Axis→marks (dainty Λ)) (q q': Axis→ℝ)(h:q j=q' j)(s:List α)(p : (G₀).permission j false (enter v) q s): (G₀).permission j false (enter v) q' s :=by cases s with
| nil=>exact p
| cons i l=>
 simp only [permission_step,Bool.false_eq_true, ↓reduceIte] at *
 exact ⟨by rw [Pi.sub_apply,←h]; exact p.1,p.2⟩

lemma stays (s: List α) (u:ν) (h:(G₀).permission j false (enter p) (eject j (u:ℝ)) s): ∃ z : Domain Y H G false (flank j 0),
    z.val = mx (-u) (wager Y H x p s) ∧ X z= (ψ p (enter p)) (u:ℝ) s (Ω) :=by
  induction s generalizing u with
  | nil=> exact ⟨⟨_,domain_one ..⟩,(stride_one (-u) (tent Y H) j).symm,vacuum_ticket ..⟩
  | cons i s ih=>
    simp only [permission_step,Bool.false_eq_true,↓reduceIte] at h
    let a:= p i j + finerNow Λ (ζ i); let w:= finerNow Λ (ω i); let b:= a+w; let y:= a-u
    have hA:(G₀).start j (enter p) i j=a := by rw [Fixture.start,Pi.add_apply,Pi.single_eq_same]; rfl
    have hB:(G₀).stop j (enter p) i j=b:=by rw [Fixture.stop,Pi.add_apply,hA, Pi.single_eq_same]; rfl
    obtain ⟨u',hu,k⟩:= ih b (permissions Y H G j x Ρ p _ _ (hB.trans (eject_at j (b:ℝ)).symm) s h.2) -- arg order
    obtain ⟨w',hw,hv⟩:= (journey_cost Y H V G Ρ.register (still Y H j x p) j (R j) (c j) (fun i=>still_range Y H G j x Ρ p i) i).graph u'
    have hp : 0≤ (y:ℝ) := by
      have hx : 0≤ ((G₀).start j (enter p) i - eject j (u:ℝ)) j:=h.1; rw [Pi.sub_apply,hA,eject_at] at hx; exact hx
    refine ⟨⟨_,pitch_bar Y H G j hp w'⟩,?_,?_⟩
    · change stride K j y w'.val=_
      rw [hw,hu]; change mx y (move K (-(eject j (ζ i))) (Kₜ i) * move K (eject j (ω i)) _) = _; rw [wager_step,swoop_all Y H j (p i),stride_mul,stride_mul,← LightBudget.eject_neg,← earlier_here Y H j (-(ζ i)),← earlier_here Y H j (ω i)]
      dsimp only [b]; simp only [stride_add,map_neg]; rw [show y + (finerNow Λ (ω i)+ -(a+w)) = -u from (by unfold w y; abel),
        show y + -(finerNow Λ (ζ i)) = -u + p i j from (by unfold y a; abel)]; rfl
    change X ⟨mx y w'.val,_⟩ = _; rw [← time_even Y H V G iA R χ j y hp w', hv,k]; unfold coin; rw [roll_step,hA,hB]; rfl

lemma score_beat (s:List α)(u:ν)(p1: (G₀).permission j true (enter p) (eject j (u:ℝ)) s):
    wager Y H x p s∈ Domain Y H G false Set.univ ∧
      watch Y H V G iA R χ x p s= inner ℂ (Ω) ((coin Y H V G iA R χ j x Ρ p (enter p) (u:ℝ) s) (Ω)):=by
  obtain ⟨z,h,q⟩:= stays Y H V G iA R χ j x Ρ p s u ((G₀).permission_ge _ _ _ _ p1)
  have t : wager Y H x p s= mx u z.val :=by rw [h,stride_add,add_neg_cancel,stride_zero]
  let f:P:=⟨z.val,domain_mono Y H G (Set.subset_univ _) z.property⟩
  have h := (economic Y H G j u _ f.property)
  have he:wager Y H x p s∈ P:=by rw [t]; exact h
  refine ⟨he,?_⟩; unfold watch; rw [dif_pos he, ←q, FirstWindows.expectation,os_across Y H V G iA (R iA) χ]
  refine Eq.trans ?_ (column_cost Y H V G iA R χ j u f); exact congrArg (F) (Subtype.ext t)
lemma stage_kept (q:Σx) (i:α)(h:∀ i, still Y H j x p i=still Y H j x q i) : stage Y H V G iA R χ j x Ρ p i=stage Y H V G iA R χ j x Ρ q i:= by
  -- change entire launch method rather than pay uniqueness of estimates
  have he : still Y H j x p=still Y H j x q:=funext h
  unfold stage; congr 2
section geometry
variable {ι: Type*} [TopologicalSpace ι] (w : ι→α→Axis→ℝ) (u:ι→ℝ)
include V
lemma currency (T': ι → A) (ht:Continuous T')(a:List α)(hw:Continuous w)(p₀:Continuous u): Continuous (fun t':ι=> (ψ p (w t')) (u t') a (T' t')) := by
  induction a generalizing u with
  | nil=> exact ht
  | cons i a ih=>
    simp only [coin, roll_step, ContinuousLinearMap.comp_apply]; refine actor_continuous _ 1 zero_lt_one ?_ ?_ _ ((ContinuousLinearMap.continuous _).comp ?_)
    · intro z y; exact (((Q).E _).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((Q).shrinks _) (norm_nonneg _))
    · intro z; exact ((Q).continuousE z).comp (continuous_real_toNNReal.comp (((continuous_apply j).comp (((G₀).start_cont j i).comp hw)).sub p₀))
    exact ih (fun a=> (G₀).stop j (w a) i j) ((continuous_apply j).comp (((G₀).stop_cont j i).comp hw))
end geometry

end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
