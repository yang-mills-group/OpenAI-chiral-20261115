import YM.SU5.Reconstruction.Nymph.Ladder
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

local notation "U" s:max=> ((outfit Y H V G iA R χ j).crew s)
variable (s : Trans j)
local notation "P'" => glimpse Y H G j s
lemma owns_play (x:ν) (f:N) : (U s).play x (X f)= X (P' x f):= rises_even Y H V G iA R χ j s x f
-- The spine clocks are at the same labels
lemma comm_heat (x:ν)(t:ℝ≥0) : ((U s).play x).comp ((Q).E t) = ((Q).E t).comp ((U s).play x) := by
  let u:= (U s).play x
  have he (t:ν)(p:0 ≤ (t:ℝ)) (v : N): u ((Q).E (Real.toNNReal (t:ℝ)) (X v))= (Q).E (Real.toNNReal (t:ℝ)) (u (X v)):= by
    unfold u; rw [time_even Y H V G iA R χ j t p, owns_play, owns_play,time_even Y H V G iA R χ j t p]
    exact congrArg X (Subtype.ext (stride_cross ..))
  have hf (y:N) : (fun t:ℝ≥0=>u ((Q).E t (X y))) = fun t:ℝ≥0=>(Q).E t (u (X y)) :=by
    apply (fills (dainty Λ)).denseRange_val.equalizer (u.continuous.comp ((Q).continuousE (X y))) ((Q).continuousE (u (X y)))
    funext t; obtain ⟨a,b,h⟩:= MeshClock.split _ t.property; let z: ν:= notch (dainty Λ) a (b:ℤ)
    have hz:(z:ℝ)= ((t:ℝ≥0):ℝ):=(natural_time _ _ _).trans (congrArg (fun x:ℝ≥0=>(x:ℝ)) h)
    have p:0≤ (z:ℝ):=hz.symm ▸ (t:ℝ≥0).property
    dsimp only [Function.comp_apply]; have H₁:= he z p y; rw [hz,Real.toNNReal_coe] at H₁; exact H₁
  apply DFunLike.ext'
  apply (attains_full_axis Y H V G iA j R χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext w; exact congrFun (hf w) t

lemma older_clock (x : marks (timeMesh Λ)) : Ξ (eject s.val x)= ((V₀).crew s).play x:=by
  unfold atEstate; rw [eject_away s.val x j s.property.symm]; change ((Q).E (Real.toNNReal (0:ℝ))).comp _=_; rw [Real.toNNReal_zero,OS.Semigroup.eZero]
  have he:(fun i:Trans j=> eject s.val x i.val)=Function.update (0:Trans j→marks (timeMesh Λ)) s x:=by
    funext i; by_cases h:i=s; · subst i; simp
    have h':i.val≠ s.val:=fun v=> h (Subtype.ext v); simp [h,h']
  rw [he, spotlight (V₀) _ (look_one j) (look_all j s)]; rfl
lemma older_stride (x:marks (timeMesh Λ)) : (U s).play (finerNow Λ x)= ((V₀).crew s).play x:=by
  apply DFunLike.ext'; apply (attains_full_axis Y H V G iA j R χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext f; change (U s).play (finerNow Λ x) (X f)= ((V₀).crew s).play x (X f)
  let p: 0≤ ((eject s.val x j).val:ℝ):= by rw [eject_away s.val x j s.property.symm]; exact le_refl (0:ℝ)
  rw [owns_play,← older_clock Y H V G iA R χ j s]
  rw [← transported_ket Y H V G j (R j) (c j) _ f.property (eject s.val x) p (later_frame Y H V G _ _ _ f.property p)]; exact congrArg X (Subtype.ext (by rw [show (P' _ f).val= (B s.val (finerNow Λ x)) f.val from rfl,earlier_here Y H])) -- tune
-- commute with real time via uniqueness `charge`
lemma comm_lit (x:ν)(t:ℝ) : Commute ((U s).play x) ((Q).edge t) := (lamp_orbit (Q) (show Commute ((Q).E 1) ((U s).play x) from (comm_heat Y H V G iA R χ j s x 1).symm) t).symm
local notation "Πf" => (saunters Y H V G.history G.clipped j false (R j) (c j)).starProjection
lemma commencing (x:ν)(v : Trans j)(t : marks (timeMesh Λ)) : Commute ((U s).play x) (((V₀).crew v).play t) := by
 rw [← older_stride Y H V G iA R χ]; exact (outfit Y H V G iA R χ j).cCom s v _ _
lemma even_preserves (x:ν) : Commute (Πf) ((U s).play x) := by
 rw [← stack_projection]; exact ((V₀).ground (look j) _ (fun i _ y=> (commencing Y H V G iA R χ j s x i y).eq.symm)).symm
lemma heat_preserves (x:ℝ≥0) : Commute (Πf) ((Q).E x) := by
 rw [← stack_projection]; exact ((V₀).ground (look j) _ (fun _ _ _=> follows_road Y H V G.history G.clipped j false (R j) (c j) ..)).symm
lemma larger_lives : (U s).lives (A) ≤ ((V₀).crew s).lives (A) :=by
  intro z h; apply (((V₀).crew s).living).2
  intro ε e; obtain ⟨t,h,p⟩:= ((U s).living).1 h ε e
  exact ⟨t,h,fun j' hj=> by rw [← older_stride]; exact p (finerNow Λ j') hj⟩
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
