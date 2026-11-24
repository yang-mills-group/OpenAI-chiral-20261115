import YM.SU5.Reconstruction.Nymph.AlwaysFar
import YM.SU5.Reconstruction.Nymph.Footprints
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
local notation "Kk"=> (saunters Y H V G.history G.clipped j false (R j) (c j))
local notation "V₁"=> (Kk).orthogonalProjectionOnto
local notation "Hc"=> fort Y H V G.history G.clipped j false (R j) (c j)
local notation "Xt"=>physicalKet Y H V G j (R j) (c j)
local notation "Γ"=> compassKet Y H V G j (R j) (c j)
local notation "Qₜ"=> peninsula Y H V G.history G.clipped j false (R j) (c j)
local notation "W" d:max x:max=> (marksLane Y H V G iA R χ j s d x)
local notation "F" d:max x:max=> traceLane Y H V G iA R χ j s d x

lemma cast_receives (f:N) : ∃ d v:ℝ, f.val∈Domain Y H G false (sideLand s.val d false) ∧
  room d v false ∧ (D₁ s) (X f)∈ F v false:= by
 obtain ⟨W₁,c',p,u⟩:= (compact_domain Y H G).1 f.property
 obtain ⟨a,b,k⟩:= Schedule.surrounding c' s.val
 have h: f.val∈ D false (lowland s.val b) := domain_mono Y H G (fun x p=> (k x p).2.le) u
 exact ⟨b,b+1,h,show b<b+1 by linarith,here Y H V G iA R χ j s _ false (as_far Y H V G iA R χ j s _ false (d:=b) (by change b<b+1; linarith) f h)⟩
-- Opposite direction full unproj orthogonality needed later
lemma lane_shields (b:ℝ) (u: A) (y:u ∈ F b false)(f:N)(v : ℝ)(p : b<v)
    (h:f.val∈ D false (sideLand s.val v true)) : inner ℂ (X f) u=0:=by
  have hz:u ∈ Z s := priced_shadow Y H V G iA R χ j s b false y
  have hv:= (side_prices Y H V G iA R χ j s b y : u∈ (F b true)ᗮ)
  have hp:(D₁ s) (X f)∈ F b true:= here Y H V G iA R χ j s _ true (as_far Y H V G iA R χ j s _ true (d:=v) p f h)
  apply Eq.trans _ (inner_right_of_mem_orthogonal hp hv); rw [shadow,inner_starProjection_left_eq_right,starProjection_eq_self_iff.mpr hz]

section Forward
variable (tF : ConePrice.Forward (peninsula Y H V G.history G.clipped j false (R j) (displacement Y H V G.history G.clipped iA false (R iA) χ j (R j))))
include tF
lemma withdraw (b:ℝ)(u:Hc)(p:u.val∈ F b false) : u=0:=by
  let L₁:= far Y H V G j (R j) (c j) s.val (b+1) true
  apply Dense.eq_zero_of_mem_orthogonal («K»:=L₁) _ _
  · exact even_closer Y H V G j (R j) (c j) s.val s.property tF (b+1) true -- K notation collision?
  intro v hv; obtain ⟨f,rfl⟩:= LinearMap.mem_range.mp hv
  let g:N:=⟨f.val,domain_mono Y H G inter_subset_left (domain_loose Y H G _ f.property)⟩
  change inner ℂ (V₁ (X g)) u=0
  rw [inner_orthogonalProjectionOnto_eq_of_mem_right]; exact lane_shields Y H V G iA R χ j s b u.val p g (b+1) (by linarith) (domain_mono Y H G inter_subset_right (domain_loose Y H G _ f.property))
lemma lane_free (b:ℝ)(u:A)(p:u∈ F b false) : (Π₀) u=0:= by
  have he := older_lives_on_lane Y H V G iA R χ j s b false p
  exact congrArg Subtype.val (withdraw Y H V G iA R χ j s tF b ((V₁) u) he)
lemma zero_focus : (Π₀).comp (D₁ s)= 0 := by
  apply DFunLike.ext'; apply (attains_full_axis Y H V G iA j R χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext f; obtain ⟨_,v,-,-,p⟩:= cast_receives Y H V G iA R χ j s f; exact lane_free Y H V G iA R χ j s tF v _ p
lemma bought_under_forward : Kk ≤ L' s:=by
  intro z e
  apply ((L' s).starProjection_eq_self_iff).1
  have hz : (D₁ s) z=0:=by
    nth_rw 1 [← (Kk).starProjection_eq_self_iff.mpr e, ← ContinuousLinearMap.comp_apply,show (D₁ s).comp Π₀=0 from (shadow_kept Y H V G iA R χ j s).eq.trans (zero_focus Y H V G iA R χ j s tF)]; rfl
  exact (sub_eq_zero.mp hz).symm
lemma sector_progress : (outfit Y H V G iA R χ j).aviator (look j)= Kk:= by
  apply le_antisymm
  · intro z v; exact ((V₀).assembled _ _).2 (fun i p=>larger_lives Y H V G iA R χ j i (((outfit Y H V G iA R χ j).assembled _ _).1 v i p))
  intro z v; exact ((outfit Y H V G iA R χ j).assembled _ _).2 (fun i _=> bought_under_forward Y H V G iA R χ j i tF v)
-- No need to redo continuum construction. for EVERY even stamp can pay as before CP2.
lemma enjoy (u:Hc) (v:ν) : ((Qₜ).U ((v:ℝ) • transversal j s.val s.property) u:Kk).val= (U s).play v u.val:=by
  let r (x:ν):A:= ((Qₜ).U ((x:ℝ) • transversal j s.val s.property) u:Kk).val; let pe(x:ν):= (U s).play x (u.val:A)
  have h : Continuous r := by unfold r; exact continuous_subtype_val.comp (((Qₜ).continuousU u).comp (continuous_subtype_val.smul continuous_const))
  have he : Continuous pe := ((U s).far (bought_under_forward Y H V G iA R χ j s tF u.property)).continuous
  have hf : DenseRange (finerNow Λ):= by
    intro x; rw [Metric.mem_closure_iff]; intro ε v
    obtain ⟨p,h,w⟩:= Schedule.walls (daylight (timeMesh Λ)) (show (x:ℝ)<(x:ℝ)+ε by linarith)
    refine ⟨finerNow Λ p,⟨p,rfl⟩,?_⟩; change dist (x:ℝ) (p:ℝ) < ε; rw [Real.dist_eq, abs_of_neg (sub_neg.mpr h)]; linarith
  have hi : r=pe:= hf.equalizer h he (funext fun p : marks (timeMesh Λ)=> ?_)
  exact congrFun hi v
  -- `x` ALWAYS old regular. panel formula from mainsea. both workers. proof of transverse distance calibration
  change ((Qₜ).U (((finerNow Λ p:ν):ℝ) • transversal j s.val s.property) u:Kk).val= (U s).play (finerNow Λ p) u.val
  rw [older_stride Y H V G iA R χ j s p]
  rw [show ((finerNow Λ p:ν):ℝ) • transversal j s.val s.property= diameter (fun i:Axis=> (Function.update (0:Axis→marks (timeMesh Λ)) s.val p i).val) from ?_] -- uses ↑ projection architecture
  · exact pane_grid Y H V G.history G.clipped j false (R j) (c j) u s p
  apply Subtype.ext; ext k
  by_cases l:k=j
  · subst k; change _ = _; rw [show (diameter (a:=j) _).val j=0 from ((diameter (a:=j) (fun i:Axis=> (Function.update (0:Axis→marks (timeMesh Λ)) s.val p i).val)).property)]; simp [transversal,s.property.symm] -- patch
  rw [diameter_at _ _ l]; by_cases k': k=s.val; · simp [k',transversal,finerNow]
  simp [k',transversal,finerNow]
end Forward
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
