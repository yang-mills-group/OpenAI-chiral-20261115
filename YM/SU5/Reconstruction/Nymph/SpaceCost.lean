import YM.SU5.Reconstruction.Nymph.RealRoll
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
open LightBudget
local notation "Ue" s:max=> (outfit Y H V G iA R χ j).crew s
local notation "Q'" i:max=> ride Y H V G.history G.clipped i false (R i) (c i)
variable (s:Trans j)
local notation "k'" => s.val
local notation "Zp" => OSvector Y H V G s.val (R s.val) (c s.val)
local notation "D'" => Domain Y H G false (flank s.val 0)
local notation "Kt" => flipMark k' K
local notation "Kj" => flipMark j K
local notation "mx" => stride (tent Y H) k'
local notation "κ" => glimpse Y H G j s

lemma flipped_left (f:Sky (tent Y H)) (a:ℝ)(h:f∈ D false (lowland s.val a)) : Kj f ∈ D false (lowland k' a) :=by
  apply domain_mono Y H G _ (mirror_support Y H G j f h)
  rintro _ ⟨z,h,rfl⟩; change mirrorE j 0 z s.val≤ a; rw [mirrorE, if_neg s.property]; exact h
lemma low_shift (f:Sky (tent Y H))(a b:ℝ)(x:ν)(p:a+(x:ℝ)≤ b) (h:f∈D false (lowland k' a)) : mx x f∈ D false (lowland k' b):=by
  apply domain_mono Y H G _ (stride_region Y H G s.val _ _ h); rintro _ ⟨u,v,rfl⟩; change u s.val+eject s.val (x:ℝ) s.val≤ b; rw [eject_at]; exact (add_le_add_left (show u s.val≤a from v) _).trans p
lemma low_flip (f:Sky (tent Y H))(h:f∈D false (lowland k' 0)) : Kt f∈ D':=by
  apply domain_mono Y H G _ (mirror_support Y H G s.val _ h); rintro _ ⟨v,h,rfl⟩; change (0:ℝ)≤ mirrorE s.val 0 v s.val; rw [mirrorE,if_pos rfl]; linarith [show v s.val ≤0 from h]
-- write for all ψ (loose marks). Use the chosen char literal from Pane. medium independent of Γ
variable (a b:ℝ) (p:a<b)
variable (f g: Domain Y H G false (flank j 0)) (t:f.val ∈ Domain Y H G false (lowland s.val a))
 (hz:g.val ∈ Domain Y H G false (flank s.val b))
include hz t p
lemma budget_overlap :
    ∃ (w : ν), 0<(w:ℝ) ∧ ∃ f' g':Domain Y H G false (flank s.val 0),∀ t':ν, 0 ≤ ((t'+w:ν):ℝ) →
      inner ℂ (X f) ((Ue s).play t' (X g))=inner ℂ (Zp f') ((Q' s.val).E (Real.toNNReal (((t'+w:ν):ℝ))) (Zp g')):=by
  obtain ⟨v, hv,hV⟩:= exists_between p
  obtain ⟨v₁,vx,h1⟩ := Schedule.walls (daylight (dainty Λ)) hv
  obtain ⟨v₂,h2,vy⟩ := Schedule.walls (daylight (dainty Λ)) hV
  let T' := mx (-v₁) (Kj f.val); let T₂ := v₂-v₁
  let f': D':= ⟨Kt T',low_flip Y H G j s T' (low_shift Y H G j s _ a 0 (-v₁) (by simp; linarith) (flipped_left Y H G j s f.val a t))⟩
  let g': D' := ⟨mx (-v₂) g.val,relax_shape Y H G s.val (-v₂) b 0 (by simp; linarith) g.val hz⟩
  refine ⟨T₂,(by unfold T₂; push_cast; linarith), f',g',fun x₁ t'=>?_⟩
  rw [owns_play,time_even Y H V G iA R χ s.val (x₁+T₂) t',registered_pair,registered_pair,os_across Y H V G iA (R iA) χ j (R j),os_across Y H V G iA (R iA) χ s.val (R s.val)]; symm
  let A₁:P:=⟨flipMark j K f.val * (κ x₁ g).val, paired_forever Y H G j _ _ f.property (κ x₁ g).property⟩
  refine (congrArg (osValue Y H V G iA (R iA) χ) (show _=(⟨_,economic Y H G s.val (-v₁) A₁.val A₁.property⟩:P) from Subtype.ext ?_)).trans (column_cost Y H V G iA R χ s.val (-v₁) A₁)
  change Kt (Kt T') * mx (x₁+T₂) (mx (-v₂) g.val) = mx (-v₁) (Kj f.val * mx x₁ g.val)
  rw [stride_mul,mirror_twice,stride_add,stride_add,show x₁+T₂+-v₂= -v₁+x₁ from (by unfold T₂; abel)]

lemma price_overlap : ContinuousAt (fun i:ν=> inner ℂ (X f) ((Ue s).play i (X g))) 0 := by
  obtain ⟨i,v,h,y,z⟩:= budget_overlap Y H V G iA R χ j s a b p f g t hz
  have he : Continuous (fun t:ν=> ((t+i:ν):ℝ)):= continuous_subtype_val.comp (continuous_id.add continuous_const)
  refine (continuousAt_const.inner ((Q' s.val).continuousE (Zp y) |>.comp (continuous_real_toNNReal.comp he) |>.continuousAt) : ContinuousAt (fun t:ν=> inner ℂ (Zp h) ((Q' s.val).E (Real.toNNReal (((t+i:ν):ℝ))) (Zp y))) _).congr ?_
  filter_upwards [(he.tendsto 0).eventually (le_mem_nhds (show 0 < (↑(0+i:ν):ℝ) by simpa using v))] with k h; exact (z k h).symm
-- project just the k-ambiguity globally
noncomputable def fourth (s:Trans j) : (indoor Y H V G.history G.clipped j false (R j) (c j)).Op := (Ue s).pi_c
local notation "Λ₀" s:max=>fourth Y H V G iA R χ j s
lemma overlapping : inner ℂ (X f) ((Λ₀ s) (X g))= inner ℂ (X f) (X g):=
  (Ue s).retain (innerSL ℂ (X f)) (X g) (price_overlap Y H V G iA R χ j s a b p f g t hz)

noncomputable def eclipse (s:Trans j) : (A).Op := 1- fourth Y H V G iA R χ j s
local notation "Δ" s:max=> eclipse Y H V G iA R χ j s
lemma orth_consumed : inner ℂ (X f) ((Δ s) (X g))=0:=by
 change inner ℂ _ (X g- (Λ₀ s) (X g))=0; rw [inner_sub_right,overlapping Y H V G iA R χ j s a b p f g t hz,sub_self]
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
