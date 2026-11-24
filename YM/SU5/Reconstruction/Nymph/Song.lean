import YM.SU5.Reconstruction.Nymph.Beat
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
local notation "Λ₀" => Ρ.register
local notation "B₀" => Ρ.register.ready t o
local notation "Ψ" j:max v:max=> prices Y H V G iA R χ x Ρ o t j v
local notation "W" u:max t:max=> watch Y H V G iA R χ x u t
local notation "Gt"=> marks (timeMesh Λ)
variable (r: List α) (p0: r.Nodup) (σ:∀i:Axis,r.Perm (o i))
-- q is any even p, but map to larger press budget.
lemma wagers (v: α → placement Λ) :
    wager Y H x (fun i j=> finerNow Λ (v i j)) r=generate Y H x v r := by
  unfold wager Chambers.generate; congr 1; congr 1; funext i; rw [old_steps]
lemma presence (v:α→placement Λ) : watch Y H V G iA R χ x (fun i j=> finerNow Λ (v i j)) r=score Y H V G iA R χ x v r:=by
  unfold watch Chambers.score; rw [wagers Y H x]; -- dependent rw
-- permission any strict per previous?
lemma permitted (u : Axis → ℝ)(v:Axis→ℝ)(h : u j=v j)(s:List α)(p' : (Λ₀).permission j true (enter p) u s): (Λ₀).permission j true (enter p) v s :=by cases s with
| nil=> exact p'
| cons i l=>
 simp only [permission_step,↓reduceIte] at *; exact ⟨by rw [Pi.sub_apply,←h]; exact p'.1,p'.2⟩
include σ in
lemma watch_march (k:Axis) (q:enter p∈ Ρ.register.ready t o):
    wager Y H x p r ∈ P ∧ watch Y H V G iA R χ x p r= inner ℂ (doorstep Y H V G.history G.clipped k false (R k) (c k))
      (coin Y H V G iA R χ k x Ρ p (enter p) ((t k k):ℝ) (o k) (doorstep Y H V G.history G.clipped k false (R k) (c k))) :=by
  have hx : (Λ₀).permission k true (enter p) (eject k ((finerNow Λ (t k k):ν):ℝ)) (o k):= permitted Y H G k x Ρ p _ _ (eject_at k _ |>.symm) (o k) (q k)
  have he:= score_beat Y H V G iA R χ k x Ρ p (o k) (finerNow Λ (t k k)) hx; rw [wager_perm Y H x p (σ k)]; unfold watch; rw [wager_perm Y H x p (σ k)]; exact he

include p0 σ in
-- arbitrary α; need electronic `curves` with regular continuation. this arclaw IDENTIFIES even press on whole open.
lemma press (u:enter p∈ B₀) : prices Y H V G iA R χ x Ρ o t j (enter p)= watch Y H V G iA R χ x p r:= by
  -- allow more of the axes to be at smaller stamp pitches. Continuity within one k clock, independently, NO uniform speed budgets.
  suffices h:∀ Ll:Finset Axis,∀ p:Σx, (enter p∈ B₀) → (∀ j∉Ll,∀ i:α,∃ y : marks (timeMesh Λ), finerNow Λ y=p i j) → Ψ j (enter p)=W p r from h Finset.univ p u (by simp)
  intro i; induction i using Finset.induction_on with
  | empty=>
    intro p u h; choose v hv using fun (j:Axis)=> h j (by simp); -- hv j i
    let v' : α → placement Λ := fun i j=> v j i
    rw [show p=(fun i j=> finerNow Λ (v' i j)) from funext fun i=> funext fun j=> (hv j i).symm,presence]; refine (prices_here Y H V G iA R χ x Ρ o t r p0 σ j v' ?_).2
    rw [show enter v'=enter p from ?_]; exact u
    ext i j; change (v j i:ℝ)=(p i j:ℝ); exact congrArg Subtype.val (hv j i)
  | @insert k s v ih=>
    intro p' u' h; let f:=(fun (w:α→(ν)) (i:α) (j:Axis)=> if j=k then w i else p' i j);
    let y':α→ν := fun i=> p' i k
    have agree (w:α→ν)(i:α): still Y H k x (f w) i=still Y H k x p' i:= sparely Y H k _ _ _ (fun _ v=> if_neg v)
    have he : Continuous fun p:Σx=> enter p :=continuous_pi (fun i=>continuous_pi fun j=> continuous_subtype_val.comp ((continuous_apply j).comp (continuous_apply i)))
    have he':Continuous f:=by
      unfold f; apply continuous_pi; intro i; apply continuous_pi; intro j; by_cases h:j=k
      · simpa [h] using (continuous_apply («A»:=fun i:α=> ν) i)
      simp_rw [if_neg h]; exact continuous_const -- tune indentation
    let U:= {w:α→ν| enter (f w) ∈ B₀}; have openU:IsOpen U:=(ready_open ..).preimage (he.comp he'); let w(k':α→Gt):α→ν:= fun i=> finerNow Λ (k' i)
    have g : DenseRange w:= DenseRange.piMap («X»:=fun i:α=> marks (timeMesh Λ)) (fun _=> from_dainty)
    let Ωk:=doorstep Y H V G.history G.clipped k false (R k) (c k)
    let ϕ:= fun w:α→ ν=> inner ℂ Ωk (coin Y H V G iA R χ k x Ρ p' (enter (f w)) (paste (t k) k) (o k) Ωk)
    have hp: Continuous ϕ:= continuous_const.inner (currency Y H V G iA R χ k x Ρ p' (fun w=> enter (f w)) (fun w=>paste (t k) k) (fun _=> Ωk) continuous_const (o k) (he.comp he') continuous_const)
    have ht(v : α→ν)(e:v∈U) : ϕ v= W (f v) r :=by
      rw [ (watch_march Y H V G iA R χ x Ρ o t (f v) r σ k e).2 ] -- dot args
      have hx: coin Y H V G iA R χ k x Ρ p'= coin Y H V G iA R χ k x Ρ (f v):=by unfold coin; rw [show stage Y H V G iA R χ k x Ρ (f v)= stage Y H V G iA R χ k x Ρ p' from funext (fun i=>stage_kept Y H V G iA R χ k x Ρ (f v) p' i (agree v))]
      unfold ϕ; rw [hx]; rfl
    have eh : f y'=p':= by funext i j; unfold f y'; split_ifs with h <;> simp_all only
    have hU:y'∈U:=by unfold U; simp [eh]; exact u'
    have e₁: prices Y H V G iA R χ x Ρ o t j (enter (f y'))= ϕ y' := close_on_open (D':=U) g ((prices_cont Y H V G iA R χ x Ρ o t j).comp (he.comp he')) hp openU ?_ hU
    swap
    · rintro i ⟨t,⟨g0,rfl⟩⟩ -- intersection orientation
      rw [ht _ t]
      apply ih (f _) t
      intro j' v' i; by_cases hx:j'=k
      · subst j'; exact ⟨g0 i, (if_pos rfl).symm⟩
      specialize h j' (by simp [hx,v']) i -- v'
      exact (show f (w g0) i j' = p' i j' from if_neg hx).symm ▸ h
    have hu:= ht y' hU; rw [eh] at hu e₁; exact e₁.trans hu
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
