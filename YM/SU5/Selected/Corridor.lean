import YM.SU5.Selected.Mingle
import YM.SU5.Selected.HearthMix
/-!
# CP5. No spectral assumptions: exploit chart rotations (overlap identity not spacetime sym)
to obtain some stronger cluster limits. NOT the full spacelike cluster assertion.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 340000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
local notation "S"=> turnstile Y H V Q Qt j strict C f
local notation "R" => ride Y H V Q Qt j strict C f
local notation "P" k:max => (S).crew k
local notation "T" => look j
open Germ SelectionAnalysis Sunbelt
local notation "Ξ"=> mainsea Y H V Q Qt j strict C f
local notation "δ"=> daylight Μ
local notation "U" i:max z:max=> (((S).crew i).play z)
local notation "Γ"=> MeshClock.marks Μ
local notation "sel" v:max=> (Ξ).plane v
local notation "V'" v:max => atEstate Y H V Q Qt j strict C f v
local notation "κ" s:max t:max=> Moving.pause (spotter Μ (S) s) t
local notation "L"=> fort Y H V Q Qt j strict C f
local notation "Π₀"=> peninsula Y H V Q Qt j strict C f
local notation "Ω₁"=> vocation Y H V Q Qt j strict C f
/-- Keep u dependence in the second term (once we project for K, those motions disappear).
No regularity assumption on vectors in the other directions or on full H. 
No claim that *just* one unbounded direction gives convergence to rank-one. -/
lemma mix_coordinate (k:List (Trans j))(u v:Ρ)(s:ℕ)(t:ℝ)(p:0<t): ∃ b:ℝ,∀ w:placement Λ, (∀ a∈k,b ≤ |(w a.val : ℝ)|) → uptown j w →
      ‖inner ℂ u ((V' w) v) - inner ℂ u ((V' w) ((κ s k) v))‖ ≤ t:=
  (Ξ).worldly (R) rfl (follows_road Y H V Q Qt j strict C f) (mix_first Y H V Q Qt j strict C f) _ _ s k _ p
-- physical k aliases
lemma grades_agree (k:List (Trans j))(v:Ρ)(r:ℕ): v∈ Moving.aligned (spotter Μ (S) r) k ↔ ∀ i∈ k,∀ (t:marks Μ),(U i t) v=v:=by
 rw [Moving.aligned_ok]; apply forall_congr'; intro i; apply forall_congr'; intro i'
 rw [← Rolls.calm_mem]; exact (Ξ).quiet (R) rfl i v r (mix_first Y H V Q Qt j strict C f i)

-- on heat displacement to infinity and all spatial coordinates also to infinity
variable (p: Victory Y H V Q Qt strict j C f)
include p
lemma mix_annulus (x y:Ρ)(l:ℝ)(h:0<l): ∃ b:ℝ,0≤ b ∧ ∀ u:placement Λ,b ≤ (u j:ℝ)→ (∀ i:Trans j,b ≤ |(u i.val : ℝ)|) →
    ‖inner ℂ x ((V' u) y) - inner ℂ x Ω*inner ℂ Ω y‖ ≤ l:= (Ξ).intermingled (R) rfl (follows_road Y H V Q Qt j strict C f) (mix_first Y H V Q Qt j strict C f) _ (fun _ h t=> one_real Y H V Q Qt j strict C f p ⟨(lamp_fixed ..).2 ((R).fixed _|>.1 h),t⟩) (resides_real Y H V Q Qt j strict C f).2 ((R).fixed _|>.2 ((lamp_fixed ..).1 (resides_real Y H V Q Qt j strict C f).1)) (ready ..) _ _ _ h -- tune
lemma model_mixes (x y:L)(l:ℝ)(h:0<l): ∃ b:ℝ,0≤ b ∧ ∀ u:Axis→ℝ,b < u j → (∀ i:Trans j,b < |u i.val|) →
    ‖inner ℂ x ((Π₀).E ((u j).toNNReal) ((Π₀).U (diameter u) y)) - inner ℂ x Ω₁ * inner ℂ Ω₁ y‖ ≤ l :=by
    obtain ⟨b,r,q⟩:= (Ξ).glass_mingle (R) rfl (follows_road Y H V Q Qt j strict C f) (mix_first Y H V Q Qt j strict C f) Ω (fun _ h t=> one_real Y H V Q Qt j strict C f p ⟨(lamp_fixed ..).2 ((R).fixed _|>.1 h),t⟩) (resides_real Y H V Q Qt j strict C f).2 ((R).fixed _|>.2 ((lamp_fixed ..).1 (resides_real Y H V Q Qt j strict C f).1)) (ready ..) x y _ h
    refine ⟨b,r,fun u h t=>?_⟩; specialize q u h t
    rw [← vocate] at q; exact q
-- upper coordinates *not* necessarily disjoint on the RHS since these queries already prepared. Uniform chart pair-reading statement in actual costs. No PPC, only on claims that are already budgeted for future-vs-past. Distinct from true spatial cluster issue.
lemma mix_response_pair (x y: 𝔙 s)(l:ℝ)(h:0<l) : ∃ b:ℝ,0≤ b∧∀ u:placement Λ,b ≤ (u j:ℝ)→(∀ i:Trans j,b ≤ |(u i.val:ℝ)|)→
    ∀(r:ℕ),s ≤ r→∀ t:Cover,(∀k, notch Μ r (t k)=u k) →
    ‖(Ε r) (upGrade Y H s Q strict ((Θ) ((M₁ s) x)) r * relocateWorld Y H strict t (upGrade Y H s Q strict ((M₁ s) y) r)) - (Ε s) ((Θ) ((M₁ s) x)) * (Ε s) ((M₁ s) y)‖ ≤ l:=by
  obtain ⟨b,x₁,h₁⟩:= mix_annulus Y H V Q Qt j strict C f p (a₀ s x) (a₀ s y) l h
  refine ⟨b,x₁,fun v k₁ t₁ r r' v' l'=>?_⟩
  rw [← visits_higher Y H V s Q Qt j strict C f _ _ _ (show uptown j v from x₁.trans k₁) _ r' v' l', show ((Ε s)) ((Θ) ((M₁ s) x))=_ from all_mirror Y H V s Q Qt j strict C f ((M₁ s) x) j, ← call, ←call]
  rw [show star _ = inner ℂ (a₀ s x) Ω from inner_conj_symm ..]
  exact h₁ v k₁ t₁
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.mix_coordinate
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.mix_response_pair
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.model_mixes
