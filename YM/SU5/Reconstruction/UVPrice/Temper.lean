import YM.SU5.Reconstruction.UVPrice.Walls
import YM.Fields.Spectrum
/-!
# Single-ground authentication by prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
variable (Ω:H)(p: ‖Ω‖=1)(e:∀ t:E4,S.unit.translation t Ω=Ω)
variable (x:H)
lemma alongTemp (u:ℝ): S.unit.translation (u • basis a) (cue S x)= cue S x:= by
 let Q : Set E4:= toe a
 suffices he: trans S (u • basis a)*cue S=cue S from DFunLike.congr_fun he x
 apply Registers.single ((story S (u • basis a)).times (toe_pays S))
 convert toe_pays S using 1; funext y; by_cases h:y∈ toe a
 swap; · simp only [Pi.mul_apply, indicator_of_notMem h, mul_zero]
 simp only [Pi.mul_apply, indicator_of_mem h]; unfold plane; rw [real_inner_smul_right,innerB, show y a=0 from h]; simp -- tactic global?
-- geometry independence of coordinate test sufficient.
include e in
lemma goesHome: cue S Ω=Ω:= by rw [cue_ground]; exact S.ground.starProjection_eq_self_iff.mpr (by exact offiero S Ω fun _=>e _) -- tune call
lemma full_basis (h:∀ (b:Axis)(u:b≠a)(s:ℝ), S.U (s • cross a b u) (cue S x)= cue S x)(p:E4): S.unit.translation p (cue S x)=cue S x:=by
 have he: ∑ i:Axis,p i • basis i=p:=by ext1 i; simp
 suffices ∀ i:Finset Axis, S.unit.translation (∑ j∈i,p j • basis j) (cue S x)=cue S x by rw [←he, this]
   -- rw [←he] changes S.unit p fine not p elsewhere
 intro i; induction i using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty,S.unit.origin]; rfl
 | @insert i j k ih=>
   rw [Finset.sum_insert k,← S.unit.sends,ContinuousLinearMap.comp_apply,ih]; by_cases u:i=a
   · subst i; exact alongTemp ..
   change trans S _ _=_; rw [trans_space i _ S (h:=u)]; exact h i u (p i)
-- call the hearth.Occupancy for every x needed
abbrev Hearth := ∀ x:H, cue S x=inner ℂ Ω x • Ω
include p e
lemma allHearth (h:∀ x:H, (∀ t:E4,S.unit.translation t x=x) → ∃ z:ℂ,z • Ω=x) (b:∀ (x:H)(b:Axis)(u:b≠a)(s:ℝ), S.U (s • cross a b u) (cue S x)=cue S x): Hearth S Ω:= by
 intro x; obtain ⟨z,hx⟩:=h (cue S x) (full_basis S x (b x))
 suffices z=inner ℂ Ω x by rw [←this,hx]
 have he:= goesHome S Ω e
 nth_rw 1 [←he]
 rw [← show (cue S).adjoint=cue S from (cue_project S).2, ContinuousLinearMap.adjoint_inner_left,←hx,inner_smul_right,inner_self_eq_norm_sq_to_K,p]; simp
omit p e
lemma orthStick {U:Submodule ℂ H}(w:U≤S.ground)(v:H)(h:v∈U): cue S v=v:= by rw [cue_ground]; exact S.ground.starProjection_eq_self_iff.mpr (w h)
end YM.Roy
