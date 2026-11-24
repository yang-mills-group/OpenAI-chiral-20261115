import YM.SU5.Selected.Longitude
import YM.SU5.Selected.CompassGlass
import YM.SU5.Selected.Conveyance
/-! # Reconstruct true space-time translation groups on the CP4 compass sector,
with semantics and projection as stated. Main application.

Loses unproven spatial continuity on entire H. Calls only in the continuous sector,
and comparisons to the CP2 full resolving hierarchy prove precise connections back to it.
Edge heat and real time genuine analytic continuation, PVM through this group.
No Lorentz invariant cone asserted (momentum orthogonal to a not yet controlled),
full QFT spacetime locality and continuum still open.
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
abbrev saunters := (turnstile Y H V Q Qt j strict C f).aviator (look j)
local notation "K₀"=> saunters Y H V Q Qt j strict C f
noncomputable def fort := (turnstile Y H V Q Qt j strict C f).Realm (look j)
local notation "L"=> fort Y H V Q Qt j strict C f
local notation "P₀"=> (K₀).orthogonalProjectionOnto

lemma follows_road (i : {x:Axis//x≠j})(v:marks Μ)(e:ℝ≥0): ((P i).play v).comp ((R).E e)= ((R).E e).comp ((P i).play v) := (rides_trans Y H V Q Qt j strict C f (α:=i) v e).symm
noncomputable def peninsula : OS.Semigroup (fort Y H V Q Qt j strict C f) j := glass (Ξ) δ (R) (follows_road Y H V Q Qt j strict C f)
local notation "G"=> peninsula Y H V Q Qt j strict C f
lemma pane_heat {z:ℂ} (p:z∈ OS.Semigroup.inside)(x:L) : ((G).F z x:K₀).val= (R).F z x.val:= glass_room (Ξ) δ (R) (follows_road Y H V Q Qt j strict C f) p x
lemma pane_time (x:L) (t:ℝ) : ((G).edge t x:K₀).val=(R).edge t x.val:=glass_strikes (Ξ) δ (R) _ t x
lemma pane_grid (x:L) (u:Trans j) (t:marks Μ) : ((G).U (diameter (fun i:Axis=> (Function.update (0:Axis→ marks Μ) u.val t i).val)) x:K₀).val=(Π (Σ₁ u t)) (x.val:Ρ):=glass_single (Ξ) δ (R) _ x u t -- parentheses
lemma occupant_compass : doorstep Y H V Q Qt j strict C f ∈ saunters Y H V Q Qt j strict C f:=by
  refine ((S).assembled T _).mpr ?_; intro i _
  change ContinuousAt (fun p => ((P i).play p Ω)) _; have h := resides_real Y H V Q Qt j strict C f
  simp_rw [h.2 i]; exact continuousAt_const
noncomputable def vocation : fort Y H V Q Qt j strict C f := P₀ Ω
local notation "λ₀" => vocation Y H V Q Qt j strict C f
lemma vocate : (λ₀).val=Ω := (K₀).starProjection_eq_self_iff.mpr (occupant_compass Y H V Q Qt j strict C f)
lemma vocation_norm : ‖λ₀‖=1:= by change ‖((λ₀).val:Ρ)‖=1; rw [vocate,ready]
open Spectral
lemma compass_origin : ∀ t:E4,(G).unit.translation t λ₀=λ₀:= by
  apply (invariant_glass (Ξ) δ (R) _ (λ₀)).mpr; have h:= resides_real Y H V Q Qt j strict C f; -- unfold solves proof k matching
  refine ⟨fun i=>?_,fun i u=>?_⟩; · change (R).edge i (λ₀).val=(λ₀).val; rw [vocate,h.1]
  change (P i).play u (λ₀).val=(λ₀).val; rw [vocate,h.2]
lemma compass_invariant (p: Victory Y H V Q Qt strict j C f)(x:L)(t:∀ k:E4,(G).unit.translation k x=x) : ∃ z:ℂ,z • (vocation Y H V Q Qt j strict C f)=x := by
  have hx:RealJoint Y H V Q Qt j strict C f (x.val:Ρ) := (invariant_glass (Ξ) δ (R) _ x).mp t
  obtain ⟨z,u⟩:= one_real Y H V Q Qt j strict C f p hx; exact ⟨z, Subtype.ext (by change z • (λ₀).val = _; rw [vocate,u])⟩

/-- The projection is always required! In reception defined on this compass we BUY the B operators
notch and all. Not claiming composition even for *slab* operators without paying the projections. -/
noncomputable def narrowOrt (x: (driveAlgebra Y H V Q Qt j strict C)): (L).Op := (P₀).comp ((Π x).comp (K₀).subtypeL) -- result type syntax
local notation "𝕋" p:max=> narrowOrt Y H V Q Qt j strict C f p
noncomputable def land : (Tower.Field Y H s j 0 strict) →ₗ[ℂ] fort Y H V Q Qt j strict C f := (P₀).toLinearMap.comp (arriving Y H V s Q Qt j strict C f)
local notation "X" v:max=> land Y H V v Q Qt j strict C f
lemma land_amount (t:ℕ)(p:s≤t)(v:Tower.Field Y H s j 0 strict) : (X t) (Raise Y H Q.circuit j 0 strict s t p v)=(X s) v:=by change P₀ (bud _ _ _ _ _ _ _ _ _ _ _)=_; rw [flourishes]; rfl
lemma land_call (v:Tower.Field Y H s j 0 strict) : inner ℂ λ₀ ((X s) v)= response Y H V s Q Qt j strict C f ((M₁ s) v):=by change inner ℂ (λ₀:K₀) (P₀ (a₀ s v))=_; refine (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=K₀) λ₀ _).trans ?_; rw [vocate,call]
lemma scout {w:ℕ}(x:Entry Y H s j strict w)(p:0<w) : (X s) x.val=(𝕋 (E₀ s x p)) λ₀:=by
 change P₀ (a₀ s (x.val))= P₀ ((Π (E₀ s x p)) (λ₀).val); rw [vocate,turns Y H V s Q Qt j strict C f x p,arrive_vec]
lemma reception (x:driveAlgebra Y H V Q Qt j strict C) : inner ℂ λ₀ ((𝕋 x) λ₀)= Φ x:=by
 change inner ℂ (λ₀:K₀) (P₀ ((Π x) (λ₀).val)) = _; refine (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=K₀) λ₀ _).trans ?_; rw [vocate,← arrive_vec,arrive_mean]
lemma peninsula_window (x y : Tower.Field Y H s j 0 strict) (u:Axis→ℝ): scene Y H V s Q Qt j strict C f x y u= inner ℂ ((X s) x) ((G).E (u j).toNNReal ((G).U (diameter u) ((X s) y))):= glass_window (Ξ) δ (R) rfl _ (a₀ s x) (a₀ s y) u -- args
lemma shore_dense (C:Arena Y H Q.circuit j 0 false)(f : (displayAlgebra Y H V Q Qt j false C)→⋆ₐ[ℂ]ℂ) : Dense (⋃ s:ℕ, range (fun x:Tower.Field Y H s j 0 true=> land Y H V s Q Qt j false C f (admit Y H s j x))) := by
 let R' := (saunters Y H V Q Qt j false C f); let F:= R'.orthogonalProjectionOnto
 have hx:= reserved_actor Y H V Q Qt j C f
 have he : Function.Surjective F := fun x=> ⟨x.val,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
 apply (he.denseRange.dense_image F.continuous hx).mono; rintro _ ⟨x,h,rfl⟩
 obtain ⟨s,h⟩:= Set.mem_iUnion.mp h; obtain ⟨f,rfl⟩:= h; exact Set.mem_iUnion.mpr ⟨s,f,rfl⟩

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.land_call
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.compass_invariant
