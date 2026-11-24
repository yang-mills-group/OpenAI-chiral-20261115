import YM.SU5.Selected.Appointments
import YM.SU5.Selected.SpatialCard
/-! # Regularizing and the overlap of coordinate chart pairs on the common projected data.
Apply Sunbelt to this very character, all corresponding apparatus paid.
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
noncomputable def mainsea : Sunbelt j (marks (timeMesh Λ)) (indoor Y H V Q Qt j strict C f) where
  track:=S
  list:=T
  unique_list:= look_one _
  traverses:= look_all _
  heat:= (R).E
  smooth:= (R).continuousE
  diffusion x:=by simp_rw [(R).sym]; exact (R).continuousE _

local notation "Ξ"=> mainsea Y H V Q Qt j strict C f
local notation "δ"=> daylight Μ
noncomputable def scene (x y : Tower.Field Y H s j 0 strict) := (Ξ).curtain (daylight Μ) (a₀ s x) (a₀ s y)
lemma scene_cont (x y : Tower.Field Y H s j 0 strict) : Continuous (scene Y H V s Q Qt j strict C f x y) := curtain_cont (Ξ) (δ) ..
lemma scene_on_mesh (x y : Tower.Field Y H s j 0 strict) (u : placement Λ) :
    scene Y H V s Q Qt j strict C f x y (fun i=> (u i:ℝ))= (Ξ).playback (a₀ s x) (a₀ s y) u (look j) := ((Ξ).curtain_eq δ (a₀ s x) (a₀ s y) u).symm
lemma scene_empty (x y : Tower.Field Y H s j 0 strict) (u : placement Λ) : Visits Y H V s Q Qt j strict C f x y u=(Ξ).playback (a₀ s x) (a₀ s y) u []:=rfl
variable {a' : Axis} {C' : Arena Y H Q.circuit a' 0 strict}
  {f' : (displayAlgebra Y H V Q Qt a' strict C') →⋆ₐ[ℂ] ℂ}
  {x y : Tower.Field Y H s j 0 strict} {x' y' : Tower.Field Y H s a' 0 strict}
lemma cohesion (p : Duality Y H V s Q Qt j strict C f C' f' x y x' y') :
    Sunbelt.Links (mainsea Y H V Q Qt j strict C f) (arriving Y H V s Q Qt j strict C f x) (arriving Y H V s Q Qt j strict C f y)
        (mainsea Y H V Q Qt a' strict C' f') (arriving Y H V s Q Qt a' strict C' f' x') (arriving Y H V s Q Qt a' strict C' f' y') [] [] := fun u=> Duality.compare Y H V s Q Qt j strict C f C' f' x y x' y' p u -- many args `..` syntax
lemma keeps_scene (p : Duality Y H V s Q Qt j strict C f C' f' x y x' y') (e:j≠ a') (u:Axis→ℝ) (xU:0≤u j)(yU:0≤u a') : scene Y H V s Q Qt j strict C f x y u=scene Y H V s Q Qt a' strict C' f' x' y' u:=
    Sunbelt.links_match (Ξ) δ _ _ _ _ _ e (cohesion Y H V s Q Qt j strict C f p) u xU yU
lemma scene_revival (x y : Tower.Field Y H s j 0 strict) (p : ∀ (k:Axis)(g:k≠j),∃ (C' : Arena Y H Q.circuit k 0 strict)
    (f' : (displayAlgebra Y H V Q Qt k strict C') →⋆ₐ[ℂ] ℂ)
    (x' y' : Tower.Field Y H s k 0 strict), Duality Y H V s Q Qt j strict C f C' f' x y x' y') (u:placement Λ) (h:∀i,uptown i u):
    scene Y H V s Q Qt j strict C f x y (fun i=> (u i:ℝ))=Visits Y H V s Q Qt j strict C f x y u:=by
  rw [scene_on_mesh,scene_empty]
  refine playback_all (Ξ) δ (a₀ s x) (a₀ s y) _ u h ?_
  rintro ⟨k,g⟩ _ v w
  obtain ⟨C',f',x',y',z⟩ := p k g
  exact Sunbelt.Links.window (Ξ) _ _ _ _ _ (cohesion Y H V s Q Qt j strict C f z) g v (w j)
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.scene_revival
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.keeps_scene
