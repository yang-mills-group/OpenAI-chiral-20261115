import YM.SU5.Selected.Room
/-!
# Local continuity in Swatch norm ($L^\infty$ actual data and fixed basis)

Raw actor on Ω uses the revenue at the single box including reflections. For continuity
**in the preparer norm**, classical trick: graph closure via strong test on just that Ω!
This works because all products $Leg^* Leg$ lie in the phase algebra where Ω separates.
Thus classical point/reconstruct artifacts need not be used. Important for upgrading selection
without assuming separability of the wide tests.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false

open Tapestry
local notation "B" => groundAlgebra Y H V Q Qc j false C
local notation "L₀" s:max => prepare Y H V Q Qc j false C s
local notation "L" => basisRoom Y H V Q j false C
local notation "J" => (↑(R) →L[ℂ] A)
local notation "P" => pipeline Y H V Q Qc j false C
variable (s : ℕ) (S : Finset Cover) (h : Tower.region j (meshface (Λ:=Λ) 0 s) (tent Y H).ℓ S)

def atomField : Swatch S →ₗ[ℂ] (F₊ s) where
  toFun x := ⟨render S K x, (show _ from (purpose_ok ..).2 ⟨(show _ from ⟨S,texture ..,h⟩),fun p => by cases p⟩)⟩
  map_add' x y := Subtype.ext (map_add (render S K) x y)
  map_smul' t x := Subtype.ext (map_smul (render S K) t x)
local notation "Φ" => atomField Y H j s S h

include V Q C h
lemma actor_sensitivity : ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Swatch S, ‖(φ s) (Φ x)‖≤c*‖x‖ := by
  let X := reflectedBox j 0 S ∪ S
  let u := toll Y H s X; let v:=spread S
  have ht:0≤u:= (toll_pays Y H s X).1
  have hx:0≤v:= by unfold v Tapestry.spread; positivity
  refine ⟨Real.sqrt u * v,by positivity,fun x=>?_⟩
  let a := (φ s) (Φ x); let f:= render S K x
  have he : pay f (v*‖x‖) := fun m p => renderLe S K m x p
  have hp := texture S K x
  have e:=E_bound Y H V s X ((axial K j 0 hp|>.mono subset_union_left).mul (hp.mono subset_union_right)) (pay_mul (pay_flips K he j 0) he)
  have H0 : ‖inner ℂ a a‖ ≤ u*(v*‖x‖*(v*‖x‖)) := by unfold a; rw [stems Y H V,area0]; exact e
  rw [inner_self_eq_norm_sq_to_K, norm_pow] at H0; change ‖((‖a‖:ℝ):ℂ)‖^2 ≤ _ at H0; simp only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at H0
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [mul_pow,Real.sq_sqrt ht]
  exact H0.trans_eq (by ring)

local notation "P₁" => (arrows Y H V Q.circuit j 0 false C s)
lemma actor_coherent : Continuous ((P₁).comp Φ) := by
  obtain ⟨c,u,e⟩ := actor_sensitivity Y H V Q j C s S h
  exact (( (P₁).comp Φ).mkContinuous c e).continuous
abbrev money := (plants Y H V Q Qc j false C s).comp Φ

-- closed graph over other parameters to avoid transparency stress
omit V Q C h
private lemma graph_pull (X Y : Hilbert) (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    (B' : StarSubalgebra ℂ X.Op)(p : IsClosed (B' : Set X.Op))(k : X)(t:∀i:B',i.val k=0→ i=0)
    (A' : Z →ₗ[ℂ] (X→L[ℂ] Y)) (h : ∀ x, (A' x).adjoint.comp (A' x)∈ B')(g:Continuous (fun x:Z=> A' x k)) :
    Continuous A' := by
  let C (i : X→L[ℂ] Y):= i.adjoint.comp i
  have hv : Continuous C := Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id -- search
  apply LinearMap.continuous_of_seq_closed_graph
  intro f i j hf hJ
  let z:= j-A' i; let w (x:ℕ):= f x-i
  have t1:Tendsto w atTop (𝓝 0):= by simpa [w] using hf.sub_const i
  have t2:Tendsto (fun n=> A' (w n)) atTop (𝓝 z):=(hJ.sub_const (A' i)).congr (fun n=>Eq.symm (map_sub A' _ _))
  have t3:Tendsto (fun n=> A' (w n) k) atTop (𝓝 (z k)):=(show Continuous (fun w : X→L[ℂ] Y=>w k) from continuous_id.clm_apply continuous_const).continuousAt.tendsto.comp t2 -- search
  let u' : B' := ⟨C z,p.mem_of_tendsto (hv.continuousAt.tendsto.comp t2) (Eventually.of_forall fun i=> h (w i))⟩
  have u:z k=0:= (tendsto_nhds_unique t3 (g.continuousAt.tendsto.comp t1)).trans (by rw [map_zero]; rfl)
  have he:C z=0:= (congrArg Subtype.val (t u' (by change z.adjoint (z k)=_; rw [u,map_zero])))
  apply sub_eq_zero.mp; ext1 x
  change z x=0
  rw [← inner_self_eq_zero (𝕜:=ℂ),←ContinuousLinearMap.adjoint_inner_left]; change inner ℂ (C z x) x= _; rw [he]; simp

include V Q C Qc h
lemma continuously : Continuous (money Y H V Q Qc j C s S h) := by
  apply graph_pull (L) (A) (Swatch S) (B) isClosed_closure Ω (fun u h=> distinguish Y H V Q Qc j false C u 0 h)
  · intro x; exact owns_each Y H V Q Qc j false C (asLeg Y H V Q Qc j false C s (Φ x)) (asLeg Y H V Q Qc j false C s (Φ x))
  change Continuous (fun z => (L₀ s) (Φ z) Ω)
  simp only [planted]
  exact actor_coherent Y H V Q j C s S h
end YM.CF.Buffered.Afterglow.Tower.Selection
#check @YM.CF.Buffered.Afterglow.Tower.Selection.atomField
#print axioms YM.CF.Buffered.Afterglow.Tower.Selection.atomField
#print axioms YM.CF.Buffered.Afterglow.Tower.Selection.continuously
