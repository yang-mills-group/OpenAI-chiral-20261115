import YM.SU5.Selected.Countable
import YM.SU5.Selected.Axes
import YM.SU5.Selected.Panes
import YM.SU5.Selected.Criterion
/-!
# Pay the criterion and select characters on the FULL drive algebra of a Satin history

Still in the resolution and discrete spatial mesh OS semantics. Exactly our trajectory
used. No older estimates invoked on a different one. Keep *all* distinct axes in this one
probability integral; on each, real structure and weights are actually identified, not
claimed on intersection of measures from separate constructions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 480000
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
open TopologicalSpace OS.Ground SelectionAnalysis
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "ℛ" => groundRoom Y H V Q j strict C
local notation "R" => Aurora Y H V Q j strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "Ω" => seat0 Y H V Q j strict C
local notation "ω" => floorV Y H Q.circuit j 0 strict C
local notation "Λ₀" => timeMesh Λ
local notation "τ" x:max => advance Y H V Q.circuit j 0 strict C x
local notation "v₀" s:max n:max => whenly (timeMesh Λ) s n
local notation "U" x:max => ((ladder Y H V Q.circuit j 0 strict C).crew x).play

abbrev PinMark (j : Axis) := (ℕ × ℕ) ⊕ (Trans j × ℕ × ℤ)
def travelAt (x : PinMark j) : driveAlgebra Y H V Q Qt j strict C :=
  match x with
  | .inl (u,v) => heatStamp Y H V u Q Qt j strict C v
  | .inr (x,s,d) => shiftStamp Y H V Q Qt j strict C x (notch Λ₀ s d)

def rolodex (j : Axis) : ℕ → PinMark j := (exists_surjective_nat (PinMark j)).choose
lemma tours (j : Axis) : Surjective (rolodex j) := (exists_surjective_nat (PinMark j)).choose_spec

def traveller : ℕ → driveAlgebra Y H V Q Qt j strict C :=
  travelAt Y H V Q Qt j strict C ∘ rolodex j
local notation "T" => travelAt Y H V Q Qt j strict C
local notation "b₀" => traveller Y H V Q Qt j strict C
local notation "𝕋" => reduceToDisplay Y H V Q Qt j strict C

lemma travellers (n) : ‖b₀ n‖ ≤ 1 := by
  cases p:rolodex j n with
  | inl x => rw [traveller,comp_apply,p]; exact advance_small Y H V Q.circuit j 0 strict C _
  | inr x =>
    rw [traveller,comp_apply,p]; change ‖(U x.1) (notch Λ₀ x.2.1 x.2.2)‖ ≤ _
    rw [on_ladder]; exact sailV_small ..
lemma in_flight {x : (A)} : (∀ i, (b₀ i).val x=x) ↔ x ∈ R := by
  rw [Aurora, Submodule.mem_iInf]; constructor
  · intro p
    have he (b:PinMark j) : (T b).val x=x := by obtain ⟨n,rfl⟩ := tours j b; exact p n
    intro i; rw [formal]
    have hv : Dense (times Λ₀) := fills _
    refine ⟨?_,?_⟩
    · suffices V : (fun a : ℝ≥0 => (τ a) x)=fun _ : ℝ≥0 => x from congr_fun V
      apply hv.denseRange_val.equalizer (advance_strong Y H V Q.circuit j 0 strict C x).continuous continuous_const; funext s
      obtain ⟨s,y,hy⟩ := (show ∃ s n, whenly Λ₀ s n=_ from s.property) -- shadow s
      dsimp only [Function.comp_apply]; rw [←hy]; exact he (.inl (s,y))
    intro a z; rw [← on_ladder Y H V i Q.circuit j 0 strict C a z]; exact he (.inr (a,i,z))
  intro p n; cases t:rolodex j n with
  | inl y => rw [traveller,comp_apply,t]; exact ((formal Y H V y.1 Q j strict C _).1 (p y.1)).1 _
  | inr y =>
    rw [traveller,comp_apply,t]; change (U y.1) _ x=x; rw [on_ladder]; exact ((formal Y H V _ Q j strict C _).1 (p y.2.1)).2 ..

lemma voyages : joint (b₀) (𝔅).subtype = R := by
  ext x; exact (mem_joint b₀ (travellers Y H V Q Qt j strict C) (𝔅).subtype x).trans (in_flight Y H V Q Qt j strict C)
lemma reduces_stamps (n): 𝕋 (b₀ n) = 1 := by
  apply Subtype.ext; ext1 v; change (R).orthogonalProjectionOnto ((b₀ n).val (v.val:A))=v
  rw [(in_flight Y H V Q Qt j strict C).2 v.property n]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v

variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
-- send through a fixed character in the SAME state.
def atCharacter : (driveAlgebra Y H V Q Qt j strict C) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (f.toAlgHom.toLinearMap.comp (𝕋).toLinearMap)
    fun _ p => _root_.map_nonneg f (reduce_nonneg Y H V Q Qt j strict C p)
local notation "e" f:max => atCharacter Y H V Q Qt j strict C f
lemma setup (x:𝔅) : (e f) x=f (𝕋 x) := rfl
lemma setupState : VacuumState (e f) b₀ :=
  ⟨by rw [setup,reduce_origin,map_one], fun i => by rw [setup,reduces_stamps,map_one]⟩

variable (j' : Axis) (C' : Arena Y H Q.circuit j' 0 strict)
local notation "𝔄'" => displayAlgebra Y H V Q Qt j' strict C'
noncomputable def displacement : (displayAlgebra Y H V Q Qt j' strict C') →⋆ₐ[ℂ] ℂ :=
  f.comp (adjustment Y H V Q Qt j' strict C' j C).toStarAlgHom

open Measure
abbrev Panel := Panes (displayAlgebra Y H V Q Qt j strict C)
abbrev Issued (P : Panel Y H V Q Qt j strict C) := Panes.Shines (groundRoom Y H V Q j strict C) (displayAlgebra Y H V Q Qt j strict C).subtype (seat0 Y H V Q j strict C) P
lemma display_receives : ∃ P : Panel Y H V Q Qt j strict C, Issued Y H V Q Qt j strict C P := by
  haveI := display_separable Y H V Q Qt j strict C
  haveI : Nonempty (↥𝔄) := ⟨1⟩
  obtain ⟨x,h⟩ := exists_dense_seq (↥𝔄)
  exact representation (ℛ) (𝔄).subtype (Ω) (norm_one_vac Y H V Q j strict C) x h fun i p => display_faithful Y H V Q Qt j strict C p
lemma transported (P : Panel Y H V Q Qt j strict C) (h : Issued Y H V Q Qt j strict C P) :
    Issued Y H V Q Qt j' strict C' (Panes.adjust P (adjustment Y H V Q Qt j' strict C' j C)) :=
  Panes.Shines.adjusted h _ fun x => adjust_mean Y H V Q Qt j' strict C' j C x

variable (P : Panel Y H V Q Qt j strict C) (h : Issued Y H V Q Qt j strict C P)
include P h
local notation "ϕ" => (fun i : P.X => e (P.character i))
lemma shone (x:𝔅) : (∫ i, ϕ i x ∂P.μ)=inner ℂ ω (x.val ω) := (h.ground (𝕋 x)).trans (reduce_mean Y H V Q Qt j strict C x)
lemma reflected_price (x:𝔅) :
    (∫ i, ‖ϕ i x‖^2 ∂P.μ)=‖(joint b₀ (𝔅).subtype).starProjection (x.val ω)‖^2 := by
  let P' := joint b₀ (𝔅).subtype
  have he : (R).starProjection=P'.starProjection := eqproj (show R=P' from (voyages Y H V Q Qt j strict C).symm)
  refine Eq.trans (Panes.Shines.energyMatch («A»:= (displayAlgebra Y H V Q Qt j strict C)) h (𝕋 x)) ?_
  change ‖(R).starProjection (x.val ω)‖^2=‖P'.starProjection (x.val ω)‖^2
  rw [he]
where
 eqproj {X : Hilbert} {A' B' : Submodule ℂ X} [A'.HasOrthogonalProjection]
   [B'.HasOrthogonalProjection] (h : A'=B') : A'.starProjection=B'.starProjection := by subst B'; rfl

/-- Here single means on the joint stamps, one GNS based on the **whole limiting local
slab operators and norms** (not just separate slice algebras). -/
lemma almost : ∀ᵐ x ∂P.μ, SingleGround (ϕ x) b₀ := by
  haveI := h.normalized
  haveI := drive_separable Y H V Q Qt j strict C
  apply rank_one_almost_everywhere P.μ ϕ b₀ (travellers Y H V Q Qt j strict C)
    (𝔅).subtype ω (fun i => setupState Y H V Q Qt j strict C _)
    (fun x => h.weak (𝕋 x)) (shone Y H V Q Qt j strict C P h) (reflected_price Y H V Q Qt j strict C P h)

abbrev Victory (j : Axis)(C : Arena Y H Q.circuit j 0 strict)
    (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ) :=
  SingleGround (atCharacter Y H V Q Qt j strict C f) (traveller Y H V Q Qt j strict C) ∧
  ExtremeVacuum (atCharacter Y H V Q Qt j strict C f) (traveller Y H V Q Qt j strict C) -- includes vacuum
lemma full_house (c : ∀ j, Arena Y H Q.circuit j 0 strict) :
    ∀ᵐ x ∂P.μ, Victory Y H V Q Qt strict j C (P.character x) ∧ ∀ k : Axis,
      Victory Y H V Q Qt strict k (c k) (displacement Y H V Q Qt j strict C (P.character x) k (c k)) := by
  have hx (k:Axis) := almost Y H V Q Qt k strict (c k) _ (transported Y H V Q Qt j strict C k (c k) P h)
  have he (k:Axis) : ∀ᵐ x ∂P.μ, SingleGround (atCharacter Y H V Q Qt k strict (c k) (displacement Y H V Q Qt j strict C (P.character x) k (c k))) (traveller Y H V Q Qt k strict (c k)) := hx k
  filter_upwards [ae_all_iff.mpr he, almost Y H V Q Qt j strict C P h] with x hx hv
  exact ⟨⟨hv,single_is_extreme _ _ (travellers Y H V Q Qt j strict C) (setupState Y H V Q Qt j strict C _) hv⟩,
    fun k => ⟨hx k,single_is_extreme _ _ (travellers Y H V Q Qt k strict (c k)) (setupState Y H V Q Qt k strict (c k) _) (hx k)⟩⟩

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.almost
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.full_house
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.display_receives
