import YM.SU5.MacroSix.Smear
/-!
# Reflections, footprints and qualification of the actual smeared probes

`scenery` uses gauge coordinates as in Drape; `doubledBudget` below retains
that convention so that the actual stencil-payment checks (`keep`, `printedHere`, ...)
apply. Test smears use fermion units (same as `realWidth` and the translation/spectral price).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open _root_.YM.MacroSix

namespace Spine
variable (P : Spine) (s n t : ℕ) (Z Z' : Window.Family) (f g : Vantage → ℝ)
  (x : P.Spectrum0 3) (A : P.Apron) (j : Axis)
local notation "M" => timeMesh P.par
local notation "w" => P.sixWidth s n
local notation "D" i:max => P.sixBody s n i
local notation "B" i:max => (P.sixBody s n i).kiss P 3
local notation "Δ" => P.fieldAt t A
local notation "μ" => P.singleState 3 t x
local notation "π" => P.pose t

lemma pose_mirror (y : Cover) : π (mirrorΩ j y) = mirrorΩ j (π y) := by
  rw [pose_place,P.pose_place]
  funext i; by_cases h : i=j <;> simp [mirrorΩ,h, MacroSix.Grid.place]

lemma reflect_move (L : List Axis) (y : Cover) (f : P.Test) : P.reflectTest j (P.cruise L y f) =
    P.cruise L (mirrorΩ j y) (P.reflectTest j f) := by
  induction L with
  | nil => rfl
  | cons i l ih =>
    rw [P.cruise_step,P.cruise_step,AlgHom.comp_apply,AlgHom.comp_apply,← ih]
    by_cases h : i=j
    · subst i; rw [mirrorΩ,if_pos rfl]; exact P.meetOwn ..
    rw [mirrorΩ,if_neg h]; exact (P.meetrefl i j _ _ h).symm

lemma reflect_fieldAt (y : Cover) : P.fieldAt t (A.kiss P j) (mirrorΩ j y)=
    P.reflectTest j (P.fieldAt t A y) := by
  unfold fieldAt chartAll; rw [P.reflect_move, Apron.full_exchange]

lemma mirrorInvol {H : Type*} [AddCommGroup H] (p : Axis → H) : mirrorΩ j (mirrorΩ j p)=p := by
  funext i; by_cases h : i=j <;> simp [mirrorΩ,h]

lemma mirrorMeasurable (j : Axis) : MeasurePreserving (mirrorΩ (A:=ℝ) j) := by
  let g (i : Axis) := if i=j then fun x : ℝ ↦ -x else id
  have ht (i : Axis) : MeasurePreserving (g i) := by
    unfold g; split
    · exact Measure.measurePreserving_neg (volume:Measure ℝ)
    exact MeasurePreserving.id volume
  have he : mirrorΩ (A:=ℝ) j = fun (a : Axis → ℝ) i ↦ g i (a i) := by
    funext a i; by_cases h : i=j <;> simp [g,mirrorΩ,h]
  rw [he]; exact volume_preserving_pi (α':=fun _ ↦ ℝ) (β':=fun _ ↦ ℝ) ht

def mirrorHome (j : Axis) : Vantage ≃ₜ Vantage :=
  ⟨Involutive.toPerm (fun (x : Vantage) ↦ mirrorΩ j x) (mirrorInvol j), mirrorPose j, mirrorPose j⟩

lemma throughMirror :
    tsupport (f ∘ mirrorΩ j) = mirrorΩ j ⁻¹' (tsupport f) :=
  tsupport_comp_eq_preimage f (mirrorHome j)

lemma mirrorSmooth (p : SmoothDensity f) : SmoothDensity (f ∘ mirrorΩ j) := by
  have he := mirrorMeasurable j
  refine ⟨p.smooth.comp ?_,p.compact.comp_homeomorph (mirrorHome j),fun i ↦ p.nonneg _,
    (he.integral_comp (mirrorHome j).toMeasurableEquiv.measurableEmbedding _).trans p.mass⟩
  rw [contDiff_pi]
  intro i; unfold mirrorΩ; by_cases h : i=j <;> simp only [h,↓reduceIte]
  · exact (contDiff_apply ℝ ℝ _).neg
  exact contDiff_apply ℝ ℝ _

lemma pose_finite (h : HasCompactSupport f) : (Function.support (f ∘ π)).Finite :=
  P.gridCosts_finite t ℝ f h

lemma reflect_smearField (h : HasCompactSupport f) : P.reflectTest j (P.smearField t f A)=
    P.smearField t (f ∘ mirrorΩ j) (A.kiss P j) := by
  let τ (i : Cover) := (f (π i):ℂ) • Δ i
  let p (i : Cover) := P.fieldAt t (A.kiss P j) i
  have he : HasFiniteSupport τ := (P.pose_finite t f h).subset (by
    intro i u q
    have hp : f (P.pose t i) = 0 := q
    exact u (by change (f (P.pose t i):ℂ) • _ = _; rw [hp,Complex.ofReal_zero,zero_smul]))
  let R := P.reflectTest j
  let c : ℝ := (P.meshSize t)^4
  change R ((c:ℂ) • ∑ᶠ i, τ i)= (c:ℂ) • ∑ᶠ i, (f (mirrorΩ j (π i)):ℂ) • p i
  rw [map_smulₛₗ,Complex.conj_ofReal,map_finsum _ he]
  apply congrArg; refine finsum_eq_of_bijective (mirrorΩ j) (Involutive.bijective
    (mirrorInvol j (H:=ℤ))) (fun i ↦ ?_)
  have hu : R (Δ i) = p (mirrorΩ j i) := (P.reflect_fieldAt t A j i).symm
  change R (τ i)= (f (mirrorΩ j (π (mirrorΩ j i))):ℂ) • p _
  unfold τ; rw [P.pose_mirror, mirrorInvol,map_smulₛₗ,Complex.conj_ofReal,hu]

-- Single-height location. (Can convert directly to `keep` on any bounded open containing this price.)
def doubledBudget : Set RSpace := {z | ∃ x ∈ tsupport f, z∈ A.scenery P x}

lemma doubledBudget_compact (h : HasCompactSupport f) : IsCompact (P.doubledBudget f A) := by
  let Y : Vantage × RSpace → RSpace := fun v ↦ (2:ℝ) • v.1 + v.2
  let u := A.scenery P 0
  have he : IsCompact u := P.pay_places A _
  have hY : Continuous Y := by unfold Y; fun_prop
  have hp : P.doubledBudget f A= Y '' ((tsupport f) ×ˢ u) := by
    ext x
    constructor
    · rintro ⟨y,p,q⟩; refine ⟨(y,x - (2:ℝ) • y),⟨p,?_⟩,?_⟩
      · intro j; simpa [smul_eq_mul] using q j -- tuning
      change (2:ℝ) • y + (x - (2:ℝ) • y) = x; rw [add_comm]; exact sub_add_cancel x ((2:ℝ) • y)
    rintro ⟨⟨x,y⟩,⟨p,q⟩,rfl⟩
    refine ⟨x,p,fun j ↦ ?_⟩
    have he := q j
    change |(2:ℝ)*x j+y j-2*x j| ≤ _
    simp only [add_comm,add_sub_cancel_right]
    exact (by simpa using he)
  rw [hp]; exact (IsCompact.prod h he).image hY

lemma smear_locates (K : P.Register) (u : A.s ≤ t) (h : HasCompactSupport f) :
    P.smearField t f A ∈ keep P.par P.width t P.calibration true (P.doubledBudget f A) ∧
      P.smearField t f A ∈ enclave P.calibration := by
  have he : ∀ (i : Cover), i ∈ Function.support (f ∘ π) →
      A.scenery P (π i) ⊆ P.doubledBudget f A := fun i e x t ↦
    ⟨π i, subset_tsupport f (show f (π i) ≠ 0 from e), t⟩
  have hv : ∀ i ∈ Function.support (f ∘ π), Δ i ∈ _ := fun i b ↦
    rooms P.par P.width t P.calibration true _ (he i b) (P.fieldAt_budget t K A i u)
  exact ⟨finiteTest_mem _ _ _ (P.pose_finite t f h) _ hv,
    finiteTest_mem _ _ _ (P.pose_finite t f h) _ (fun i _ ↦ P.fieldAt_singlet t A i)⟩

lemma smear_centered (h : HasCompactSupport f) (u : A.s ≤ t)
    (p : P.singleState 3 A.s x A.F=0) : μ (P.smearField t f A)=0 :=
  finiteTest_zero _ _ _ _ (P.pose_finite t f h) fun i _ ↦ (P.fieldAt_single t x A i u).trans p

lemma measureAt_centered (hs : s ≤ t) (h : HasCompactSupport f) (u : HasCompactSupport g) :
    μ (P.smearField t f (B Z))=0 ∧ μ (P.smearField t g (D Z'))=0 :=
  ⟨P.smear_centered t f x (B Z) h hs (P.oneMirror_centered s n Z x),
    P.smear_centered t g x (D Z') u hs (P.oneTest_centered s n Z' x)⟩

lemma OnFrame.places {P : Spine} {s n f g c}
    (u : P.OnFrame s n f g c) (Z Z' : Window.Family) :
    (P.doubledBudget f ((P.sixBody s n Z).kiss P 3) ⊆ {x | x 3 < 2*c}) ∧
    (P.doubledBudget g (P.sixBody s n Z') ⊆ {x | 2*c < x 3}) := by
  constructor
  · rintro x ⟨y,h,p⟩; have hx := (abs_le.mp (p 3)).2
    have he : ((P.sixBody s n Z).kiss P 3).realWidth P 3=(P.sixWidth s n 3:ℝ) :=
      P.sixBody_width s n Z 3
    rw [he] at hx; exact (show x 3 < 2*c by linarith [u.before y h])
  rintro x ⟨y,h,p⟩; have hx := (abs_le.mp (p 3)).1
  rw [P.sixBody_width] at hx; exact (show 2*c < x 3 by linarith [u.after y h])

/-- Price at other projections too when the corresponding strict margins are
supplied. We'll use closed bounded rectangles with these after adding the body width. -/
lemma budgetOrder (v : ∀ y∈tsupport f, ∀ z∈tsupport g, P.fieldOrder s n j y z) :
    ∀ y ∈ P.doubledBudget f (B Z), ∀ z ∈ P.doubledBudget g (D Z'), y j < z j := by
  rintro y ⟨a,h,p⟩ z ⟨b,e,t⟩
  have hx := (abs_le.mp (p j)).2; have ht := (abs_le.mp (t j)).1
  rw [(D Z).kiss_width,P.sixBody_width] at hx; rw [P.sixBody_width] at ht
  have he := v a h b e; unfold fieldOrder at he; linarith

lemma sideBudget (i : Axis) : P.doubledBudget f (A.kiss P i)= P.doubledBudget f A := rfl

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms smear_locates
#print axioms OnFrame.places
#print axioms reflect_smearField
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
