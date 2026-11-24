import YM.SU5.Selected.Cylinder
import YM.SU5.Selected.Networks
/-!
# Use operator assembly on the chosen line; separability after a single refinement

AT EACH level and reading support. The sets of Marks and even of narrow neutral
plus bounded Borel neutral marks with a common norm bound are not assumed separable in a sup topology.
This step is crucial for paying countably many (a.e.) spectral prices for all local arguments.
It is specific to Coherent, not bought with an abstract RP certificate or Gram space.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 310000
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
open TopologicalSpace
open Tapestry
variable (S : Finset Cover)
local notation "W" => wingspan Λ l S
local notation "U" => Swatch S

-- single bang in the Coherent system - do not use a different `Exhibition` reader's limiting operator
noncomputable def renovate : Swatch S →ₗ[ℂ] Swatch (wingspan Λ l S) where
  toFun f := fabric W K (Q.circuit.supports s (texture S K f)).1
  map_add' x y := by
    apply render_inj W K; rw [map_add (render W K),render_fabric,render_fabric,render_fabric, map_add]
    exact Q.circuit.plus_lift _ (aux_test (texture S K x)) (aux_test (texture S K y))
  map_smul' z x := by
    apply render_inj W K
    change render W K (fabric W K ((Q.circuit.supports s (texture S K (z • x))).1)) = render W K (z • fabric W K ((Q.circuit.supports s (texture S K x)).1)) -- too many args
    rw [map_smul (render W K),render_fabric,render_fabric,map_smul]
    exact Q.circuit.amp _ (aux_test (texture S K x)) _
local notation "g" => renovate Y H s Q S
lemma renovate_eq (x : U) : render W K (g x)=D s (render S K x) := render_fabric W K (Q.circuit.supports s (texture S K x)).1
include V in
lemma single_bill (t : Evens S) :
    TotallyBounded (g '' ((fun i : Purse S => fabric S K (atoms_test Y H S t i)) ''
      {i : Purse S | ∀ x, ‖i.val x‖ ≤ 1})) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε h
  let G (i' : Purse S) := g (fabric S K (atoms_test Y H S t i'))
  let d : ℝ := Fintype.card (Evens W)
  have hd : 0 ≤ d := by unfold d; positivity
  let δ := ε/(d+1)
  have e : 0 < δ := div_pos h (by linarith)
  obtain ⟨X,p⟩ := finance_inputs Y H s S t δ e
  refine ⟨G '' (X : Set _), (X.finite_toSet).image G,?_⟩
  rintro _ ⟨-,⟨x,hx,rfl⟩,rfl⟩
  obtain ⟨y,k',hy⟩ := p x hx
  refine mem_iUnion.mpr ⟨G y, mem_iUnion.mpr ⟨ Set.mem_image_of_mem G k', ?_⟩⟩
  let A (x' : Purse S) := note K x'.val (tagWord S t.val)
  let z := A x - A y
  have Hx : InTest K true S false (A x) := atoms_test ..
  have Hy : InTest K true S false (A y) := atoms_test ..
  have Hz : InTest K true S false z := InTest.subOp Hx Hy
  let B' n := block Y H s (i (a n)) (k (b n)) S
  have F : ∀ᶠ n in atTop, pay (B' n z) (d*δ) := by
    have ht' := ((V.pick.grow_i.comp Q.growsA).tendsto_atTop.eventually (admit_event Y H s S))
    filter_upwards [Q.finance (s+1), ht'] with n q u
    apply Tower.banner_rate W K (booked Y H s ..)
    intro v Z; unfold z
    rw [sub_scheme Y H s (i (a n)) (k (b n)) Hx Hy, Tower.banner_sub W K (booked ..) (booked ..), ← dist_eq_norm]
    exact hy (i (a n)) (k (b n)) ⟨q.depth,q.enters⟩ u.1 u.2 v Z
  obtain ⟨m,Hm⟩ := (Buffered.separates K W).exists
  obtain ⟨l',hl⟩ := Journey.valuation Y H Hz
  have hl' : pay z l' := hl; have hl'' := pay_nonneg hl'
  change dist (G x) (G y)<ε
  rw [dist_eq_norm]; apply lt_of_le_of_lt (b := d*δ+δ/2) ?_ (by
    have ht : δ*(d+1)=ε := div_mul_cancel₀ _ (by positivity)
    linarith)
  apply sampling W K m ⟨Hm⟩
  intro v
  have Δ : 0 < δ/(2*(l'+1)) := div_pos e (by positivity)
  obtain ⟨C₀,p₀,e₀⟩ := Q.implements s S
  obtain ⟨n,Hn,gz⟩ := (F.and (e₀ _ Δ)).exists
  rw [← appearRender, map_sub]; unfold G
  rw [renovate_eq, renovate_eq,render_fabric,render_fabric]
  have he : D s z=D s (A x)-D s (A y) := D_sub Y H Q (aux_test Hx) (aux_test Hy)
  change ‖(D s (A x)-D s (A y)) m v‖ ≤ _; rw [←he]
  let f₁ := B' n z m v; let f₂ := D s z m v
  have hp₁ : ‖f₁‖≤d*δ := Hn m v
  have hp₂ : ‖f₁-f₂‖≤ (δ/(2*(l'+1)))*l' := (gz z Hz _ hl').2.2.1 m v
  change ‖f₂‖ ≤ _; rw [norm_sub_rev] at hp₂
  have hQ : δ/(2*(l'+1))*(2*(l'+1))=δ := div_mul_cancel₀ _ (by positivity)
  nlinarith only [Δ,hQ,norm_sub_norm_le f₂ f₁,hp₁,hp₂]

-- why separable is enough for now. exploit spanning, no extra 'equicontinuous estimator' system.
include V
theorem venue_separable : IsSeparable (Set.range (renovate Y H s Q S)) := by
  let G (t : Evens S) (x : Purse S) := fabric S K (atoms_test Y H S t x)
  let B t := (G t) '' {i : Purse S | ∀ x, ‖i.val x‖ ≤ 1}
  let X := ⋃ t:Evens S,g '' B t
  have Xh := (show IsSeparable X from IsSeparable.iUnion fun i =>
    (single_bill Y H V s Q S i).isSeparable)
  let L := Submodule.span ℂ X
  have h (t : Evens S) (z : Purse S) : g (G t z) ∈ L := by
    obtain ⟨C,k⟩ := z.property.env.cost
    have hp : 0 < C+1 := by
      have k := (norm_nonneg _).trans (k (1,1))
      linarith
    let a := (((C+1:ℝ):ℂ)⁻¹)
    have ha : ‖a‖=(C+1)⁻¹ := by unfold a; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hp.le]
    let y : Purse S := Satin.hue S z a
    have hf : G t y=a • G t z := by
      apply render_inj S K
      rw [map_smul]; exact (render_fabric S K (atoms_test Y H S t y)).trans ((swindle S K z _ (bracketV ..) a).symm.trans (congrArg (a • ·) (render_fabric S K (atoms_test Y H S t z)).symm))
    have he : G t y ∈ B t := by
      refine ⟨y,fun x => ?_,rfl⟩
      change ‖a • z.val x‖ ≤ _; rw [norm_smul,ha]; apply le_trans (mul_le_mul_of_nonneg_left ((k x).trans (by linarith : C ≤ C+1)) (by positivity))
      rw [inv_mul_cancel₀ hp.ne']
    have hG : g (G t y)∈L := Submodule.subset_span (Set.mem_iUnion.mpr ⟨t,Set.mem_image_of_mem g he⟩)
    rw [hf,map_smul] at hG; exact (L.smul_mem_iff (show a≠0 from by unfold a; exact inv_ne_zero (by exact_mod_cast hp.ne'))).1 hG -- tune
  apply (Xh.span (R:=ℂ)).mono
  rintro _ ⟨x,rfl⟩; let T := render S K x; let v (i:Evens S) : Purse S := ⟨_,Tower.banner_paid S K T i⟩
  have hp : x=∑ i:Evens S, G i (v i) := by
    apply render_inj S K; rw [map_sum]; simp_rw [G,render_fabric]; exact Tower.banner_pays S K (texture S K x)
  -- note v depends x; avoid dependent rewrite.
  change g x ∈ L; rw [hp,map_sum]; exact L.sum_mem fun i _ => h i _

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.venue_separable
