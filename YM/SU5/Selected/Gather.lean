import YM.SU5.Selected.Recolor
import YM.SU5.Selected.SeparableOrbit
/-!
# Determining Color, part I: The average can be bought in supported Swatch at next level

Compact gauge finishes on this very physical algebra; given any Borel mark no need
for questionable Bochner integral into its original Swatch. Instead refine *as
gauge-covariantly paid* first. Use separability of the refiners and then Lusin-Souslin.
In particular the colored representatives in the *costed system itself* form a measurable
evaluation of all needed actors, before passing a character through them, at next level. For
continuous-coefficient marks can also average without refining.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 300000
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
open Tapestry _root_.YM.SelectionAnalysis TopologicalSpace CF.Pannier.Chancel
variable (S : Finset Cover) (m : Side)
section veil
variable (J : Calibration) (p : Hosp S (J.c m))
local notation "Q₀" => Swatch S


local notation "N" => J.c m
local notation "T" => Zodiac (N)
local notation "W" x:max => render S J x

noncomputable def coup (u : Zodiac (J.c m)) : Swatch S →L[ℂ] Swatch S := ocelli J S (u ∘ wrap _)
local notation "K'" u:max => coup S m J u
lemma coup_local (u : T) (x : Q₀) : Circular S (u ∘ wrap _) (render S J x) (render S J ((K' u) x)) := decorates J S _ _
lemma coup_trace (u : T) (x : Q₀) : Harmony u (render S J x m) (render S J ((K' u) x) m) :=
  coup_local S m J u x m u (fun _ _=> rfl)
lemma coup_agrees (u : T) (x : Q₀) (y : Fields N) : render S J ((K' u) x) m y=getBack (render S J x m) u y := by
  exact (twist (quantU (tradew N u))).injective ((coup_trace S m J u x y).symm.trans (trueBack (render S J x m) u y))
include p in
lemma coup_times (x : Q₀) (u v : T) : (K' u) ((K' v) x)=(K' (v*u)) x := by
  apply Tapestry.appear_inj S J m p
  funext a; change render S J _ m a=render S J _ m a; rw [coup_agrees,coup_agrees,
    show render S J ((K' v) x) m = getBack (render S J x m) v from funext (coup_agrees S m J v x),Back_consistency]

-- measurability of orbit evaluations, ALL marks incl discontinuous regulators
open Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
private lemma replete (y:Fields N) (F : Mark N) (p : Measurable F) : Measurable (fun v : T => getBack F v y) := by
  let g (v:T) := simultaneous v y
  let z(v:T) : FC (Single N) := (quantU (tradew N v)).val
  have hc : Continuous g := by
    apply Continuous.prodMk (f:=fun v:T=> Lattice.gauge v y.1) (g:=fun v:T=>Lattice.gauge v y.2) <;>
      apply continuous_pi <;> intro i <;> unfold Lattice.gauge <;> fun_prop
  have ht : Continuous z := quant_cont.comp (CF.Pannier.Chancel.trade_cont N) -- tune
  rw [show (fun v:T=> getBack F v y)=(fun v:T=> star (z v) * F (g v) * star (star (z v))) from funext fun v=> twist_formula ..]
  exact ((ht.star.measurable).mul (p.comp hc.measurable)).mul ht.star.star.measurable
include p
lemma coup_measures (x : Q₀) (h : IsSeparable (Set.range (fun u : Zodiac (J.c m) => coup S m J u x))) :
    StronglyMeasurable (fun u : Zodiac (J.c m)=> coup S m J u x) := by
  let f (u:T) := (K' u) x
  let v (t : Fields N) (x : Q₀) := render S J x m t
  have he (x y : Q₀) (h:∀ z,v z x=v z y) : x=y := Tapestry.appear_inj S J m p (funext h)
  apply measurable_evaluated (f) h v (fun i => render_cont S J m i) he
  intro z
  rw [show v z ∘ f=(fun u=>getBack (render S J x m) u z) from funext fun u => coup_agrees S m J u x z]
  exact replete m J z _ (((texture S J x).support m).env.meas)
lemma coup_pays (x : Q₀) (h : IsSeparable (Set.range (fun u : Zodiac (J.c m) => coup S m J u x))) :
    Integrable (fun u : Zodiac (J.c m)=> coup S m J u x) (domeLaw (J.c m)) := by
  apply Integrable.of_bound (C:=spread S * ‖x‖) (coup_measures S m J p x h |>.aestronglyMeasurable)
  apply ae_of_all _; intro u
  apply sampling S J m p; intro v; rw [←appearRender,coup_agrees]; unfold getBack; rw [twist_norm]
  exact renderLe ..

lemma coup_smooth (x : Q₀) (h : Continuous (render S J x m)) : Continuous (fun u : Zodiac (J.c m)=> coup S m J u x) := by
  let X(u:T) : C(Fields N, FC (Single N)) :=
    ⟨getBack (render S J x m) u, (costsBack (render S J x m) h).comp (f:=fun i:Fields N=> (u,i)) ((continuous_const (y:=u)).prodMk continuous_id)⟩
  have hX : Continuous X := ContinuousMap.continuous_of_continuous_uncurry X (costsBack (render S J x m) h)
  apply continuous_iff_continuousAt.mpr; intro u; apply Metric.tendsto_nhds.mpr; intro ε e
  filter_upwards [Metric.tendsto_nhds.mp (hX.tendsto u) ε e] with i hi
  refine lt_of_le_of_lt ?_ hi
  rw [dist_eq_norm,dist_eq_norm]
  apply sampling S J m p; intro v; let k(v:Q₀):= render S J v m
  rw [← appearRender,map_sub]; change ‖render S J ((K' i) x) m v -render S J ((K' u) x) m v‖ ≤ _
  rw [coup_agrees,coup_agrees]; exact (X i-X u).norm_coe_le_norm v
lemma coup_smooth_price (x : Q₀) (h : Continuous (render S J x m)) : Integrable (fun u : Zodiac (J.c m)=> coup S m J u x) (domeLaw (J.c m)) :=
  (coup_smooth S m J p x h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit p
/-- Haar representative of the given local input, if integrable in Swatch itself. -/
noncomputable def sigil (x : Swatch S) : Swatch S := ∫ u:Zodiac (J.c m),coup S m J u x∂ domeLaw (J.c m)
local notation "M" => sigil S m J
lemma sigil_pennant (f : Q₀) (u : T) (h : Integrable (fun u=> coup S m J u f) (domeLaw (J.c m))) (p : Hosp S N) :
    coup S m J u (sigil S m J f)=sigil S m J f := by
  refine (ContinuousLinearMap.integral_comp_comm (E:=Swatch S) (Fₗ:=Swatch S) (𝕜:=ℂ) (K' u) h).symm.trans ?_
  unfold sigil
  simp_rw [coup_times S m J p]
  exact integral_mul_right_eq_self (μ:=domeLaw N) (fun v=> (K' v) f) u
include p
lemma sigil_cov (x : Q₀) (h : Integrable (fun u=> coup S m J u x) (domeLaw (J.c m))) : CovCover J (render S J (sigil S m J x)) := by
  apply complete_cov J (texture S J _) m p; intro t y
  rw [coup_trace S m J t (sigil S m J x) y,sigil_pennant S m J x t h p]

-- Mark literally agrees with torus molasses (on this host). Include for corresponding
-- interaction applications. Also free continuity / local stencil.
lemma sigil_pour (x : Q₀) (h : Integrable (fun u=> coup S m J u x) (domeLaw (J.c m))) :
    render S J (sigil S m J x) m=molasses (render S J x m) := by
  funext u; let Te : Swatch S →L[ℂ] FC (Single N) := -- name shadow notation
    { (LinearMap.proj (R:=ℂ) (φ:=fun _ : Fields N=> FC (Single N)) u).comp (Tapestry.appear S J m) with cont:=render_cont S J m u }
  change Te (sigil S m J x) = ∫ p:Zodiac N,getBack (render S J x m) p u∂ domeLaw N
  refine (ContinuousLinearMap.integral_comp_comm (E:=Swatch S) (Fₗ:=FC (Single N)) (𝕜:=ℂ) Te h).symm.trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall fun i=> coup_agrees S m J i x u)
end veil

section rising
include V Q
local notation "W" => wingspan Λ l S
local notation "P₀" => renovate Y H s Q S
lemma twists_refine (u : Cover → SU.E) (x : Swatch S) :
    ocelli (tent Y H) W u ((P₀) x)=(P₀) (ocelli (tent Y H) S (parentGauge Λ u) x) := by
  apply pegOutput (tent Y H) W u (P₀ x)
  swap; · exact decorates (tent Y H) W u (P₀ x)
  rw [renovate_eq, renovate_eq]
  exact lens_up Y H V s Q (texture S K x) (texture S K _) u (decorates K S (parentGauge Λ u) x) -- tune

lemma pays_refined_gauge (x : Swatch S) (p : Hosp (wingspan Λ l S) ((tent Y H).c m)) :
    Integrable (fun u=> coup (wingspan Λ l S) m (tent Y H) u (P₀ x)) (domeLaw ((tent Y H).c m)) := by
  -- note: strong measurability & use of our actual funding of separability, no assertion
  -- that sup-distance is computable from a *prior* countable set of candidate regulator values.
  apply coup_pays W m _ p
  apply (venue_separable Y H V s Q S).mono
  rintro _ ⟨u,rfl⟩
  unfold coup; dsimp only; rw [twists_refine Y H V]
  exact mem_range_self _
end rising
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.pays_refined_gauge
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.sigil_cov
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.sigil_pour
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.coup_smooth_price
