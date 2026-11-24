import YM.SU5.MacroSix.PolarizedMeasure

/-!
# Region restriction calculus on the present PVM

Prove directly from the project's spectral diagonal-integral identities what we need:
projecting commutes (range/kernel perpendicular at every spectral region), pairings
with a general wedge shifted-and-heated vector, and the zero-time case. No density of
any joint measure with respect to Lebesgue assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix.Projections
open Function Filter Set MeasureTheory Mink OS OS.Semigroup.Balloon Spectral Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators

variable {H : Hilbert} {j : Axis}
section orth
variable {X : Type*} [MeasurableSpace X] (P : PVM H X) {A : Set X} (h : MeasurableSet A)
local notation "K" => P.region A
include h

lemma slides (x y : H) : inner ℂ (K x) y = inner ℂ x (K y) := by
  nth_rw 1 [← P.real h]; rw [ContinuousLinearMap.adjoint_inner_left]

lemma smaller {B : Set X} (p : B ⊆ A) (q : MeasurableSet B) :
    (P.region B).comp (K) = P.region B := by rw [P.joins q h,inter_eq_left.mpr p]

private lemma regions_commute {B : Set X} (v : MeasurableSet B) (x : H) :
    K (P.region B x) = P.region B (K x) := by
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, P.joins h v,
    P.joins v h, inter_comm]

lemma diagonal_restrict (x : H) : P.diagonal (K x) = (P.diagonal x).restrict A := by
  ext B b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [Measure.restrict_apply b]; change (P.diagonal _).real _ = (P.diagonal _).real _
  rw [P.same b, P.same (b.inter h), ← ContinuousLinearMap.comp_apply, P.joins b h]

lemma norm_sq_grant (x : H) : ‖K x‖^2 ≤ ‖x‖^2 := by
  calc _ = (P.diagonal x).real A := (P.same h x).symm
       _ ≤ (P.diagonal x).real univ := measureReal_mono (subset_univ _)
       _ = ‖x‖^2 := by rw [P.same MeasurableSet.univ, P.all]; rfl

private lemma annul (x y : H) (p : K x=x) (v : K y=0) : inner ℂ x y=0 := by
  nth_rw 1 [← p]; rw [slides P h,v]; simp

omit h in
private lemma diagonal_pm (x y : H) (u : inner ℂ x y=0) : ‖x+y‖^2 = ‖x-y‖^2 := by
  rw [norm_add_sq (𝕜:=ℂ), norm_sub_sq (𝕜:=ℂ), u]; simp

private lemma polarOff (x y : H) (p : K x=x) (q : K y=0) :
    P.diagonal (x+y) = P.diagonal (x-y) := by
  ext B b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (P.diagonal _).real _=(P.diagonal _).real _
  rw [P.same b, P.same b, map_add,map_sub]
  exact diagonal_pm _ _ (annul P h _ _ (by rw [regions_commute P h b,p])
    (by rw [regions_commute P h b,q,map_zero]))

private lemma zeroOff (x y : H) (p : K x=x) (q : K y=0) (T : H.Op) (f : X → ℂ)
    (u : ∀ x : H, inner ℂ x (T x)=∫ w, f w ∂P.diagonal x) :
    inner ℂ x (T y)=0 ∧ inner ℂ y (T x)=0 := by
  have he : inner ℂ x (T y)=0 := by
    rw [← Cheer.MatrixZoom.polar_inner]; simp_rw [u]; unfold Cheer.MatrixZoom.polar
    dsimp only; rw [polarOff P h x y p q, polarOff P h x (Complex.I • y) p (by rw [map_smul,q,smul_zero])]; ring
  have hp : inner ℂ (x+y) (T (x+y))=inner ℂ (x-y) (T (x-y)) := by
    rw [u,u,polarOff P h x y p q]
  simp only [map_sub,map_add,inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,he] at hp
  refine ⟨he,?_⟩
  linear_combination (norm := ring1) hp / 2

private lemma mixCommute (T : H.Op) (v : ∀ (x y : H), K x=x → K y=0 →
    inner ℂ x (T y)=0 ∧ inner ℂ y (T x)=0) (x : H) : K (T x)=T (K x) := by
  apply ext_inner_left ℂ; intro w
  let Q (z : H) := z-K z
  have he (z : H) : K (Q z)=0 := by rw [show Q z=z-K z from rfl,map_sub, P.idempotent h z,sub_self]
  rw [← slides P h]
  have ht : inner ℂ (K w) (T (Q x))=0 := (v _ _ (P.idempotent h w) (he x)).1
  have hv : inner ℂ (Q w) (T (K x))=0 := (v _ _ (P.idempotent h x) (he w)).2
  unfold Q at ht hv
  rw [map_sub,inner_sub_right] at ht
  rw [inner_sub_left] at hv
  exact (sub_eq_zero.mp ht).trans (sub_eq_zero.mp hv).symm

lemma diag_commute (T : H.Op) (f : X → ℂ)
    (u : ∀ x : H, inner ℂ x (T x)=∫ w, f w ∂P.diagonal x) (x : H) : K (T x)=T (K x) :=
  mixCommute P h T (fun x y p v ↦ zeroOff P h x y p v T f u) x

lemma pairing_inside (T : H.Op) (f : X → ℂ)
    (u : ∀ x : H, inner ℂ x (T x)=∫ w, f w ∂P.diagonal x) (x : H) :
    inner ℂ (K x) (T x) = ∫ w in A, f w ∂P.diagonal x := by
  rw [← diagonal_restrict P h x, ← u, ← diag_commute P h T f u x, ← slides P h,
    P.idempotent h x]

end orth

variable (S : OS.Semigroup H j)
local notation "P" => S.ℚmeasure
local notation "K" D:max => S.ℚmeasure.region D
variable {D : Set E4} (h : MeasurableSet D)

def heatSpace (a : OS.Cross j) (r : ℝ≥0) (x : E4) : ℂ :=
  plane x (a:E4)*(↑(tinct j r x):ℂ)
include h
lemma slideHeat (x : H) (a : OS.Cross j) (r : ℝ≥0) : (K D) (S.U a (S.E r x)) =
    S.U a (S.E r ((K D) x)) :=
  diag_commute P h ((S.U a).comp (S.E r)) (heatSpace a r) (during S r a) x
lemma pairHeat (x : H) (a : OS.Cross j) (r : ℝ≥0) : inner ℂ ((K D) x) (S.U a (S.E r x)) =
    ∫ w in D, heatSpace a r w ∂(P).diagonal x :=
  pairing_inside P h ((S.U a).comp (S.E r)) (heatSpace a r) (during S r a) x

omit h
lemma darkTime (r : ℝ≥0) (x : H) :
    S.ℚmeasure.region {x : E4 | x j=0} (x-S.E r x)=0 := by
  let D := {x : E4 | x j=0}
  have he : MeasurableSet D := isClosed_eq (PiLp.continuous_apply _ _ j) continuous_const |>.measurableSet
  have ht : S.E r ((K D) x)= (K D) (S.E r x) := by
    simpa only [S.uZero, ContinuousLinearMap.id_apply] using (slideHeat S he x 0 r).symm
  let y := (K D) x
  have hu (t : ℝ≥0) : (inner ℂ y (S.E t y)).re=‖y‖^2 := by
    rw [earthy S t y, ← (P).same he,(show ((P).diagonal x).real D = ∫ _ in D,(1:ℝ) ∂(P).diagonal x by simp)]
    unfold y; rw [diagonal_restrict (P) he x]; refine integral_congr_ae ?_
    exact (ae_restrict_mem he).mono (fun v w ↦ by simp [tinct]; exact Or.inr w)
  have hp : ‖y-S.E r y‖^2=0 := by
    rw [norm_sub_sq (𝕜:=ℂ)]; change _ - 2*(inner ℂ y (S.E r y)).re + _=0
    rw [hu r, ← inner_self_eq_norm_sq (𝕜:=ℂ) (S.E r y), S.swing, ← ContinuousLinearMap.comp_apply,
      ← S.time]; rw [show RCLike.re (inner ℂ y _)=(inner ℂ y (S.E (r+r) y)).re from rfl, hu (r+r)]
    ring
  rw [map_sub, ← ht]; exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hp)
end YM.MacroSix.Projections
#print axioms YM.MacroSix.Projections.pairHeat
#print axioms YM.MacroSix.Projections.darkTime
