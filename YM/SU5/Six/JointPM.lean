import YM.SU5.Six.ApplyPM
import YM.SU5.Six.HalfLimit
import YM.SU5.Cheer.Pavilion
/-!
# Axis-3 spectral conventions (same `ℚmeasure`), half-space costs
-/
set_option autoImplicit false
noncomputable section

namespace YM.Six
open MeasureTheory Filter Spectral OS Semigroup Balloon Cheer Boundary Probe
open scoped Topology InnerProductSpace ComplexConjugate NNReal

variable {H : Hilbert} (S : Semigroup H timeAxis)
local notation "Q" => S.ℚmeasure
variable {f : E4 → ℂ}

lemma positive_energy (x : H) : ∀ᵐ p ∂(Q).diagonal x, p ∈ half := S.bright x
lemma HalfTest.adm (hf : HalfTest f) : (Q).Admissible f :=
  ⟨_,⟨hf.clamp.1,hf.clamp.2⟩,fun x => (clamp_ae (positive_energy S x)).symm⟩

lemma zoom_half {ρ : ℝ} (hρ : 0 ≤ ρ) (p : E4) (hp : p ∈ half) : zoom ρ p ∈ half := by
  change 0 ≤ time (ρ • p)
  rw [Mink.clock_mul]
  exact mul_nonneg hρ hp
lemma HalfTest.zoom {ρ : ℝ} (hf : HalfTest f) (hρ : 0 ≤ ρ) :
    HalfTest (fun p => f (zoom ρ p)) := by
  have he : Continuous fun p : half => Cheer.zoom ρ (p:E4) := (eligible ρ).comp continuous_subtype_val
  exact ⟨hf.borel.comp (he.measurable.subtype_mk (h:=fun y => zoom_half hρ _ y.property)),
    hf.bounded.imp (fun _ hC y hy => hC _ (zoom_half hρ _ hy))⟩
lemma HalfTest.outlay_integral {ρ : ℝ} (hf : HalfTest f) (hρ : 0 ≤ ρ) (x : H) :
    ∫ p, f p ∂((outlay S x ρ):Measure E4) = ∫ p, f (Cheer.zoom ρ p) ∂(Q).diagonal x := by
  have hx := hf.integrable (μ:=((outlay S x ρ):Measure E4)) (radiant S x ρ hρ)
  exact integral_map (eligible ρ).measurable.aemeasurable hx.1

lemma rep_unit (x : E4) : (Q).Represents (fun p => plane p x) (S.unit.translation x) := by
  refine ⟨PVM.admBB _ ⟨?_,1,by simp⟩,fun v => ?_⟩
  · exact (show Continuous fun p => plane p x from by unfold plane; fun_prop).measurable
  rw [← S.joint,charFun_apply]
  rfl

lemma rep_edge (t : ℝ) : (Q).Represents
    (fun p => Complex.exp ((↑(time p*t):ℂ)*Complex.I)) (S.edge t) := by
  have h := rep_unit S (t • basis timeAxis)
  have he : (fun p : E4 => plane p (t • basis timeAxis)) =
      (fun p => Complex.exp ((↑(time p*t):ℂ)*Complex.I)) := by
    ext p
    rw [plane,real_inner_smul_right,real_inner_comm (basis _),basis_inner,mul_comm t _]
    rfl
  have hu : S.unit.translation (t • basis timeAxis) = S.edge t := by
    have ht : SEP timeAxis (t • basis timeAxis) = 0 := Subtype.ext (show t • basis timeAxis -_= 0 by simp)
    dsimp only [unit]; rw [ht, S.uZero]; simp
  rwa [he,hu] at h
lemma rep_space (y : Cross timeAxis) :
    (Q).Represents (fun p => plane p y.val) (S.U y) := by
  have hy : y.val timeAxis = 0 := y.property
  have ht : SEP timeAxis y.val = y := Subtype.ext
    (show y.val-y.val timeAxis • _=y.val by rw [hy,zero_smul,sub_zero])
  have hu : S.unit.translation y.val = S.U y := by
    dsimp only [unit]; rw [ht,hy,S.birth]; rfl
  rw [← hu]; exact rep_unit ..

/-- Spatial Fourier cost, radian positive sign. -/
def phasor (y : Space3) (p : E4) := plane (spatial p) y

lemma rep_phasor (y : Space3) : (Q).Represents (phasor y) (S.U (shore y)) := by
  have hp : (fun p : E4 => plane p (shore y).val) = phasor y := by
    ext p
    have ht : time (shore y).val = 0 := (shore y).property
    rw [plane,Mink.pairing,ht,mul_zero,add_zero,show spatial (shore y).val=y from spatial_position ..]
    rfl
  rw [← hp]; exact rep_space ..

/-- Axis-3 heat cost (no truncation needed a.e.). -/
def fade (t : ℝ≥0) (p : E4) : ℂ := ↑(tinct timeAxis t p)
lemma fade_test (t : ℝ≥0) : HalfTest (fade t) := by
  refine ⟨(show Continuous (fade t) by unfold fade tinct; fun_prop).measurable.comp
      measurable_subtype_coe,1,fun p hp => ?_⟩
  rw [fade,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ tinct timeAxis t p from (Real.exp_pos _).le)]
  exact fuel _ _ hp
lemma rep_heat (t : ℝ≥0) : (Q).Represents (fade t) (S.E t) := by
  refine ⟨(fade_test t).adm S,fun v => ?_⟩
  have h := during S t 0 v
  rw [S.uZero,ContinuousLinearMap.id_apply] at h
  simp only [ZeroMemClass.coe_zero,plane_zero,one_mul] at h
  exact h

end YM.Six
