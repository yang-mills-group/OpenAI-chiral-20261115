import ExactRunning.Thermo.Unmask

/-!
# External momentum probes
-/
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal ComplexConjugate Matrix


def tilt (i : Axis) (t : ℝ) : Momentum := axes (t • step i)

@[simp] lemma tilt_real (i t) : star (tilt i t) = tilt i t := axes_real _

@[simp] lemma tilt_zero (i) : tilt i 0 = 0 := by simp [tilt,axes_origin]

lemma tilt_neg (i t) : tilt i (-t) = -tilt i t := by simp only [tilt,neg_smul,axes_flip]

@[fun_prop] lemma tilt_smooth (i) : ContDiff ℝ ω (tilt i) :=
  axes_maps.comp (contDiff_id.smul contDiff_const)

@[simp] lemma tilt_pick (i t) : tilt i t i = t := by simp [tilt,axes, step]

lemma tilt_off {i j} (h : i ≠ j) (t) : tilt i t j = 0 := by simp [tilt, axes, step,h.symm]

lemma tilt_quiet (D : Latitude) {i} (h : i ≠ 3) (t) : D.quiet (tilt i t) :=
  Latitude.quiet.of_eq (tilt_off h t) _

def Radian (t : ℝ) := ∃ r : ℚ, t = 2 * Real.pi * r

lemma Radian.equalizer {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, Radian t → f t = g t) : f = g := by
  let L := fun x : ℝ=> 2 * Real.pi * x
  have hL : Continuous L := by unfold L; continuity
  have he : f ∘ L = g ∘ L :=
    Rat.denseRange_cast.equalizer (hf.comp hL) (hg.comp hL)
      (funext fun r=> h _ ⟨r,rfl⟩)
  funext t
  have hx : L (t / (2 * Real.pi)) = t := by unfold L; field_simp [Real.pi_ne_zero]
  rw [← hx]
  exact congr_fun he _

/-- Availability of arbitrarily long periods (parameter `lo` can run).
The actual periods needn't be part of any selected diagonal; they are
auxiliary to identify the coefficient from its matching conditions. -/
lemma Radian.packet_tilt {t} (h : Radian t) (i : Axis) (lo : ℕ) :
    ∃ m : ℕ → Side, Tendsto (fun n => (m n).val) atTop atTop ∧
      (∀ n, lo ≤ (m n).val) ∧
      ∃ a : ∀ n, Site (m n), ∀ n, rolls (mon (a n)) (tilt i t) := by
  obtain ⟨r,rfl⟩ := h
  let d : Side := ⟨r.den,r.den_pos⟩
  let u (n : ℕ) : Side := ⟨lo+n+1,by omega⟩
  let m (n) := u n * d
  have he n : lo+n+1 ≤ (m n).val :=
    le_mul_of_one_le_right (a:=lo+n+1) (Nat.zero_le _) (show 1 ≤ d.val from d.property)
  refine ⟨m,tendsto_atTop.2 fun b => ?_,fun n => le_trans (by omega) (he n), ?_⟩
  · filter_upwards [eventually_ge_atTop b] with n hn
    exact le_trans (by omega) (he n)
  let v n : Cover := ((r.num*(u n).val):ℤ) • step i
  have hz n : tilt i (2*Real.pi*r) = (((m n).val:ℂ))⁻¹ • reciprocal (v n) := by

    funext j; unfold v
    by_cases h : j=i
    · subst j
      rw [tilt_pick, Rat.cast_def]
      simp only [m,d, PNat.mul_coe, Pi.smul_apply, smul_eq_mul, reciprocal]
      rw [show (step i:Cover) i=1 by simp]
      push_cast; field_simp [side_ne]
      rfl
    rw [tilt_off (Ne.symm h)]
    simp [reciprocal,step,h]
  let X n := wrap (m n) (v n)
  refine ⟨X, fun n => ?_⟩
  obtain ⟨z,hz'⟩ := cover_of_eq _ (v n) (wrap_lift (X n))
  rw [hz n]
  refine ⟨z,?_⟩
  funext j
  simp only [reciprocal,hz',mon, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [nsmul_eq_mul]
  push_cast; field_simp [side_ne]

namespace Latitude
variable {p : Momentum} {L : Side}

private lemma mark_alias {d δ} {l : Site L} :
    (incoming L d).mark (aliasAt p l) = (native δ).mark p := by
  have ht : rolls p (L.val • aliasAt p l) := ⟨lift l,alias_scale p l⟩
  refine Eq.trans ?_ (((native δ).mark_rolls ht).symm)
  unfold mark
  simp [native,incoming]

@[simp] lemma active_alias {d} {l : Site L} :
    (incoming L d).active (aliasAt p l) ↔ (native (L.val*d)).active p := by
  rw [active, active, mark_alias (δ:=L.val*d)]
  rfl
@[simp] lemma safe_alias {d} {l : Site L} :
    (incoming L d).safe (aliasAt p l) ↔ (native (L.val*d)).safe p := by
  rw [safe, safe, mark_alias (δ:=L.val*d)]; rfl
@[simp] lemma quiet_alias {d} {l : Site L} :
    (incoming L d).quiet (aliasAt p l) ↔ (native (L.val*d)).quiet p := by
  rw [quiet, quiet, mark_alias (δ:=L.val*d)]

end Latitude
end ExactRunning
