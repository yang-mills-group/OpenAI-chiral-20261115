import ExactRunning.Finite.Projection

/-!
Translation by one cycle in the fourth direction. In particular,
rectangular intertwinings of translations intertwine cuts to the same radius (membership is a function
of translation eigenvalue).
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

/-- Matrix for pullback by a permutation. -/
def scroll [DecidableEq ι] (t : α ≃ ι) : Matrix α ι ℝ :=
  of fun i j => if j=t i then 1 else 0

lemma scroll_mul (t : α ≃ β) (M : Matrix β ι ℝ) (a b) :
    (scroll t * M) a b = M (t a) b := by
  simp [scroll,Matrix.mul_apply,ite_mul]

lemma mul_scroll (t : α ≃ β) (M : Matrix ι α ℝ) (a b) :
    (M * scroll t) a b = M a (t.symm b) := by
  simp [scroll, Matrix.mul_apply,mul_ite, show ∀ x, b=t x ↔ x=t.symm b from fun _ =>
    eq_comm.trans t.apply_eq_iff_eq_symm_apply]

@[simp] lemma scroll_mulVec (t : α ≃ β) (v : Corn β) :
    scroll t *ᵥ v = v ∘ t := by
  ext i; simp [scroll,Matrix.mulVec,dotProduct,ite_mul]

@[simp] lemma approached_scroll_mulVec (t : α ≃ β) (v : Phase β) :
    approached (scroll t) *ᵥ v = v ∘ t := by
  ext i; simp [scroll,Matrix.mulVec,dotProduct,ite_mul,approached,apply_ite (Complex.ofReal)]

lemma scroll_tr (t : α ≃ β) :
    (scroll t)ᵀ = scroll t.symm := by
  ext i j; simp [scroll, ← Equiv.apply_eq_iff_eq_symm_apply, eq_comm]

lemma scroll_orthog (t : α ≃ β) : scroll t * (scroll t)ᵀ = 1 := by
  rw [scroll_tr]
  apply ext_of_mulVec_single; intro i; rw [← mulVec_mulVec, scroll_mulVec, scroll_mulVec, one_mulVec]
  ext; simp

lemma comm_scroll_iff {t : Equiv.Perm α} {u : Equiv.Perm β} {M : Matrix α β ℝ} :
    scroll t * M = M * scroll u ↔ ∀ i j, M (t i) (u j) = M i j := by
  constructor
  · intro h i j; simpa only [scroll_mul,mul_scroll,Equiv.symm_apply_apply] using congr_fun (congr_fun h i) (u j)
  intro h; ext i j; simpa only [scroll_mul,mul_scroll,Equiv.apply_symm_apply] using h i (u.symm j)

namespace Latitude
variable (D : Latitude)
def stepIV (m : Side) : Site m := D.cycle.val • (step 3)
def shift (m : Side) (α : Type) : Equiv.Perm (Co m α) :=
  (Equiv.addRight (D.stepIV m)).prodCongr (.refl α)
def spin (m : Side) (α : Type) [DecidableEq α] : Matrix (Co m α) (Co m α) ℝ :=
  scroll (D.shift m α)

lemma shift_how (x : Co m ι) :
    D.shift m ι x = (x.1 + D.stepIV m,x.2) := rfl

lemma spin_orthog (m : Side) (α : Type) [DecidableEq α] [Fintype α] :
    D.spin m α * (D.spin m α)ᵀ = 1 := scroll_orthog _

def wind (p : Momentum) : ℂ := Complex.exp (Complex.I * (D.cycle.val * p 3))
@[simp] lemma wind_zero : D.wind 0 = 1 := by simp [wind]
lemma wind_add (p q) : D.wind (p+q) = D.wind p * D.wind q := by
  unfold wind; rw [Pi.add_apply,mul_add,mul_add,Complex.exp_add]
@[simp] lemma wind_neg (p) : D.wind (-p) = (D.wind p)⁻¹ := by simp [wind,Complex.exp_neg]
lemma wind_ne (p) : D.wind p ≠ 0 := Complex.exp_ne_zero _

lemma wind_rolls {p q} (h : rolls p q) : D.wind p = D.wind q := by
  obtain ⟨x,rfl⟩ := h
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-((D.cycle.val:ℤ) * x 3),?_⟩
  simp [reciprocal]
  ring

lemma mark_eq_of_wind_eq {D E : Latitude} {p q}
    (h : D.wind p = E.wind q) : D.mark p = E.mark q := by
  obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have t := congr_arg Complex.im hn
  have t : (D.cycle.val:ℝ)*(p 3).re = E.cycle.val * (q 3).re + 2 * Real.pi * n :=
    by simp at t; rw [t]; ring
  rw [mark,t,wrapDist_add]; rfl

lemma quiet_iff_wind {p} (hp : star p = p) : D.quiet p ↔ D.wind p = 1 := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := wrapDist_eq_zero.mp h
    have hi : (p 3).im = 0 := by have := congr_arg Complex.im (congr_fun hp 3); simp at this; linarith
    apply Complex.exp_eq_one_iff.mpr
    exact ⟨n,by apply Complex.ext <;> simp [hi,hn]; ring⟩
  intro h
  exact (mark_eq_of_wind_eq <| h.trans D.wind_zero.symm).trans D.quiet_zero

lemma stepIV_fares (p : Site m) :
    cell p (D.stepIV m) = D.wind (mon p) := by
  rw [wind,show Complex.I * (_ * _) = (D.cycle.val:ℂ) * (Complex.I * mon p 3) by ring,
    Complex.exp_nat_mul,← cell_step,stepIV]
  induction D.cycle.val <;> simp_all only [zero_smul,cell_origin,pow_zero,pow_succ,succ_nsmul,cell_add]

lemma spin_tune (p : Site m) (v : Phase α) :
    approached (D.spin m α) *ᵥ tune p v = D.wind (mon p) • tune p v := by
  rw [spin,approached_scroll_mulVec]; ext; simp [tune,shift_how, stepIV_fares]; ring

lemma spinT_tune (p : Site m) (v : Phase α) :
    (approached (D.spin m α))ᵀ *ᵥ tune p v = (D.wind (mon p))⁻¹ • tune p v := by
  let A := approached (D.spin m α)
  have h : A * Aᵀ = 1 := by
    exact (prom_mul (D.spin m α) (D.spin m α)ᵀ).symm.trans (by rw [spin_orthog, approach_one])
  have u : IsUnit A := ⟨⟨_,_,h,mul_eq_one_comm.mp h⟩,rfl⟩
  apply mulVec_injective_of_isUnit u
  unfold A at *
  rw [mulVec_mulVec,h,one_mulVec, mulVec_smul,spin_tune,inv_smul_smul₀ (D.wind_ne _)]

lemma cut_tune (p : Site m) (v : Phase α) :
    approached (D.cut m α).e *ᵥ tune p v =
      (if D.active (mon p) then (1:ℂ) else 0) • tune p v := by
  rw [D.cut_jaunt _ _ p _ (rolls.refl _),add_zero, maskM]
  split <;> ext <;> simp [tune]

/-- Any translation-intertwiner carries the cut. Useful e.g. for
block presentation, and repeated gauge transformations. -/
lemma cut_of_spinC {D E : Latitude} {n : Side} {X : Matrix (Co m α) (Co n β) ℂ}
    (hr : D.radius = E.radius)
    (h : approached (D.spin m α) * X = X * approached (E.spin n β)) :
    approached (D.cut m α).e * X = X * approached (E.cut n β).e := by
  apply mat_ext_on_tune; intro p v; apply ray_book; intro q u
  have hy := congr_arg (fun M => dotProduct (tune q u) (M *ᵥ tune p v)) h
  have hd (v w : Phase (Co m α)) (M : Matrix (Co m α) (Co m α) ℂ) :
      dotProduct v (M *ᵥ w) = dotProduct (Mᵀ *ᵥ v) w :=
    by rw [dotProduct_mulVec, mulVec_transpose]
  rw [← mulVec_mulVec,hd,D.spinT_tune,smul_dotProduct,
    ← mulVec_mulVec (tune p v) X,E.spin_tune,mulVec_smul,dotProduct_smul] at hy

  have h₀ : (approached (D.cut m α).e)ᵀ = approached (D.cut m α).e :=
    congr_arg approached (D.cut m α).sym
  rw [← mulVec_mulVec,hd,h₀,D.cut_tune,smul_dotProduct,
    ← mulVec_mulVec (tune p v) X,E.cut_tune,mulVec_smul,dotProduct_smul]
  rcases eq_or_ne (dotProduct (tune q u) (X *ᵥ tune p v)) 0 with h | h
  · simp [h]
  have he := mark_eq_of_wind_eq ((D.wind_neg _).trans <| mul_right_cancel₀ h hy)
  rw [D.mark_neg] at he
  simp [Latitude.active,hr,he]

lemma cut_of_spin {D E : Latitude} {n : Side} {X : Matrix (Co m α) (Co n β) ℝ}
    (hr : D.radius = E.radius)
    (h : D.spin m α * X = X * E.spin n β) : (D.cut m α).e * X = X * (E.cut n β).e := by
  apply approached_inj
  rw [prom_mul,prom_mul]
  exact cut_of_spinC hr (by rw [← prom_mul,← prom_mul,h])

/-- Spin law for a shifted operator. -/
lemma jaunt_spin {a : Site m} {X : CircM m α β} {F : Momentum → CompM α β}
    (h : Jaunt X F a) :
    approached (D.spin m α) * X =
      D.wind (mon a) • (X * approached (D.spin m β)) := by
  apply mat_ext_on_tune; intro p v
  rw [← mulVec_mulVec, h p _ (rolls.refl _), spin_tune,
    smul_mulVec,← mulVec_mulVec,spin_tune,mulVec_smul,h p _ (rolls.refl _),
    smul_smul,mul_comm (D.wind (mon a)),
    D.wind_rolls ((rolls.refl _).combine (rolls.refl _)), wind_add]

lemma jaunt0_spin {X : CircM m α β} {F : Momentum → CompM α β} (h : Jaunt X F 0) :
    approached (D.spin m α) * X = X * approached (D.spin m β) := by
  simpa [mon_zero] using D.jaunt_spin h

end Latitude
end ExactRunning
