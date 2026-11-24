import ExactRunning.Det.Fit

/-!
# Restricted Schur rule with gauges

The first splitting we'll use for the joint log determinant. B refers to
the variables we'd like to eliminate ("high", will include fine links
and coarse frame). V denotes the high gauge condition, A the high verticals,
S the high-by-high Hessian, X the mixed block. If you want to use another,
possibly degenerate, gauge U on B, pass between them by congruence
(`shear_sq`): when VA is invertible and the columns of A are (S=Sᵀ and Xᵀ)
null directions, just add A(VA)⁻¹(U−V) to the identity.

In gauge V we can pivot to get restricted log determinants on high B
and on the other variables, the latter evaluated on an
ordinary Schur complement (full inverse!). See `Det.log_schur`:
all of this is through second order on rays, using `Fit` for cut
calculations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix Filter
open scoped Topology ContDiff

namespace ExactRunning

variable {m n k j : Type} [Fintype m] [Fintype n] [Fintype k] [Fintype j]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq j]

variable {P : ModeCut m} {Q : ModeCut n} {R : ModeCut k}

section pivot

lemma Fit.cutdet_cont {U : ℝ → Matrix m m ℝ} (h : Fit P P U) :
    ContinuousAt (fun t => P.cutdet (U t)) 0 :=
  (MatTouch.cutdet (MatTouch.refl h.cont) P).hf

theorem pivot {X : ℝ → Matrix m m ℝ} {Y : ℝ → Matrix m n ℝ}
    {Z : ℝ → Matrix n m ℝ} {W : ℝ → Matrix n n ℝ}
    (hx : Fit P P X) (hy : Fit P Q Y) (hz : Fit Q P Z) (hw : Fit Q Q W)
    (hu : (X 0).det ≠ 0) :
    Touch (fun t => (P.direct Q).cutdet (fromBlocks (X t) (Y t) (Z t) (W t)))
      (fun t => P.cutdet (X t) * Q.cutdet (W t - Z t * (X t)⁻¹ * Y t)) := by
  let T t := fromBlocks (1 : Matrix m m ℝ) (0 : Matrix m n ℝ) (-(Z t * (X t)⁻¹)) 1
  have hT : Fit (P.direct Q) (P.direct Q) T :=
    (Fit.one P).blocks (Fit.zero _ _) (hz.mul (hx.inv hu)).neg (Fit.one Q)

  refine (hT.cutdet_mul (hx.blocks hy hz hw)).symm.congr
    (Eventually.of_forall fun _ => by simp [T]) ?_
  filter_upwards [hx.cont.det.eventually_ne hu] with t ht
  dsimp [T]
  rw [fromBlocks_multiply]
  have hk := Matrix.nonsing_inv_mul (X t) (isUnit_iff_ne_zero.mpr ht)
  simp only [Matrix.one_mul,Matrix.zero_mul,add_zero, Matrix.neg_mul,
    Matrix.mul_assoc (Z t) _ (X t), hk, Matrix.mul_one,neg_add_cancel,
    ModeCut.cutdet_upper]
  rw [add_comm,← sub_eq_add_neg]
end pivot

namespace Det

/-- Block matrix of Hessian, with high gauge completion by `C`. Include
any low completion in `T`. -/
def joint (C : Matrix k m ℝ) (S : Matrix m m ℝ) (X : Matrix m n ℝ) (T : Matrix n n ℝ) :=
  fromBlocks (S + Cᵀ * C) X Xᵀ T

variable {A : ℝ → Matrix m k ℝ} {U V : ℝ → Matrix k m ℝ}
    {S : ℝ → Matrix m m ℝ} {X : ℝ → Matrix m n ℝ} {T : ℝ → Matrix n n ℝ}


private lemma gauge_factor (ha : Fit P R A) (hu : Fit R P U) (hv : Fit R P V)
    (hm : ((V 0 * A 0)).det ≠ 0) :
    Touch (fun t => P.cutdet (1 + A t * ((V t * A t)⁻¹ * (U t - V t))) * R.cutdet (V t * A t))
      (fun t => R.cutdet (U t * A t)) := by
  let M := fun t => (V t * A t)⁻¹ * (U t - V t)
  have hd : Fit R P M := ((hv.mul ha).inv hm).mul (hu.sub hv)
  refine (((ha.cutdet_sylvester hd).mul
    (Touch.refl (hv.mul ha).cutdet_cont))).trans ?_

  refine ((hv.mul ha).cutdet_mul ((Fit.one _).add (hd.mul ha))).symm.congr
    (Eventually.of_forall fun _ => _root_.mul_comm _ _) ?_
  filter_upwards [(hv.mul ha).cont.det.eventually_ne hm] with t ht
  dsimp [M]
  have hk := Matrix.mul_nonsing_inv ((V t) * A t) (isUnit_iff_ne_zero.mpr ht)
  rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc (V t * A t), hk, Matrix.one_mul, Matrix.sub_mul]
  congr 1; abel

private lemma gauge_eq
    (A : Matrix m k ℝ) (U V : Matrix k m ℝ)
    (S : Matrix m m ℝ) (X : Matrix m n ℝ) (T : Matrix n n ℝ)
    (hm : IsUnit (V * A).det) (hs : S * A = 0 ∧ Xᵀ * A = 0 ∧ Sᵀ = S) :
    let D := fromBlocks (1 + A * ((V * A)⁻¹ * (U - V))) 0 0 (1 : Matrix n n ℝ)
    Dᵀ * joint V S X T * D = joint U S X T := by
  let Y := 1 + A * ((V * A)⁻¹ * (U - V))
  have hy : V * Y = U := by
    rw [show Y = 1 + _ from rfl,Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc V,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hm, Matrix.one_mul]
    abel

  have hS : S * Y = S := by
    rw [show Y = 1 + _ from rfl,Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc S,hs.1];simp
  have hX : Xᵀ * Y = Xᵀ := by
    rw [show Y = 1 + _ from rfl,Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc Xᵀ,hs.2.1];simp
  have hS' : Yᵀ * S = S := by simpa [hs.2.2] using congr_arg transpose hS
  have hX' : Yᵀ * X = X := by simpa using congr_arg transpose hX
  dsimp only [joint]
  rw [fromBlocks_transpose,fromBlocks_multiply,fromBlocks_multiply]
  simp only [transpose_one,transpose_zero,Matrix.mul_zero, Matrix.zero_mul, zero_add,add_zero,
    Matrix.one_mul, Matrix.mul_one]
  change fromBlocks ((Yᵀ * (S+Vᵀ*V)) * Y) (Yᵀ * X) (Xᵀ * Y) T = _
  rw [hX,hX', Matrix.mul_add Yᵀ, hS', Matrix.add_mul,hS,
    ← hy,transpose_mul V Y]
  simp only [Matrix.mul_assoc]

lemma cutdet_congr {D H : ℝ → Matrix m m ℝ}
    (hd : Fit P P D) (hh : Fit P P H) :
    Touch (fun t => P.cutdet ((D t)ᵀ * H t * D t))
      (fun t => P.cutdet (H t) * P.cutdet (D t)^2) := by
  refine ((hd.tr.mul hh).cutdet_mul hd).trans
    (((hd.tr.cutdet_mul hh).mul (Touch.refl hd.cutdet_cont)).congr .rfl ?_)
  exact Eventually.of_forall fun _ => by simp only [ModeCut.cutdet_transpose]; ring

/-- Change of high gauge completion by a (possibly singular)
change of variables. -/
theorem shear_sq (ha : Fit P R A) (hu : Fit R P U) (hv : Fit R P V)
    (hs : Fit P P S) (hx : Fit P Q X) (ht : Fit Q Q T)
    (hm : (V 0 * A 0).det ≠ 0)
    (hell : ∀ᶠ t in 𝓝 (0:ℝ), S t * A t = 0 ∧ (X t)ᵀ * A t = 0 ∧ (S t)ᵀ = S t) :
    Touch (fun t => (P.direct Q).cutdet (joint (U t) (S t) (X t) (T t)) * R.cutdet (V t * A t)^2)
      (fun t => (P.direct Q).cutdet (joint (V t) (S t) (X t) (T t)) * R.cutdet (U t * A t)^2) := by
  let hY := (Fit.one P).add (ha.mul (((hv.mul ha).inv hm).mul (hu.sub hv)))
  let hD := hY.blocks (Fit.zero P Q) (Fit.zero Q P) (Fit.one Q)
  let hH := (hs.add (hv.tr.mul hv)).blocks hx hx.tr ht
  let h := gauge_factor ha hu hv hm
  let hB := Touch.refl (f:=fun t => R.cutdet (V t * A t)^2) ((hv.mul ha).cutdet_cont.pow 2)
  simp only [joint]
  refine Touch.trans (((cutdet_congr hD hH).mul hB).congr ?_ .rfl) ?_
  · filter_upwards [(hv.mul ha).cont.det.eventually_ne hm, hell] with t he hg
    exact congr_arg (fun M => (P.direct Q).cutdet M * R.cutdet (V t * A t)^2) (gauge_eq _ _ _ _ _ _
      (isUnit_iff_ne_zero.2 he) hg)

  simp only [ModeCut.cutdet_upper,ModeCut.cutdet_id,_root_.mul_one, _root_.mul_assoc,← mul_pow]
  exact ((Touch.refl hH.cutdet_cont).mul (h.mul h)).congr
    (Eventually.of_forall fun _ => by dsimp; ring) (Eventually.of_forall fun _ => by simp only [pow_two])

/-- A gapped operator respecting the cut is gapped on the cut. -/
lemma cutdet_nz {X : Matrix m m ℝ} (he : P.e * X = X * P.e) (hu : X.det ≠ 0) : P.cutdet X ≠ 0 := by
  have hh : P.cutdet X * P.cutdet X⁻¹ = 1 := by
    simp only [ModeCut.cutdet, ← det_mul, P.compMat_mul_left _ _ he,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu), ModeCut.compMat_id, det_one]
  exact left_ne_zero_of_mul_eq_one hh

private lemma log_split {a b c u v : ℝ → ℝ}
    (h : Touch (fun t => a t * v t ^ 2) (fun t => (b t * c t) * u t ^ 2))
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0) (hc : ContinuousAt c 0)
    (hu : ContinuousAt u 0) (hv : ContinuousAt v 0)
    (bz : b 0 ≠ 0) (cz : c 0 ≠ 0) (uz : u 0 ≠ 0) (vz : v 0 ≠ 0) :
    Touch (fun t => 1/2 * Real.log (a t) - Real.log (u t))
      (fun t => (1/2 * Real.log (b t) - Real.log (v t)) + 1/2 * Real.log (c t)) := by
  have eh : a 0 * v 0 ^ 2 ≠ 0 := h.zero.symm ▸ mul_ne_zero (mul_ne_zero bz cz) (pow_ne_zero _ uz)
  have az := left_ne_zero_of_mul eh
  refine ((((Touch.const (1/2:ℝ)).mul (h.log eh)).sub
      (Touch.refl (hu.log uz))).sub (Touch.refl (hv.log vz))).congr ?_ ?_
  · filter_upwards [ha.eventually_ne az,hv.eventually_ne vz] with t ht it
    simp only [Real.log_mul ht (pow_ne_zero 2 it),Real.log_pow]
    push_cast
    ring
  · filter_upwards [hb.eventually_ne bz,hc.eventually_ne cz,hu.eventually_ne uz] with t bt ct ut
    simp only [Real.log_mul (mul_ne_zero bt ct) (pow_ne_zero 2 ut),Real.log_mul bt ct,Real.log_pow]
    push_cast
    ring

def schur (S : Matrix m m ℝ) (X : Matrix m n ℝ) (T : Matrix n n ℝ) (V : Matrix k m ℝ) :=
  T - Xᵀ * (S + Vᵀ * V)⁻¹ * X

/-- Change of high gauge completion, pivot on high block,
restricted determinants. -/
theorem log_schur (ha : Fit P R A) (hu : Fit R P U) (hv : Fit R P V)
    (hs : Fit P P S) (hx : Fit P Q X) (ht : Fit Q Q T)
    (hm : (V 0 * A 0).det ≠ 0)
    (hell : ∀ᶠ t in 𝓝 (0:ℝ), S t * A t = 0 ∧ (X t)ᵀ * A t = 0 ∧ (S t)ᵀ = S t)
    (hop : (S 0 + (V 0)ᵀ * V 0).det ≠ 0)
    (hghost : R.cutdet (U 0 * A 0) ≠ 0)
    (hef : Q.cutdet (schur (S 0) (X 0) (T 0) (V 0)) ≠ 0) :

    Touch (fun t =>
        (1/2) * (P.direct Q).cutlog (joint (U t) (S t) (X t) (T t)) - R.cutlog (U t * A t))
      (fun t =>
        ((1/2) * P.cutlog (S t + (V t)ᵀ * V t) - R.cutlog (V t * A t)) +
        (1/2) * Q.cutlog (schur (S t) (X t) (T t) (V t))) := by
  let hh := shear_sq ha hu hv hs hx ht hm hell
  let hd := hs.add (hv.tr.mul hv)
  have hp := pivot hd hx hx.tr ht hop
  have hc := (hu.mul ha).cutdet_cont
  have hh := hh.trans (hp.mul (Touch.refl (hc.pow 2)))
  exact log_split hh ((hs.add (hu.tr.mul hu)).blocks hx hx.tr ht).cutdet_cont hd.cutdet_cont
    (ht.sub ((hx.tr.mul (hd.inv hop)).mul hx)).cutdet_cont hc (hv.mul ha).cutdet_cont
    (cutdet_nz hd.at_zero hop) hef hghost (cutdet_nz (hv.mul ha).at_zero hm)

/-- Schur form on stationary graph, *uncompressed*. -/
theorem schur_graph (A : Matrix m k ℝ) (B : Matrix m n ℝ) (V : Matrix k m ℝ)
    (S : Matrix m m ℝ) (X : Matrix m n ℝ) (T : Matrix n n ℝ)
    (hm : IsUnit (V * A).det) (hs : S * A = 0) (hx : Xᵀ * A = 0)
    (hb : S * B + X = 0) (hu : IsUnit (S + Vᵀ * V).det) :
    schur S X T V = T + Xᵀ * B := by
  let W := A * ((V * A)⁻¹ * (V * B))
  have e : (S + Vᵀ * V) * (B-W) = -X := by
    have h1 : V * W = V * B := by
      unfold W
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hm, Matrix.one_mul]
    rw [Matrix.add_mul, Matrix.mul_assoc Vᵀ, Matrix.mul_sub, Matrix.mul_sub, h1]
    have h2 : S * W = 0 := by unfold W;rw [← Matrix.mul_assoc,hs, Matrix.zero_mul]
    simp [h2]
    exact eq_neg_of_add_eq_zero_left hb

  have h2 : Xᵀ * W = 0 := by unfold W;rw [← Matrix.mul_assoc,hx, Matrix.zero_mul]
  rw [schur,Matrix.mul_assoc,sub_eq_add_neg,← Matrix.mul_neg,← Matrix.mul_neg,← e,
    ← Matrix.mul_assoc (_⁻¹), Matrix.nonsing_inv_mul _ hu,Matrix.one_mul, Matrix.mul_sub,h2, sub_zero]
end Det
end ExactRunning
