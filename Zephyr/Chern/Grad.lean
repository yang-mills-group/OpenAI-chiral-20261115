import Zephyr.Chern.Silk
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.Laurent


def rune (i : Axis) (x : Cover) : ℂ := Complex.I * x i

lemma axis_le_size (i : Axis) (x : Cover) : (x i).natAbs ≤ size x :=
  Finset.single_le_sum (f:=fun j => (x j).natAbs) (fun _ _ => by positivity) (Finset.mem_univ i)

lemma norm_rune (i : Axis) (x : Cover) : ‖rune i x‖ ≤ size x := by
  rw [rune,norm_mul,Complex.norm_intCast,Complex.norm_I,one_mul, ←Int.cast_abs]
  norm_cast
  have := axis_le_size i x
  rwa [←Int.natCast_natAbs,Int.ofNat_le]

lemma Fast.rune {f : Cover → ℂ} (hf : Fast f) (i : Axis) :
    Fast (fun x => rune i x * f x) := by
  intro k
  apply (hf (k+1)).of_nonneg_of_le
  · intro; exact mul_nonneg (penPos ..).le (norm_nonneg _)
  intro x
  rw [norm_mul, ←mul_assoc, show pen (k+1) x= pen k x * (1+(size x:ℝ)) by
    rw [pen,pow_succ,pen]]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((norm_rune i x).trans (le_add_of_nonneg_left zero_le_one)) (penPos k x).le) (norm_nonneg _)

namespace Silk

private def gr (i : Axis) : Silk →ₗ[ℂ] Silk where
  toFun a := ⟨_, a.fast.rune i⟩
  map_add' a b := by
    apply Silk.ext
    exact funext fun x => mul_add ..

  map_smul' z a := by
    apply Silk.ext; funext x
    change rune i x * (z • a).co x= (z • (⟨_,a.fast.rune i⟩ : Silk)).co x
    rw [co_smul, co_smul]; exact mul_left_comm ..

private lemma gr_co (i : Axis) (a : Silk) (x) : (gr i a).co x = rune i x * a.co x := rfl

private lemma gr_mul (i : Axis) (a b : Silk) :
    gr i (a*b)= a * gr i b + gr i a * b := by
  apply Silk.ext; funext x
  rw [gr_co,co_mul,co_add,co_mul,co_mul, ←tsum_mul_left,
    ←(a.fast.pack (gr i b).fast x).tsum_add ((gr i a).fast.pack b.fast x)]
  refine tsum_congr fun y => ?_
  rw [gr_co,gr_co]
  simp only [rune,Pi.sub_apply,Int.cast_sub]; ring

/-- momentum derivative. -/
def D (i : Axis) : Derivation ℂ Silk Silk :=
  Derivation.mk' (gr i) (fun a b => by rw [smul_eq_mul,smul_eq_mul,mul_comm b,gr_mul])

lemma D_mul (i : Axis) (a b : Silk) : D i (a*b)=a*D i b + D i a*b := gr_mul i a b

lemma co_D (i : Axis) (a : Silk) (x) : (D i a).co x = rune i x * a.co x := rfl
lemma τ_D (i : Axis) (a : Silk) : τ (D i a) = 0 := by
  rw [τ,coeff_apply,co_D]; simp [rune]

lemma D_symm (i j : Axis) (a : Silk) :
    D i (D j a)=D j (D i a) := Silk.ext (funext fun _ => mul_left_comm ..)
