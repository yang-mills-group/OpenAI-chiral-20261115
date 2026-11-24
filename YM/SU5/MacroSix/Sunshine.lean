import YM.CF.Operator.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Instances.Matrix
/-! # Robust accretivity (L2 operator norm)

The stability statement at non-Hermitian matrices will still price the real quadratic
part. In particular this expresses positive discrepancy along every **mixed-family
ray** for the perturbed cross test in Part (i), with any requested strict slack. Not
asserting a Hermitian inequality on non-Hermitian matrices.
-/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.MacroSix
open Filter Finset Complex Matrix
open scoped Topology NNReal ENNReal InnerProductSpace MatrixOrder ComplexOrder BigOperators
  Matrix Matrix.Norms.L2Operator
attribute [local instance] CF.opCStarAlgebra
variable {J T:Type*}[Fintype J][DecidableEq J]
local notation "M"=> Matrix J J ℂ
local notation "I₀"=> (1 : Matrix J J ℂ)

def hermitianRay (A : Matrix J J ℂ) := (1/2:ℝ) • (A+star A)
def ReFloor (A : Matrix J J ℂ) (d : ℝ) : Prop := (d:ℂ) • 1 ≤ hermitianRay A

private lemma sunrise (A : Matrix J J ℂ) : IsSelfAdjoint (hermitianRay A) := by
  simp [hermitianRay, IsSelfAdjoint, star_smul, add_comm]
lemma sunrise_herm (A : Matrix J J ℂ) (h : IsSelfAdjoint A) : hermitianRay A=A := by
  have hh : star A=A := h
  unfold hermitianRay; rw [hh,smul_add, ← add_smul]; norm_num
lemma rays_cont {J:Type*}[Fintype J][DecidableEq J] : Continuous (@hermitianRay J) := by
  unfold hermitianRay; fun_prop

lemma entry_tendsto (L : Filter T)(S : T → Matrix J J ℂ) (A : Matrix J J ℂ)
    (h : ∀ i j,Tendsto (fun t ↦ S t i j) L (𝓝 (A i j))) : Tendsto S L (𝓝 A) := by
  exact (show Tendsto S L (𝓝 A) from tendsto_pi_nhds.mpr (fun i ↦ tendsto_pi_nhds.mpr (fun j ↦ h i j)))
lemma pe_identity (t:ℝ) : algebraMap ℝ (Matrix J J ℂ) t=(t:ℂ) • 1 := by
  rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rfl
private lemma peg_le {b d:ℝ}(t : b ≤ d) : (b:ℂ) • I₀ ≤ (d:ℂ) • I₀ := by
  have e: 0≤ (↑(d-b):ℂ):=by exact_mod_cast sub_nonneg.mpr t
  apply Matrix.le_iff.mpr
  rw [←sub_smul,←ofReal_sub]; exact Matrix.PosSemidef.one.smul e
lemma lower_stays (A B : Matrix J J ℂ) (b d : ℝ) (p : ReFloor A d)
    (v : ‖hermitianRay B-hermitianRay A‖ ≤ d-b) : ReFloor B b := by
  let X:= hermitianRay B-hermitianRay A
  have he : IsSelfAdjoint X:= (sunrise B).sub (sunrise A)
  have h: -(algebraMap ℝ (Matrix J J ℂ) ‖X‖) ≤ X:= he.neg_algebraMap_norm_le_self
  rw [pe_identity] at h; let C:= I₀
  unfold ReFloor
  calc
    (b:ℂ) • 1 = - (↑(d-b):ℂ) • C+(d:ℂ) • C := by rw [←add_smul]; congr 1; push_cast; ring
    _ ≤ -(↑‖X‖:ℂ) • C + (d:ℂ) • C := add_le_add_left (by rw [neg_smul,neg_smul]; exact neg_le_neg (peg_le v)) _
    _ = -((↑‖X‖:ℂ) • C) + (d:ℂ) • C := by rw [neg_smul]
    _ ≤ X + hermitianRay A:=add_le_add h p
    _ = _ := sub_add_cancel ..
lemma ReFloor.retain {A : Matrix J J ℂ} {b d : ℝ} (h : b<d) (p : ReFloor A d)
    (L : Filter T)(S : T → Matrix J J ℂ)(e : ∀ i j,Tendsto (fun t ↦ S t i j) L (𝓝 (A i j))) :
    ∀ᶠ t in L, ReFloor (S t) b := by
  have hu := (rays_cont (J:=J)).continuousAt.tendsto.comp (entry_tendsto L S A e)
  have hv : Tendsto (fun i ↦ ‖hermitianRay (S i)-hermitianRay A‖) L (𝓝 0):= by
    have ht := (hu.sub_const (hermitianRay A)).norm; simpa [sub_self] using ht
  filter_upwards [hv.eventually (gt_mem_nhds (sub_pos.mpr h))] with i w; exact lower_stays A _ _ _ p w.le
lemma ReFloor.diag {A : Matrix J J ℂ} {b : ℝ} (p : ReFloor A b) (i : J) : b ≤ (A i i).re := by
  have ht : 0 ≤ (hermitianRay A-(b:ℂ) • I₀) i i:= (Matrix.le_iff.mp p).diag_nonneg
  simp only [Complex.le_def, Complex.zero_re,Complex.zero_im,Matrix.star_eq_conjTranspose,conjTranspose_apply,
    hermitianRay,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq, Complex.add_re, Complex.sub_re,
    Complex.smul_re, RCLike.star_def, Complex.conj_re, Complex.ofReal_re,smul_eq_mul,mul_one] at ht
  linarith [ht.1]
end YM.MacroSix
#print axioms YM.MacroSix.lower_stays
