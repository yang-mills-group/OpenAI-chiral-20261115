import GaugeFieldConstruction.ProductData
import YM.CF.Pec.Sorrel

/-!
# U1. Spin of the actual construction on B_i
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Function Matrix CF CF.Scroll CF.Spire
open scoped Matrix MatrixOrder BigOperators
namespace Cauchy

theorem same_charge (s : Signed) : signBit s= CF.Spire.detX s := by
  have hm (s r : Signed) (h : signBit s=detX s) (k : signBit r=detX r) :
      signBit (s*r) = detX (s*r) := by rw [signBit_mul,h,k,det_p]
  refine signed_induction (P := fun s => signBit s=detX s) (fun p => ?_) (fun i => by rw [det_t]; simp) hm s
  induction p using Equiv.Perm.swap_induction_on with
  | one => simp [det_i]
  | swap_mul σ i j u k =>
    rw [unsigned_mul]; apply hm _ _ ?_ k
    rw [signBit_swap i j u]; exact (CF.Pec.detSwap i j u).symm

abbrev M2 := Matrix Spin Spin ℂ
def band (b : Bool) (i : Spin) : SpinIdx := if b then Fin.natAdd 2 i else Fin.castAdd 2 i
def block (x : Op SpinIdx) (b c : Bool) : M2 := x.submatrix (band b) (band c)
def cliff (i : Axis) : M2 := Matrix.of (Hij i)

lemma product_block (x y : Op SpinIdx) (b c : Bool) :
    block (x*y) b c = block x b false * block y false c + block x b true * block y true c := by
  ext i j
  simp only [block,Matrix.add_apply,Matrix.mul_apply,Matrix.submatrix_apply]
  exact Fin.sum_univ_add (fun j' : Fin (2+2) => x (band b i) j' * y j' (band c j)) -- infer
lemma star_block (x : Op SpinIdx) (b c : Bool) : block (star x) b c=star (block x c b) := rfl
lemma unit_block (b : Bool) : block 1 b b=1 := by
  ext i j; cases b <;> fin_cases i <;> fin_cases j <;> rfl
lemma sign_block (x : Op SpinIdx) (b c d) : block (pay d x) b c=pay d (block x b c) := by
  cases d <;> rfl
lemma copy_block (b : Bool) : block grading b b=pay b 1 := by
  ext i j; cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.one_apply,band,block,grading] <;> rfl
lemma other_block (b : Bool) : block grading b (!b)=0 := by
  ext i j; cases b <;> fin_cases i <;> fin_cases j <;> rfl
lemma gamma_price (i : Axis) : block (gammaOp i) false true = cliff i := by
  ext a b; fin_cases i <;> fin_cases a <;> fin_cases b <;> rfl
lemma transpose_price (i : Axis) : block (CF.cc (gammaOp i)) true false=(cliff i).transpose := by
  ext a b
  change star (gammaOp i (band true a) (band false b))=(cliff i) b a
  change star (gammaOp i) (band false b) (band true a)=_
  rw [(gammaAdj i).star_eq,← gamma_price]; rfl

lemma unitary_of_block {x : CF.UNI SpinIdx} {b c : Bool} (h : block x b (!c)=0) :
    block x b c ∈ unitary M2 := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  have he := congr_arg (fun y : Op SpinIdx => block y b b) (show (x:Op SpinIdx)*star (x:Op SpinIdx)=1 from x.property.2)
  simp only [product_block,star_block,unit_block] at he
  cases c <;> simp at h <;> simpa [h] using he

variable {s : Signed} {b : Bool} {U : CF.UNI SpinIdx}
/-- Which blocks vanish for a chosen representative. The argument displacement
 s reads stamps of `JetS` with the inverse Shape. -/
lemma diagonal (h : JetS s⁻¹ b b U) (d : Bool) : block U d (!(d.xor b))=0 := by
  have he := h.grade
  have ht : U.val * windX b grading * star U.val = pay b grading := he
  have hg : windX b grading=grading := by
    ext i j; cases b; rfl
    change star (grading i j)=grading i j; fin_cases i <;> fin_cases j <;> simp [grading]
  rw [hg] at ht
  have hv := congr_arg (fun z => z*U.val) ht
  change U.val*grading*star U.val*U.val = pay b grading*U.val at hv
  rw [mul_assoc (U.val*grading),U.property.1,mul_one] at hv
  have eq := congr_arg (fun z=>block z d (!(d.xor b))) hv
  have sf : block grading false true = 0 := other_block false
  have st : block grading true false = 0 := other_block true
  simp only [product_block,sign_block] at eq
  cases b <;> cases d <;> simp [sf,st,copy_block] at eq ⊢
  -- eq : x= -x, across intended band
  all_goals ext i j
  all_goals
    have hl := Matrix.ext_iff.mpr eq i j; simp at hl
    rw [Matrix.zero_apply]
    first | linear_combination hl/2 | linear_combination -hl/2

lemma right_frame (h : JetS s⁻¹ b b U) (d : Bool) : block U d (d.xor b) ∈ unitary M2 :=
  unitary_of_block (diagonal h d)
/-- Upper-right block identity with determinant bit. `p=b=true` also does
 charge-conjugation. Its *ordinary transpose* on the H block matters. -/
lemma spin_transport (h : JetS s⁻¹ b b U) (i : Axis) :
    block U false b * (if b then (cliff i).transpose else cliff i) *
        star (block U true (!b)) = pay (s.flip i) (cliff (s.perm i)) := by
  have hp := h.cliff (s.perm i)
  simp only [Signed.inv_perm, Equiv.symm_apply_apply,Signed.inv_flip] at hp
  have he : U.val * windX b (gammaOp i) * star U.val = pay (s.flip i) (gammaOp (s.perm i)) := hp
  have hu := congr_arg (fun z=>block z false true) he
  simp only [product_block,star_block,sign_block,gamma_price] at hu
  have h₁ := diagonal h false; have h₂ := diagonal h true
  cases b <;> simp at h₁ h₂
  · simp [windX,gamma_price,h₁,h₂] at hu; exact hu
  simp [windX,transpose_price,h₁,h₂] at hu; exact hu
lemma payment (s : Signed) : ∃ U, JetS s⁻¹ (signBit s) (signBit s) U := by
  obtain ⟨U,h⟩ := CF.Spire.det_sub (signBit s) s⁻¹
  rw [← same_charge,signBit_inv] at h; exact ⟨U,h⟩
end Cauchy
end YM.GaugeFieldConstruction
