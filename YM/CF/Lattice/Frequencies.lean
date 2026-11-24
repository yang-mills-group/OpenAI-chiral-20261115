import YM.CF.Lattice.Anti

/-! Actual discrete Fourier matrix in these spin conventions. At trivial gauge.
One momentum for each lattice site (including on the even refined sublattice when used).
We'll bundle the endpoint so invertibility test covers *all* modes. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Lat
open Lattice BZ
open Finset
open scoped MatrixOrder Matrix.Norms.L2Operator Matrix Topology BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}

lemma distinct_freq {k l:Site N} (h : k≠l) : ∑ x:Site N, star (frequency k x)*frequency l x=0 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  have hv := Equiv.sum_comp (advance i) (fun x => star (frequency k x)*frequency l x)
  let X := ∑ x:Site N, star (frequency k x)*frequency l x
  let z := phase (pm k i); let w := phase (pm l i)
  have he (x: Site N) : star (frequency k (advance i x))*frequency l (advance i x)=
      (star z*w)*(star (frequency k x)*frequency l x) := by
    have hs : star (seam (anticut N) x i)*seam (anticut N) x i=1 := by unfold seam; split <;> simp
    rw [show star (frequency k (advance i x))*frequency l (advance i x) =
          star (seam (anticut N) x i*frequency k (x+step i))*(seam (anticut N) x i*frequency l (x+step i)) by
        rw [star_mul, ← mul_assoc, mul_assoc _ (star (seam _ _ _)),hs,mul_one]; rfl]
    rw [frequency_hop, frequency_hop, star_mul]; dsimp only [z,w]; ring
  simp only [he, ← mul_sum] at hv
  by_contra H
  have hx : star z*w=1 := mul_right_cancel₀ (show X≠0 from H) (by rw [one_mul]; exact hv)
  have ha : (star z*w)*z=z := by rw [hx,one_mul]
  rw [show star z*w*z=(z*star z)*w by ring, show z*star z=1 from phase_one _,one_mul] at ha
  exact hi (phase_inj (k i) (l i) ha.symm)

def normF (N:Side) : ℂ := (N.val:ℂ)^2
lemma normF_ne (N) : normF N≠0 := pow_ne_zero _ (by exact_mod_cast N.property.ne')
def Fourier (N:Side) : Op (Site N) := Matrix.of fun x k => frequency k x / normF N
lemma fourier_mem (N) : Fourier N ∈ unitary (Op (Site N)) := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_apply, Fourier, Matrix.of_apply,star_div₀]
  have hn : star (normF N) = normF N := by simp [normF]
  simp only [hn,div_mul_div_comm, ← Finset.sum_div]
  by_cases h:x=y
  · rw [h]; simp only [frequency_unit, sum_const, card_univ, site_card, Matrix.one_apply_eq]
    rw [div_eq_iff (mul_ne_zero (normF_ne _) (normF_ne _)), nsmul_eq_mul, Nat.cast_pow]; unfold normF; ring
  rw [distinct_freq h,zero_div]; exact (Matrix.one_apply_ne h).symm

variable {n : Type*} [Fintype n] [DecidableEq n]
def bands (n : Type*) [Fintype n] [DecidableEq n] (F : Site N → Op SpinIdx) : Op (Tx N n) :=
  jump (Equiv.refl _) (fun k=> F k ⊗ₖ 1)
variable (n)
lemma bands_mul (F G : Site N → Op SpinIdx) : bands n (F*G)=bands n F*bands n G := by
  simp [bands,jump_mul,op_kron_mul]
lemma bands_add (F G : Site N → Op SpinIdx) : bands n (F+G)=bands n F+bands n G := by
  dsimp only [bands]; rw [← jump_add]; simp only [Pi.add_apply,Matrix.add_kronecker]; rfl
lemma bands_sub (F G : Site N → Op SpinIdx) : bands n (F-G)=bands n F-bands n G := by
  rw [sub_eq_add_neg, bands_add,sub_eq_add_neg]; unfold bands; simp only [← jump_neg,Pi.neg_apply,op_kron_neg]
lemma bands_one : bands n (fun _ : Site N => 1)=1 := by
  simp only [bands,Matrix.one_kronecker_one,jump_id]
lemma bands_smul (c:ℝ) (F : Site N → Op SpinIdx) : bands n (c • F)=c • bands n F := by
  ext ⟨x,i,a⟩ ⟨y,j,b⟩
  by_cases h:x=y
  · subst y; simp [bands,jump_apply]; rw [mul_assoc]
  simp [h,bands,jump_apply]
def bandMap : (Site N → Op SpinIdx) →ₗ[ℝ] Op (Tx N n) :=
  { toFun:=bands n, map_add' := bands_add n,map_smul' := bands_smul n }
def spatialU (N : Side) (n : Type*) [Fintype n] [DecidableEq n] : UNI (Tx N n) :=
  ⟨Fourier N ⊗ₖ 1, Matrix.kronecker_mem_unitary (fourier_mem N) (unitary _).one_mem⟩
lemma rowBlock {m : Type*} (J : Site N → Op (SpinIdx × n)) (f : Equiv.Perm (Site N))
    (B : Matrix (Tx N n) m ℂ) (x i y) : (jump f J * B) (x,i) y = ∑ j,J x i j * B (f x,j) y := by
  simp only [Matrix.mul_apply, Tx,Fintype.sum_prod_type, jump_apply, ite_mul]
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro a _ h; simp [Ne.symm h]
  simp
lemma colBlock {m : Type*} (J : Site N → Op (SpinIdx × n)) (B : Matrix m (Tx N n) ℂ) (x i y) :
    (B * jump (Equiv.refl _) J) x (y,i) = ∑ j, B x (y,j)*J y j i := by
  simp only [Matrix.mul_apply, Tx,Fintype.sum_prod_type, jump_apply, mul_ite,Equiv.refl_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro a _ h; simp [h]
  simp
lemma eq_twist (A B:Op (Tx N n)) (U:UNI (Tx N n)) (h : A * U.val= U.val * B) : A=twist U B := by
  rw [twist_formula,← h,mul_assoc, show U.val*star U.val=1 from U.property.2,mul_one]
lemma twist_bands_spin (A : Op SpinIdx) : spin N n A= twist (spatialU N n) (bands n (fun _ => A)) := by
  apply eq_twist
  ext ⟨x,i,a⟩ ⟨y,j,b⟩
  rw [spin,rowBlock,bands,colBlock]; change ∑ _, _ = ∑ _, _
  simp only [spatialU,Equiv.refl_apply]
  -- offsite Fourier scalar pulled both sides
  simp [Matrix.one_apply, mul_ite, ite_mul,mul_comm]

variable {n}
lemma HF (x y : Site N) (i : Axis) : seam (anticut N) x i * Fourier N (advance i x) y = Fourier N x y * phase (pm y i) := by
  simp only [Fourier, advance, Matrix.of_apply, Equiv.coe_fn_mk]
  exact Eq.trans (mul_div_assoc _ _ _).symm (Eq.trans (congrArg (· / normF N) (frequency_hop y x i)) (mul_div_right_comm ..))

lemma twist_bands_shift {K : Type*} [Group K] (R : K →* UNI n) (i : Axis) : shift R (1:RLink N K) (anticut N) i=
    twist (spatialU N n) (bands n (fun k => (atom (pm k)).T i)) := by
  apply eq_twist
  ext ⟨x,a⟩ ⟨y,b⟩
  rw [shift,rowBlock,bands,colBlock]
  simp only [hop, color,Pi.one_apply,map_one, show ((1:UNI n): Op n)=1 from rfl,Matrix.one_kronecker_one]
  -- simplify using spin one
  simp only [spatialU, BZ.atom, Matrix.smul_kronecker, Matrix.one_kronecker_one]
  -- sum must collapse
  simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, ite_mul,mul_zero,zero_mul,mul_one, Finset.sum_ite_eq', Finset.mem_univ,ite_true]
  by_cases h:a=b
  swap
  · simp only [h, ite_false]
  rw [if_pos h,if_pos h]
  exact HF x y i
end YM.CF.Lat
