import YM.CF.Lattice.Linearized
/-! Discrete antiperiodic Fourier modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Lat
open scoped Matrix Matrix.Norms.L2Operator Topology Kronecker BigOperators
attribute [local instance] opCStarAlgebra
open BZ Lattice Finset
variable {N : Side}
lemma nPos (N:Side) : (0:ℝ) < N.val := by exact_mod_cast N.property

def winding (k : Per N) : ℝ := (2*k.val+1)/N.val*Real.pi
def principal (k : Per N) : ℝ := if winding k ≤ Real.pi then winding k else winding k - 2*Real.pi
lemma winding_bounds (k : Per N) : 0 < winding k ∧ winding k < 2 * Real.pi := by
  have he := nPos N; have ht : k.val+1 ≤ N.val := ZMod.val_lt k
  have hx : (k.val:ℝ)+1 ≤ N.val := by exact_mod_cast ht
  constructor
  · unfold winding; have hp := Real.pi_pos; positivity
  unfold winding
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  rw [div_lt_iff₀ he]; linarith
lemma inZone (k : Per N) : -Real.pi < principal k ∧ principal k ≤ Real.pi := by
  have hp := Real.pi_pos
  obtain ⟨h,g⟩ := winding_bounds k
  unfold principal; split <;> rename_i e
  · exact ⟨by linarith,e⟩
  constructor <;> linarith
lemma wind_eq (k : Per N) : phase (principal k)=phase (winding k) := by
  unfold principal; split
  · rfl
  unfold phase; push_cast
  rw [sub_mul, Complex.exp_sub,Complex.exp_two_pi_mul_I,div_one]
lemma wind_p (k : Per N) : phase (winding k)^N.val= -1 := by
  unfold phase winding
  push_cast
  have he : (N.val:ℂ)≠0 := by exact_mod_cast N.property.ne'
  rw [← Complex.exp_nat_mul]
  rw [show (N.val:ℂ)*(_*Complex.I)=(k.val:ℂ)*(2*Real.pi*Complex.I)+Real.pi*Complex.I by field_simp,
    Complex.exp_add,Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow,one_mul,Complex.exp_pi_mul_I]
lemma prin_nonzero (k : Per N) : principal k≠0 := by
  have he := wind_p k
  rw [← wind_eq] at he; intro h; rw [h,phase] at he; norm_num at he
lemma prin_inj (k l:Per N) (h : principal k=principal l) : k=l := by
  have he : winding k=winding l := by
    obtain ⟨hp,hq⟩ := winding_bounds k; obtain ⟨hm,hh⟩ := winding_bounds l
    unfold principal at h; split_ifs at h <;> linarith
  unfold winding at he
  have hx := (div_left_inj' (nPos N).ne').mp (mul_right_cancel₀ Real.pi_pos.ne' he)
  have hval : k.val=l.val := by
    have h : (k.val:ℝ)=l.val := by linarith
    exact_mod_cast h
  rw [← ZMod.natCast_zmod_val k,← ZMod.natCast_zmod_val l,hval]
lemma phase_inj (k l : Per N) (h : phase (principal k)=phase (principal l)) : k=l := by
  apply prin_inj
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi ?_ ?_ ?_ ?_ h -- inferred? h def
  · simpa using congrArg Complex.im he
  · simpa using (inZone k).1
  · simpa using (inZone k).2
  · simpa using (inZone l).1
  simpa using (inZone l).2

def pm (k : Site N) : Mom := principal ∘ k
lemma pm_zone (k : Site N) : Zone (pm k) := fun i => inZone (k i)
lemma pm_nonzero (k : Site N) : pm k ≠ 0 := fun h => prin_nonzero (k 0) (congrFun h 0)

-- standard seam at last positive link.
def anticut (N : Side) : Site N := fun _ => -1
def frequency (k x : Site N) := ∏ i, phase (pm k i)^(x i).val
lemma frequency_hop (k x : Site N) (i : Axis) :
    seam (anticut N) x i * frequency k (x+step i)=frequency k x * phase (pm k i) := by
  have hh : ∏ j∈univ.erase i, phase (pm k j)^((x+step i:Site N) j).val =
      ∏ j∈univ.erase i, phase (pm k j)^(x j).val := by
    apply prod_congr rfl; intro j hj; simp [(mem_erase.mp hj).1]
  unfold frequency
  rw [← mul_prod_erase _ _ (mem_univ i),hh,← mul_prod_erase _ (fun j => phase (pm k j)^(x j).val) (mem_univ i)] -- check
  simp only [seam,anticut,Pi.add_apply,step_apply,ite_true]
  split <;> rename_i e
  · rw [e]; simp only [neg_add_cancel,ZMod.val_zero,pow_zero,_root_.one_mul]
    rw [mul_right_comm]
    rw [show phase (pm k i) ^ ZMod.val (-1 : Per N) * phase (pm k i)= -1 by
      rw [← pow_succ]
      have h : ZMod.val (-1 : Per N)+1=N.val := by
        clear * - N; rcases N with ⟨N,H⟩; cases N
        · cases H
        · exact congrArg (·+1) (ZMod.val_neg_one _)
      rw [h]; change phase (principal _)^_=_; rw [wind_eq,wind_p]]
  rw [one_mul,mul_right_comm]
  congr 1
  rw [← pow_succ]; congr 1
  have hz := ZMod.val_lt (x i)
  have hw : (x i).val+1<N.val := Nat.lt_of_le_of_ne (by omega) <| fun H => e (by
    rw [eq_neg_iff_add_eq_zero, ← ZMod.natCast_zmod_val (x i), ← Nat.cast_one (R:=Per N), ← Nat.cast_add,H,ZMod.natCast_self])
  have he : ZMod.val (1:Per N)=1 := by rw [← Nat.cast_one,ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [ZMod.val_add_of_lt (by rwa [he]), he]
lemma frequency_unit (k x : Site N) : star (frequency k x)*frequency k x=1 := by
  unfold frequency; rw [star_prod,← prod_mul_distrib]
  apply prod_eq_one; intro i _
  rw [star_pow, ← mul_pow,mul_comm,phase_one,one_pow]
end YM.CF.Lat
