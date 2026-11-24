import YM.CF.Fir.Mountain
/-! A nonunitary block transformation preserving chirality. At flat links. L odd. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

def money (j:ℕ)(L:Side)(l:Site L)(p:Momentum): ℂ:= (((Real.sqrt L.val)⁻¹:ℝ):ℂ)*muff j L (aliasAt p l)
def sprig (j:ℕ)(L:Side)(p:Momentum): Stk L := col L (fun i=> money j L i p • 1)
def trident (L:Side)(p:Momentum): Stk L := ((L.val:ℂ)^2)⁻¹ • aliasBlock L SpinIdx p
lemma pointed (L: Side)(p:Momentum)(h:physical p): star (trident L p)*trident L p=1 ∧ trident L p*star (trident L p)=1 := by
  suffices hh: star (trident L p)*trident L p=1 by exact ⟨hh,mul_eq_one_comm.mp hh⟩
  have hb : star (aliasBlock L SpinIdx p)*aliasBlock L SpinIdx p=(L.val:ℂ)^4 • 1:=by
    have he:= straightens L SpinIdx p; unfold returned at he; rw [show star p=p from h] at he; exact he
  unfold trident; rw [star_smul,star_inv₀,star_pow,star_natCast,Matrix.mul_smul,Matrix.smul_mul,hb,smul_smul,smul_smul]; ring_nf; field_simp; simp
lemma trident_spike (j:ℕ)(L:Side)(p:Momentum): peb L*(trident L p)*sprig j L p=(((((L.val:ℂ)^2)⁻¹)*(∑ l, money j L l p)) : ℂ) • peb L:=by
  ext ⟨x,a⟩ ⟨y,b⟩; rw [mul_assoc]; simp only [s_app,c_app,sprig, Matrix.mul_apply,peb,spike, s_app,Fintype.sum_prod_type,St,trident,Matrix.smul_apply,aliasBlock,Matrix.of_apply]; by_cases he:x=0 <;> by_cases h:y=0 <;> simp [he,h,c_app,Matrix.one_apply,mul_ite,ite_mul, ← Finset.mul_sum] <;> try grind
-- earnings positivity on real cube
variable (j:ℕ)(L:Side)(hj:Even j)(ho:Odd L.val){p:Momentum}
include ho in
lemma money_real (l:Site L)(hp:physical p): star (money j L l p)=money j L l p:=by
  unfold money; rw [star_mul, muff_real j L ho _ (alias_real hp l)]; simp [mul_comm]
include hj ho in
lemma money_pos (hp:p∈realCube zone): 0 < (money j L 0 p).re :=by
  obtain ⟨r,hr⟩:=hj
  have he : ∀ i:Axis, plank L (narrow L p i)≠0:=by
    intro i; apply norm_pos_iff.mp; refine plankMin_pos.trans_le (plank_lower L _ ?_ ?_)
    · rw [narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos _).ne']; exact zone_in_disk _ (mem_cube_real hp zone_pos) _
    exact (physical_iff _).mp (na_phys L hp.1) i
  let x:=muff r L (narrow L p)
  have hx:x ≠0:=pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _=> he i)
  have hh : (money j L 0 p)=(((Real.sqrt L.val)⁻¹:ℝ):ℂ)*(‖x‖^2 : ℝ):=by
    unfold money; rw [hr,muff,alias_zero_eq,pow_add]; change _*(x*x)=_
    nth_rw 2 [← show star x=x from muff_real r L ho _ (na_phys L hp.1)]; rw [Complex.star_def,Complex.mul_conj,Complex.sq_norm]
  rw [hh]; norm_cast; exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (side_pos _))) (sq_pos_of_pos (norm_pos_iff.mpr hx))
include ho hj in
lemma money_earned (hp:p∈realCube zone): ∑ l, money j L l p≠0:=by
  have H: 0 < ∑ l, (money j L l p).re:=by
    refine sum_pos' ?_ ⟨0,Finset.mem_univ _,money_pos j L hj ho hp⟩
    intro l _; obtain ⟨r,hr⟩:=hj; unfold money; rw [hr,muff,pow_add]; -- analogous
    let x:=muff r L (aliasAt p l)
    change 0≤ ((↑_ : ℂ)*(x*x)).re
    have hh:x*x=((‖x‖^2:ℝ):ℂ):=by nth_rw 2 [← show star x=x from muff_real r L ho _ (alias_real hp.1 l)]; rw [Complex.star_def,Complex.mul_conj,Complex.sq_norm]
    rw [hh]; norm_cast; positivity
  intro H'; rw [← Complex.re_sum, H'] at H; exact lt_irrefl 0 H

def stackW (j:ℕ)(L:Side)(p:Momentum):Stk L:=sprig j L p+returned (trident L) p*(1-peb L)
include ho hj in
lemma lofty (hp:p∈realCube zone): IsUnit (stackW j L p):=by
  let Z:= trident L p; let R:= peb L; let T:=trident L p*sprig j L p; let c:= ((L.val:ℂ)^2)⁻¹*(∑ l, money j L l p)
  have hc:c≠0:=mul_ne_zero (inv_ne_zero (pow_ne_zero _ (side_ne _))) (money_earned _ _ hj ho hp)
  have hZ:= pointed L p hp.1
  have hpr : R*T=c • R:=(by unfold T R; rw [← mul_assoc]; exact trident_spike j L p)
  have ht:T*R=T:=by unfold T R; rw [mul_assoc, sprig,peb_col]
  have hr : R*R=R:=peb_sq _
  have hh : Z*stackW j L p=T+(1-R):=by rw [stackW,mul_add, ← mul_assoc,returned, show star p=p from hp.1]; change T+ (Z*star Z)*(1-R)=_; rw [show Z*star Z=1 from hZ.2,one_mul]
  suffices h:IsUnit (T+(1-R)) by rw [← hh] at h; exact isUnit_of_mul_isUnit_right h
  let J:= c⁻¹ • R - c⁻¹ • ((1-R)*T)+(1-R)
  have hz: (T+(1-R))*J=1:=by
    have hu:T*(1-R)=0:=by rw [mul_sub,ht,mul_one]; abel
    rw [show J=_ from (rfl:J=c⁻¹ • R-c⁻¹ • ((1-R)*T)+(1-R)),add_mul,mul_add,mul_sub,Matrix.mul_smul,Matrix.mul_smul,←mul_assoc T (1-R), hu,zero_mul]; simp only [J,smul_sub,inv_smul_smul₀ hc,add_zero, sub_zero, ht, smul_zero,mul_add,mul_sub,sub_mul, Matrix.mul_smul,one_mul,mul_one,hr,hpr]; abel
  exact (isUnit_iff_exists_inv).mpr ⟨J,hz⟩
end YM.CF.Fir
