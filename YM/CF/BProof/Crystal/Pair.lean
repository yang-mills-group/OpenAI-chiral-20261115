import YM.CF.BProof.Crystal.Alph
/-! Edge allocations: put creation-pairs with strictly lower letter addressed
once into a commutative even formal Dough. Duplicate partners then give zero, and the
corner enforces every matching test, retaining signs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]
def cell(i j:I): Dough I:= ⟨put i*put j,Flour.putPut _ (mem_univ _) (mem_univ _)⟩
lemma cell_money(i j:I): ‖cell i j‖≤1:=(norm_mul_le ..).trans (mul_le_one₀ (payPut i) (norm_nonneg (put j)) (payPut j)) -- tune Normed lines
lemma cell_nil(i j k:I): cell i j*cell i k=0:=Subtype.ext (show put i*put j*(put i * put k)=0 from (by rw [←mul_assoc, ←put_even i i j,←mul_assoc,put_sq,zero_mul,zero_mul]))
def floss (C:Op I)(i:I):Dough I := ∑ j:I, if i<j then hollow (star (C i j))*cell i j else 0
lemma hollow_face(c:ℂ)(A:Dough I): (hollow c * A).val=c • A.val:=by change c • (1:FC I) *_=_; rw [Algebra.smul_mul_assoc,one_mul]
abbrev pour (A:Dough I):= A.val

lemma strand_nil(C:Op I)(i:I): floss C i ^2=0:=by
 unfold floss; rw [pow_two]; simp_rw [sum_mul,mul_sum]; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro k _; split_ifs <;> first|simp [mul_mul_mul_comm _ (cell i j) _ _,cell_nil]
lemma milk(C:Op I)(i:I): exp (floss C i)=1+floss C i:=by
 rw [exp_eq_tsum ℝ]; dsimp only; rw [tsum_eq_sum (s:=range 2)]; norm_num [Finset.sum_range_succ]; intro j hj; rw [mem_range] at hj; rw [pow_eq_zero_of_le (not_lt.mp hj) (strand_nil C i), smul_zero]
def top (S:Finset I)(C:Op I): Op I:= Matrix.of (fun i j=>if min i j ∈ S then C i j else 0)
lemma top_skew {C:Op I}(h:Cᵀ= -C)(S:Finset I): (top S C)ᵀ= -top S C:=by ext i j; have ht:=Matrix.ext_iff.mpr h i j; simp only [Matrix.transpose_apply,top,Matrix.of_apply, Matrix.neg_apply,min_comm j i] at *; rw [ht]; split<;> simp
lemma angled(C:Op I)(h:Cᵀ= -C) : (∑ i,floss C i).val=coupl (cc C):=by
 change (Dough I).val (∑ i,floss C i)=_; unfold coupl squareP floss; rw [map_sum]; simp_rw [map_sum,apply_ite _ _,map_zero]; let P(i j:I):=star (C i j) • (put i * put j); have ht(i j:I):(Dough I).val (hollow (star (C i j))*cell i j)= P i j:=hollow_face ..
 have he(i j:I):P i j=P j i:=by unfold P; rw [show C j i= -C i j from Matrix.ext_iff.mpr h i j,star_neg,show put j*put i= -(put i*put j) from eq_neg_of_add_eq_zero_left (put_put j i), neg_smul,smul_neg,neg_neg]
 let U:= ∑ i:I, ∑ j:I, if i<j then P i j else 0; have hh: ∑ i:I,∑ j:I, (cc C) i j • (put i*put j)=U+U:=by
    let V(i j:I): FC I:= if i<j then P i j else 0; conv_rhs=> arg 2; rw [show U=∑ j:I,∑ i:I,V i j from sum_comm]
    unfold U; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; rw [←sum_add_distrib]; apply sum_congr rfl; intro j _; unfold V; rw [he j i]; change P i j= _; rcases lt_trichotomy i j with p|p|p; simp [p,not_lt.mpr p.le]; subst j; simp [P,put_sq]; simp [p,not_lt.mpr p.le]
 simp_rw [hh,ht,smul_add]; rw [←add_smul,show (2:ℂ)⁻¹+2⁻¹=1 from (by norm_num),one_smul]
lemma floss_top(C:Op I)(i:I)(s:Finset I): floss (top s C) i= if i∈s then floss C i else 0:=by
 by_cases g:i∈ s; rw [if_pos g]; unfold floss; apply sum_congr rfl; intro j _; split; rw [top,Matrix.of_apply,min_eq_left (by order),if_pos g]; rfl
 rw [if_neg g]; apply sum_eq_zero; intro j _; split; rw [top,Matrix.of_apply,min_eq_left (by order),if_neg g,star_zero, show hollow (n:=I) 0=0 from Subtype.ext (zero_smul ..),zero_mul]; rfl
lemma spool(C:Op I)(V:Finset I)(x:Cᵀ= -C): pairWave (cc (top V C))= acts ((∏ i∈V,(1+floss C i)).val) (vacuum I):=by
 let D:=Dough I; letI : NormedAlgebra ℚ (Dough I):= NormedAlgebra.restrictScalars ℚ ℝ (Dough I); letI : NormedAlgebra ℚ (FC I):= NormedAlgebra.restrictScalars ℚ ℝ (FC I)
 rw [←stored,←angled _ (top_skew x V)]; change acts (exp ((Dough I).val _)) _=_; rw [←map_exp (Dough I).val (show Continuous _ from continuous_subtype_val), show ∑ i,floss (top V C) i=∑ i∈V,floss C i from (by simp_rw [floss_top]; rw [← sum_filter,filter_mem_eq_inter,univ_inter]), exp_sum]; simp_rw [milk]; rfl -- tune
lemma quantLake(s:Finset I)(C:Op I): acts (quant (cutM s)) (pairWave (cc (top s C)))=acts (quant (cutM s)) (pairWave (cc C)):=by
 rw [pair_cov,pair_cov,self_t]; congr 1; change Garden.square s _=Garden.square s _; ext i j; simp only [square_entry,cc_apply,Matrix.of_apply]; split; rename_i p; · have h:= p.1; have k:= p.2; unfold top; rcases le_total i j with v|v; rw [Matrix.of_apply,min_eq_left v,if_pos h]; rw [Matrix.of_apply,min_eq_right v, if_pos k]
 rfl
lemma glance(s:Finset I)(C:Op I){y:Wave I}(t:zone s y): inner ℂ (pairWave (cc C)) y= inner ℂ (pairWave (cc (top s C))) y:=by
 let P:=quant (cutM s); have hp:star P=P:=by unfold P; rw [quantCut,(cutM_idp _).isSelfAdjoint]
 have he : acts P y=y:=by unfold P; rw [quantCut]; apply PiLp.ext; intro i; rw [cut_apply]; split; rfl; rename_i g; exact (t i (fun h=>g (mem_powerset.mpr h))).symm
 rw [←he,←act_inner,←act_inner,hp,quantLake]; -- tune
end YM.CF.BProof.Crystal
