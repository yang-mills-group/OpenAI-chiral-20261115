import YM.SU5.May.FloeBasis
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable (N : Side)
abbrev Flap (N : Side) := Axis→Fin N.val
noncomputable def trem (k:Flap N) : Cover:=fun i=> ((k i).val:ℤ)-mid N
abbrev Trace (j:ℕ)(N: Side):=Fin j→ Flap N
noncomputable def traces (j:ℕ)(k:Trace j N): Cover:= ∑ i:Fin j,trem N (k i)
variable {α β γ:Type*}
-- uniform real weight; throughout no complex off-model bias
abbrev mite (α:Type*)[Fintype α]:ℝ:=(Fintype.card α:ℝ)⁻¹
def expected [Fintype α](f:α→ℂ):ℂ:= (mite α:ℂ) * ∑ i:α,f i
lemma mite_p (α:Type*)[Nonempty α][Fintype α]: 0 < mite α:= inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
lemma expected_reprice [Fintype α][Fintype β](E:α ≃ β) (f:β→ℂ): expected (f ∘ E) = expected f:=by unfold expected mite; simp only [Function.comp_apply]; rw [Fintype.card_congr E, (E.sum_comp f)]
@[simp] lemma expected_unit [Fintype α][Nonempty α](c:ℂ): expected (fun _ : α=> c)=c:=by simp only [expected,mite, Complex.ofReal_inv, Complex.ofReal_natCast,sum_const,nsmul_eq_mul,card_univ]; rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_mul]
lemma expected_sum [Fintype α](s:Finset β)(f:β→α→ℂ): expected (fun i=>∑ j∈s,f j i)=∑ j∈s,expected (f j):=by simp_rw [expected]; rw [sum_comm,mul_sum]
lemma expected_neg [Fintype α](f:α→ℂ): expected (fun a=> -f a) = - expected f:=by simp [expected]
lemma expected_mul [Fintype α](c:ℂ)(f:α→ℂ): expected (fun a=> c*f a) = c * expected f:=by unfold expected; rw [←mul_sum,mul_left_comm]
lemma expected_mulRight [Fintype α](c:ℂ)(f:α→ℂ): expected (fun a=> f a * c) = expected f * c:=by unfold expected; rw [←sum_mul,mul_assoc]
lemma expected_star [Fintype α](f:α→ℂ): expected (fun a=>star (f a))=star (expected f):=by rw [expected,expected,star_mul',star_sum]; simp
lemma expected_pow (j:ℕ)[Fintype α](f:α→ℂ): expected (fun k:Fin j→α=> ∏ i:Fin j,f (k i))= expected f ^ j:=by
 unfold expected mite; rw [← Fintype.prod_sum (fun _:Fin j=> f)]; push_cast; simp [mul_pow] -- tune inv_pow
lemma expected_diff_le [Fintype α][Nonempty α](x y:α→ℂ)(u:ℝ)(h:∀ k,‖x k-y k‖ ≤ u): ‖expected x-expected y‖ ≤ u:=by
 unfold expected; rw [←mul_sub,norm_mul, ← sum_sub_distrib]; rw [Complex.norm_real, Real.norm_of_nonneg (mite_p α).le]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i (_:i∈univ)=>h i))) (mite_p α).le); simp only [mite,sum_const,card_univ, nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ (show (Fintype.card α:ℝ) ≠ 0 from by exact_mod_cast Fintype.card_ne_zero),one_mul,le_refl] -- tune
lemma habit [Fintype α][Fintype β](u:α→β→ℂ): expected (fun s=>expected (u s))= expected (fun t=> expected (fun s=>u s t)):=by
 simp_rw [expected,←mul_sum,mul_left_comm ((mite α:ℝ):ℂ)]; rw [sum_comm] -- tune
lemma average (p: Momentum): expected (fun x:Flap N=> mode p (trem N x)) = ∏ i:Axis, plank N (p i):=by
 let f (i:Axis)(n:Fin N.val):= twirl (p i) ((n.val:ℤ)-mid N)
 have he(a:Axis→ Fin N.val): mode p (trem N a)=∏ i,f i (a i):=by
    unfold mode; rw [Finset.mul_sum,Complex.exp_sum]; refine Finset.prod_congr rfl fun i _=>?_ ; unfold f twirl; change Complex.exp (Complex.I*(p i * ↑(((a i).val:ℤ)-mid N)))=_; congr 1; ring
 unfold expected; simp_rw [he]; rw [← Fintype.prod_sum f]
 have hh(i:Axis): plank N (p i)=(N.val:ℂ)⁻¹ *∑ j: Fin N.val, f i j:=by rw [plank_centers]; exact congr_arg ((N.val:ℂ)⁻¹*·) (Fin.sum_univ_eq_sum_range (fun n=> twirl (p i) ((n:ℤ)-mid N)) N.val).symm
 simp_rw [hh,Finset.prod_mul_distrib]; simp [mite,Flap,Nat.cast_pow]
lemma weight_pose (p:Momentum)(j:ℕ): muff j N p= expected (fun c:Trace j N=> mode p (traces N j c)):=by
 have he (c:Trace j N)(s:Finset (Fin j)): mode p (∑ i∈s,trem N (c i))=∏ i∈s,mode p (trem N (c i)):=by induction s using Finset.induction_on with|empty=>simp|insert a s h ih=>rw [Finset.sum_insert h,mode_shift,ih, Finset.prod_insert h]
 simp_rw [traces,he]; rw [expected_pow (α:=Flap N) j (fun i=> mode p (trem N i)), average]; rfl
lemma weight_neg (p:Momentum)(h:Odd N.val)(j:ℕ) : muff j N p=expected (fun c:Trace j N=>mode p (-traces N j c)):=by
 rw [←muff_even j N h p,weight_pose]; apply congrArg; funext c; unfold mode; simp
lemma trem_extent (p:Odd N.val)(k: Flap N)(i:Axis): -mid N ≤ trem N k i ∧ trem N k i ≤ mid N:=by
 have he:=mid_double N p; have hp:=(k i).isLt; change _ ≤ (↑(k i).val:ℤ)-mid N ∧ (↑(k i).val:ℤ)-mid N≤_; omega
lemma trace_extent (p:Odd N.val)(j:ℕ)(k:Trace j N)(i:Axis): -(j:ℤ)*mid N ≤ traces N j k i ∧ traces N j k i ≤ (j:ℤ)*mid N:=by obtain t:=fun l=> trem_extent N p (k l) i; rw [traces,Finset.sum_apply]; refine ⟨le_trans (le_of_eq ?_) (sum_le_sum (fun l _=>(t l).1)), le_trans (sum_le_sum (fun l _=>(t l).2)) (le_of_eq ?_)⟩ <;> simp [nsmul_eq_mul]
def point (N:Side)(x:Cover)(c:Cover): Cover:= N.val • x + offset N + c
lemma point_cost (p:Odd N.val)(x:Cover)(c:Cover)(i:Axis): (2 * (point N x c i)+1:ℤ) = N.val * (2*x i+1) + 2*c i:=by
 have h:=mid_double N p; simp only [point,offset,Pi.add_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply]; linarith
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.trace_extent
#print axioms YM.CF.May.Floe.weight_pose
