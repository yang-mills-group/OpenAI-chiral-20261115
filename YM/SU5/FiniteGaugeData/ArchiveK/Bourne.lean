import YM.SU5.FiniteGaugeData.ArchiveK.Lorica
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open Set MeasureTheory.Measure
/- spectral compact mollifier -/
variable (i:Axis)(x y:E4) (p:Momentum)
abbrev ReelK:= Axis×Fin 8
abbrev Brio:=ReelK→ℝ
def iceQ:= MeasureTheory.volume.restrict (Set.Ioc (-(1:ℝ)/2) (1/2))
lemma ice_prob:IsProbabilityMeasure iceQ:=⟨by rw [iceQ,Measure.restrict_apply_univ]; rw [Real.volume_Ioc]; norm_num⟩
attribute [local instance] ice_prob
def lintZ : Measure Brio:= Measure.pi (fun _=> iceQ)
lemma lint_prob:IsProbabilityMeasure lintZ:=by unfold lintZ; infer_instance
attribute [local instance] lint_prob
def foamQ(u:Brio):E4:=∑ i:ReelK,u i • YM.basis i.1
@[fun_prop] lemma foam_cont : Continuous foamQ:=by unfold foamQ; fun_prop
def rise (p:Momentum)(x:E4):ℂ:= Complex.exp (Complex.I * ∑ i:Axis,p i*x i)
@[simp] lemma rise_add : rise p (x+y)=rise p x * rise p y:=by unfold rise; push_cast; simp [Finset.sum_add_distrib,mul_add,Complex.exp_add]
lemma rise_real : rise (brushQ x) y=coastE (inner ℝ x y):=by rw [pis]; unfold rise coastE; push_cast; rfl
lemma tee (z:ℂ): ∫ x:ℝ, Complex.exp ((Complex.I*z)*x)∂iceQ=hsinc (z/2):=by
 by_cases p:z=0; · subst z; simp [hzero]
 unfold iceQ; rw [←intervalIntegral.integral_of_le (by norm_num : -(1:ℝ)/2 ≤1/2), integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero p), haway _ (div_ne_zero p (by norm_num))]; unfold Complex.sin; push_cast; rw [show I*z*(1/2)=z/2*I from (by ring),show I*z*(-1/2)= -(z/2)* I from (by ring)]; field_simp; ring_nf; simp [sub_eq_add_neg]
lemma rise_pi : ∀ u:Brio,rise p (foamQ u)= ∏ i: ReelK, Complex.exp ((Complex.I*p i.1)*u i):=by
 intro u; unfold rise foamQ; simp_rw [WithLp.ofLp_sum, Finset.sum_apply,PiLp.smul_apply]; push_cast; simp_rw [mul_sum]; rw [Finset.sum_comm]; rw [Complex.exp_sum]; apply Finset.prod_congr rfl; intro i _; simp [mul_comm, mul_left_comm, YM.basis_eq, mul_ite,apply_ite (Complex.ofReal : ℝ→ℂ)] -- tune
lemma marrow : ∫ u:Brio,rise p (foamQ u) ∂lintZ=leer p ^ 8:=by
 unfold lintZ; simp_rw [rise_pi]; rw [integral_fintype_prod_eq_prod (f:=fun i:ReelK=> fun x:ℝ=> Complex.exp ((Complex.I*p i.1)*x))]; simp_rw [tee]; rw [Fintype.prod_prod_type]; simp_rw [Largo.leer]; simp only [prod_const,card_univ,Fintype.card_fin]; rw [Finset.prod_pow]; -- tune orientations
@[fun_prop] lemma rise_safe : Continuous (uncurry rise):=by unfold uncurry rise; fun_prop
lemma lint_cost : ∀ᵐ v ∂lintZ, ‖foamQ v‖≤ 20:= by
 let S:=Set.Ioc (-(1:ℝ)/2) (1/2); have he:∀ᵐ u ∂lintZ,∀ i:ReelK, u i∈S:=by
    rw [ae_all_iff]; intro i; exact (Measure.tendsto_eval_ae_ae (μ:=fun _=>iceQ) (i:=i) (α := fun _:ReelK=>ℝ)) |>.eventually (ae_restrict_mem measurableSet_Ioc) -- tune
 filter_upwards [he] with v h; unfold foamQ; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i:ReelK=> (1:ℝ)/2) (fun i p=>?_)).trans (by norm_num [ReelK,Axis]))
 rw [norm_smul,Real.norm_eq_abs,YM.basis_norm,mul_one]; rw [abs_le]; exact ⟨by rw [← neg_div]; exact (h i).1.le,(h i).2⟩
#print axioms marrow
end YM.CF.Window.ArchiveK
