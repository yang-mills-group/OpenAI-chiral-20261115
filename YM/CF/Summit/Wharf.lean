import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Teller
/-! Physical Gaussian substitution. Linear part in active-link variables.
Compress by windows, using positive gap on principals. No symmetrizing: use
compressed columns. Integral is over a compact interval for true inverse-root,
at each principal. Avoids squaring microscale radii when assigning primitive
support of the whitened white noises. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Summit
open Function Filter Set Matrix MeasureTheory FreeResolvent TestD AnalyticBridge.RelativeLogdet Unitary
open   Next.SectorChange.Schur (principal)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
abbrev Isle:= Ink.interval
def wind (z x:ℝ):=(1-x)^2*z+x^2
lemma wind_pos {z:ℝ}(p:0<z)(x:ℝ): 0 < wind z x:=by
 by_cases h:x=0; · simpa [wind,h]
 simpa only [wind] using add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) p.le) (sq_pos_of_ne_zero h)
lemma tonic {z:ℝ}(p:0<z) : IntegrableOn (fun x=>(wind z x)⁻¹) Isle ∧ (∫ x in Isle,(wind z x)⁻¹)= Real.pi / (2*Real.sqrt z):=by
 let r:= Real.sqrt z; have hr :0<r:= Real.sqrt_pos.2 p; have ht:= Real.sq_sqrt p.le
 have hv (x:ℝ): 0<wind z x:= wind_pos p x; let q(x:ℝ):=(x*(1+z)-z)/r
 let g x:= Real.arctan (q x)/r
 have h(x:ℝ) : HasDerivAt g ((wind z x)⁻¹) x:=by
    have h1 : HasDerivAt q ((1+z)/r) x:=by simpa using ((((hasDerivAt_id' x).mul_const (1+z)).sub_const z).div_const r)
    have h2:= (h1.arctan).div_const r
    convert! h2 using 1

    unfold q; have hx := hv x; unfold wind at hx ⊢
    change r^2=z at ht
    field_simp
    rw [ht]; ring
 have he : ContinuousOn (fun x=>(wind z x)⁻¹) Isle:= Continuous.continuousOn ((Continuous.inv₀ (by unfold wind; fun_prop) (fun x=> (hv x).ne')))
 refine ⟨he.integrableOn_Icc,?_⟩; unfold Isle Ink.interval
 rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i _=> h i) (he.intervalIntegrable_of_Icc zero_le_one)]
 have hl:r^2=z:=ht
 unfold g; rw [show q 1=r⁻¹ from by unfold q; ring_nf, show q 0=-r from by unfold q; rw [div_eq_iff hr.ne']; nlinarith]
 rw [Real.arctan_neg, Real.arctan_inv_of_pos hr]; unfold r; ring
def spanX {ι:Type}[DecidableEq ι](A:Square ι)(x:ℝ): Square ι:= (1-x)^2 • A+x^2 • (1:Square ι)
def glassX {ι:Type}[Fintype ι][DecidableEq ι](A:Square ι): Square ι:= Matrix.of fun i j=> ∫ x in Isle,(spanX A x)⁻¹ i j
def shard {ι:Type}[Fintype ι][DecidableEq ι](A:Square ι):= (2/Real.pi) • glassX A
variable {ι:Type}[Fintype ι][DecidableEq ι]{A:Square ι}
lemma shard_ideal (p:A.PosDef) : shard A=conjStarAlgAut ℝ _ p.1.eigenvectorUnitary (diagonal fun i=>(Real.sqrt (p.1.eigenvalues i))⁻¹):=by
 let F:= p.1.eigenvalues; let U:=p.1.eigenvectorUnitary; let B:= conjStarAlgAut ℝ _ U
 have h : A=B (diagonal F):= p.1.spectral_theorem
 have hr i:0<F i:= p.eigenvalues_pos i
 have ht x:(spanX A x)⁻¹=B (diagonal fun i=>(wind (F i) x)⁻¹):=by
    apply Matrix.inv_eq_right_inv; rw [show spanX A x=B (diagonal fun i=> wind (F i) x) from ?_,← map_mul]
    · rw [diagonal_mul_diagonal,show (fun i : ι =>wind (F i) x*(wind (F i) x)⁻¹)=fun _=>1 from funext fun i=>mul_inv_cancel₀ (wind_pos (hr _) _).ne',diagonal_one,map_one]
    unfold spanX; rw [h, show (1:Square ι) = B (1:Square ι) from (map_one _).symm]
    rw [← map_smul,← map_smul, ← map_add]; apply congrArg; ext i j; by_cases i=j <;> simp [*,Matrix.diagonal,wind]
 ext i j; unfold shard glassX; simp_rw [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ht]; unfold B
 simp_rw [conjugate_entry]; rw [integral_finsetSum _ fun l _=> ((tonic (hr l)).1).const_mul _, Finset.mul_sum]
 refine Finset.sum_congr rfl fun k _=>?_
 rw [integral_const_mul,(tonic (hr k)).2]; unfold U F
 field_simp [Real.pi_pos.ne']
lemma shard_unit (p:A.PosDef): (shard A).transpose*A*shard A=1:=by
 have ht:(shard A).IsSymm:=by
    ext i j; unfold shard glassX; simp only [Matrix.transpose_apply,Matrix.smul_apply, Matrix.of_apply]; congrm _ • ?_
    apply setIntegral_congr_fun measurableSet_Icc; intro x hx
    have he:(spanX A x)⁻¹.IsSymm:=(by unfold spanX; apply Matrix.IsSymm.inv; ext i j; simp only [transpose_apply,Matrix.add_apply,Matrix.smul_apply,one_apply,(isHermitian_iff_isSymm.mp p.1).apply j i,eq_comm])
    exact he.apply ..
 rw [ht, shard_ideal p]; let Q:=p.1.eigenvalues; let U:=conjStarAlgAut ℝ _ p.1.eigenvectorUnitary; let C: Square ι:=diagonal fun i=>(Real.sqrt (Q i))⁻¹
 change U C*A*U C=1
 rw [show A=U (diagonal Q) from p.1.spectral_theorem,← map_mul,← map_mul]
 suffices hf:C*diagonal Q*C=1 by rw [hf,map_one]
 unfold C; rw [diagonal_mul_diagonal,diagonal_mul_diagonal,← diagonal_one]
 congr; ext i
 have hh : 0<Q i:=p.eigenvalues_pos _
 field_simp
 nlinarith [Real.sq_sqrt hh.le] -- tune
end YM.CF.Summit
