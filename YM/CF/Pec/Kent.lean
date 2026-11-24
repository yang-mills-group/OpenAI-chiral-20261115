import YM.CF.Pec.Splice
import YM.CF.Support.Ln
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section Taylor
variable {n:Type}[LinearOrder n][Fintype n][Nonempty n]
def trout : Op n→L[ℝ]ℂ:= (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
def bore(A:Op n): Op n:= bcoef 0 • A^1 + bcoef 1 • A^2
theorem essence:ContDiffAt ℝ ω (invoice (n:=n)) 0:=by
 have ht:invoice (0:Op n)=0:=by simp [invoice,Fock.slope]
 have hw:=invoice_at (A:=(0:Op n)) (by simp); have hh: ContDiffAt ℝ ω (Matrix.det (R:=ℂ) (n:=n)) (1:Op n):=by
    let M(i j:n):= (show Op n→ₗ[ℝ]ℂ from ⟨⟨fun A=>A i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩).toContinuousLinearMap
    change ContDiffAt ℝ ω (fun x:Op n=> x.det) 1; simp_rw [Matrix.det_apply]; refine ContDiffAt.sum fun i _=> ContDiffAt.const_smul i.sign ?_; exact contDiffAt_prod fun b _=> (M (i b) b).contDiff.contDiffAt
 let P(A:Op n):=(1+A).det; have hl:ContDiffAt ℝ ω P 0:= ((show ContDiffAt ℝ ω Matrix.det (1+(0:Op n)) from by rw [add_zero]; exact hh).comp (g:=Matrix.det) (f:=fun x=> 1+x) _ (contDiffAt_const.add (contDiffAt_id (n:=ω))))
 let f:= fun A: Op n=> Complex.log (P A); have hf:ContDiffAt ℝ ω f 0:=by
    have ht:ContDiffAt ℝ ω Complex.log (P 0):= (Complex.contDiffAt_log (n:=ω) (x:=P 0) (by unfold P; simp)).restrict_scalars ℝ; exact ht.comp _ hl
 apply hf.congr_of_eventuallyEq
 have h0: Tendsto (fun i:Op n=> (invoice i).im) (𝓝 0) (𝓝 0):=by convert Complex.continuous_im.continuousAt.tendsto.comp hw.tendsto <;> first|rfl|simp [ht]
 filter_upwards [h0.eventually_lt tendsto_const_nhds Real.pi_pos, Tendsto.eventually_lt tendsto_const_nhds h0 (show -Real.pi < 0 by linarith [Real.pi_pos]),Metric.ball_mem_nhds (0:Op n) zero_lt_one] with i hi hg hy; unfold f P; rw [←factor i (by simpa using hy),Complex.log_exp hg hi.le]
lemma dents {A:Op n}(p:‖A‖≤1/2): ‖invoice A - trout (bore A)‖ ≤ ‖trout (n:=n)‖*(2*‖A‖^3):=by
 let f(i:ℕ):= bcoef i • A^(i+1); let v:=‖A‖; have hv:0≤v:=norm_nonneg _; have ht(i): ‖f i‖≤ v^(i+1):=by unfold f; rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (bc_norm _)).trans (norm_pow_le ..)
 have hp:v < 1:=p.trans_lt (by norm_num); have he:Summable fun i:ℕ=> v^i:= summable_geometric_of_lt_one hv hp; have hg : Summable fun i=> ‖f i‖:=(summable_nat_add_iff 1|>.mpr he).of_nonneg_of_le (fun _=>norm_nonneg _) ht
 let W:=trout (n:=n); let H:=∑' i,f (i+2)
 have hx: pencil A=bore A+ H:=(hg.of_norm.sum_add_tsum_nat_add 2).symm.trans (congrArg (·+H) (show ∑ i∈range 2,f i = _ from (by rw [sum_range_succ,sum_range_succ]; simp only [range_zero,sum_empty,zero_add]; rfl)))
 have hy:‖H‖ ≤2*v^3:=by
    have hA(i:ℕ): ‖f (i+2)‖≤ ((2:ℝ)⁻¹)^i*v^3:=by apply (ht (i+2)).trans; rw [show i+2+1=i+3 from rfl,pow_add]; gcongr; simpa [v] using p
    have hH: Summable (fun i:ℕ=> ‖f (i+2)‖):= (summable_nat_add_iff 2 (f:=fun i=>‖f i‖)).mpr hg; have hK : Summable (fun i:ℕ=> ((2:ℝ)⁻¹)^i * v^3):=(summable_geometric_of_lt_one (r:=(2:ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right _; apply (norm_tsum_le_tsum_norm hH).trans ((Summable.tsum_le_tsum hA hH hK).trans_eq ?_); rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
 rw [tally_log hp,hx]; change ‖W (bore A+ H)-W _‖≤ _; rw [map_add,add_sub_cancel_left]; exact (W.le_opNorm _).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
variable {C:Type}[NormedAddCommGroup C][NormedSpace ℝ C]
lemma ebbV {F:C→ Op n}(p:ContDiffAt ℝ 2 F 0)(h:F 0=0):ContDiffAt ℝ 2 (invoice ∘ F) 0 ∧ cFoot 3 (fun v=> invoice (F v)-trout (bore (F v))):=by
 let W:= (trout (n:=n)); have he:ContDiffAt ℝ 2 (invoice ∘ F) 0 := ((show ContDiffAt ℝ ω invoice (F 0) by rw [h]; exact essence).of_le le_top).comp _ p; refine ⟨he,?_⟩; have hP:ContDiffAt ℝ 2 (fun v=> invoice (F v)-W (bore (F v))) 0:= he.sub (W.contDiff.contDiffAt.comp (f:=fun v=> bore (F v)) _ ((p.pow 1|>.const_smul _).add ((p.pow 2).const_smul _)))
 apply nextF (m:=2) (by simp only [Nat.cast_ofNat]; exact hP)
 intro x; let K:=𝓝[≠] (0:ℝ); let g(t:ℝ):=F (t • x); have ht:(cFoot 1 F):=by intro i e; rw [show i=0 from by omega]; ext1; rw [iteratedFDeriv_zero_apply,h]; rfl
 have hl:Tendsto (fun t:ℝ=> t⁻¹ • g t) K (𝓝 (trim 1 F x)):=by
    have hv:(1:ℕ)≤ (2:ℕ):=by omega
    simpa only [pow_one] using (argent (p.of_le (m:=(↑(1:ℕ):WithTop ℕ∞)) (by norm_num))).mp ht x
 have hp : Tendsto g K (𝓝 0):=by
    have hh:=p.continuousAt.tendsto; rw [h] at hh; exact hh.comp ((Hull.ray_home x).mono_left nhdsWithin_le_nhds)
 have hb :Tendsto (fun x:ℝ=> (‖x⁻¹ • g x‖^2)*‖g x‖* (2*‖W‖)) K (𝓝 0):=by convert (((hl.norm.pow 2).mul hp.norm).mul_const (2*‖W‖)); simp
 refine squeeze_zero_norm' (a:=fun x=> (‖x⁻¹ • g x‖^2)*‖g x‖* (2*‖W‖)) ?_ hb; filter_upwards [hp.norm.eventually (ge_mem_nhds (show ‖(0:Op n)‖ < 1/2 from by simp))] with t ht; rw [norm_smul]; refine (mul_le_mul_of_nonneg_left (dents ht) (norm_nonneg _)).trans_eq ?_; change ‖(t^2)⁻¹‖ * (‖W‖*(2*‖g t‖^3))= _; rw [norm_smul, ←inv_pow,norm_pow]; ring
end Taylor
end YM.CF.Pec
