import YM.SU5.Regis.Breeze
-- import explicit for derivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric MeasureTheory ProbabilityTheory NormedSpace InnerProductSpace Finset
open scoped Topology BigOperators InnerProductSpace ENNReal
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E](L:StrongDual ℝ E)
local notation "μ"=>stdGaussian E
lemma mag (x:E)(n:ℕ): (∫ y, inner ℝ x y^n ∂μ)= iteratedDeriv n (fun a:ℝ=> Real.exp (‖x‖^2*a^2/2)) 0:=by
 let f:= toDual ℝ E x; change (∫ y,f y^n ∂μ)=_
 have ht: 0∈ interior (integrableExpSet (⇑f) μ):=by
   have he: integrableExpSet (⇑f) μ=Set.univ:= Set.eq_univ_of_forall (fun i=> by apply (mgf_pos_iff (X:=⇑f) (t:=i)).1; rw [exp_linear]; exact Real.exp_pos _)
   rw [he]; simp
 have hx:= iteratedDeriv_mgf_zero ht n; rw [show mgf (⇑f) μ= _ from funext fun i=> exp_linear i f,show ‖f‖=_ from LinearIsometryEquiv.norm_map (toDual ℝ E) x] at hx; exact hx.symm
lemma soloM (c:ℝ)(n:ℕ): let f:=fun a:ℝ=> Real.exp (c*a^2/2); iteratedDeriv (n+1+1) f 0= c*(n+1)*iteratedDeriv n f 0:=by
 intro f; have hv:deriv f=fun i=> c*(i*f i):=by funext i; have he:= (((((hasDerivAt_id' i).pow 2).const_mul c).div_const 2).exp).deriv; unfold f; convert he using 1 <;> first | rfl | (rw [show ((fun i:ℝ=>i) ^ 2) i = i^2 from rfl]; norm_num; ring)
 rw [iteratedDeriv_succ',hv,iteratedDeriv_const_mul_field]; have hh(n:ℕ): ContDiff ℝ n f:=by unfold f; fun_prop
 rw [iteratedDeriv_fun_mul (f:=fun x:ℝ=>x) (show ContDiffAt ℝ _ _ 0 from contDiffAt_id) (hh _|>.contDiffAt)]; simp_rw [iteratedDeriv_fun_id_zero]; rw [Finset.sum_eq_single 1]; · simp; ring
 · intro j _ h; simp [h]
 intro h; simp at h
lemma trio (x:E): (∫ y, inner ℝ x y^4 ∂μ)=3*‖x‖^4 :=by
 rw [mag, soloM (n:=2), soloM (n:=0)]; norm_num; ring
lemma houston (x:E): (∫ y, inner ℝ x y^8 ∂μ)=105*‖x‖^8:=by
 rw [mag,soloM (n:=6),soloM (n:=4), soloM (n:=2), soloM (n:=0)]; norm_num; ring
lemma curtain (x:E)(n:ℕ): Integrable (fun z=> inner ℝ x z^n) μ:=by
 let f:=toDual ℝ E x; change Integrable (fun i=> f i^n) _
 refine (IsGaussian.memLp_dual μ f n (by simp)).integrable_norm_pow'.mono' (by fun_prop) (?_)
 exact Eventually.of_forall fun i=> (norm_pow (f i) n).le
lemma coats (x:E) (n:ℕ): MemLp (fun i=> inner ℝ x i^n) 2 μ:= by
 apply (memLp_two_iff_integrable_sq (by fun_prop)).2
 simp_rw [← pow_mul]; exact curtain ..
lemma duet (x y:E): (∫ i, inner ℝ x i ^ 2 * inner ℝ y i^2 ∂μ)= ‖x‖^2*‖y‖^2 + 2*(inner ℝ x y)^2:=by
 let Z(x:E)(i:E):= inner ℝ x i ^4; let f(i):=inner ℝ x i ^2 *inner ℝ y i^2
 have h : f= fun i=> ((Z (x+y) i + Z (x-y) i)-2*Z x i-2*Z y i)/12:=by funext; unfold f Z; rw [inner_add_left, inner_sub_left]; ring
 have he (x:E): ‖x‖^4=(‖x‖^2)^2:=by ring
 change ∫ i,f i∂μ=_; rw [h,integral_div]; rw [integral_sub (((curtain (x+y) 4).fun_add (curtain (x-y) 4)).sub' ((curtain x 4).const_mul 2)) ((curtain y 4).const_mul 2)] -- tune reducibility
 rw [integral_sub ((curtain (x+y) 4).fun_add (curtain (x-y) 4)) ((curtain x 4).const_mul _), integral_const_mul, integral_const_mul, integral_add (curtain (x+y) 4) (curtain (x-y) 4)]
 simp_rw [trio,he]; rw [norm_add_sq_real, norm_sub_sq_real]; ring
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.trio
#print axioms YM.Regis.Head.Brecht.duet
#print axioms YM.Regis.Head.Brecht.houston
