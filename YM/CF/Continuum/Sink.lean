import YM.CF.Fock.Glacier

/-!
# Remove the **full** pressure factor of Fock heat, at an arbitrary finite box

Useful in the positivity investigations; more than just an estimate after picking
one many-body vector. Error is operator norm (on *entire ungraded* Fock space).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Finset Fock Lattice
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n] [Nonempty n]

private def positive (d:n→ℝ) := univ.filter fun i=> 0<d i
private lemma top_trace (U:UNI n)(d:n→ℝ)(h : Safe (spectral U d)) :
    ((spectral U d)*projector (spectral U d)).trace= ((∑ i ∈ positive d,d i : ℝ):ℂ) := by
  let P:= positive d; rw [projector_spectral U d h,spectral_mul]; unfold spectral; rw [trace_twist,Matrix.trace_diagonal]; unfold positive; push_cast; rw [sum_filter]; apply sum_congr rfl; intro i _; by_cases h:0<d i<;>simp [h,occ]

theorem flight_positive {A : Op n} (h : Safe A)(t : ℝ) : 0 < flight A t := by
  obtain ⟨U,d,rfl⟩:=spectral_exists A h.self; rw [flight,top_trace U d h, ← Complex.ofReal_mul,←Complex.ofReal_exp]; exact_mod_cast Real.exp_pos _

omit [Nonempty n] in
private lemma below {U : UNI n}{d : n→ℝ} (h : Safe (spectral U d)) (s : Finset n) (p : s ≠ positive d) :
   ∑ i∈s,d i ≤ ∑ i∈positive d,d i-1/2 :=by
  let v:=positive d
  have he i : 1/2 ≤ |d i| := by
    have hp:= h.margin; rw [spectral_pow, ←spectral_one U,spectral_smul,spectral_le] at hp; have hg:=hp i; simp only [Pi.one_apply,Pi.smul_apply,smul_eq_mul,mul_one,Pi.pow_apply] at hg; nlinarith [sq_abs (d i), abs_nonneg (d i)]
  have hf (i) (k:i∈v \ s) : 1/2 ≤ d i := by
    have hv:0<d i:=((mem_filter (p:=fun i=>0<d i)).mp (mem_sdiff.mp k).1).2; simpa only [abs_of_pos hv] using he i
  have hh i (k:i∈s \ v) : d i ≤ -(1/2) := by
    have hv:d i ≤ 0:= not_lt.mp (fun g=> (mem_sdiff.mp k).2 (mem_filter.mpr ⟨mem_univ _,g⟩)); exact le_neg_of_le_neg (show (1/2:ℝ) ≤ -d i from (abs_of_nonpos hv) ▸ he i)
  have hF : ∑ i∈ v\s,d i + ∑ i∈v∩s,d i=∑ i∈v,d i:=by rw [show v\s=v\(v∩s) by ext; simp]; exact sum_sdiff inter_subset_left
  have hh' : ∑ i∈ s\v,d i +∑ i∈v∩s,d i=∑ i∈s,d i:=by rw [show s\v=s\(v∩s) by ext; simp]; exact sum_sdiff inter_subset_right
  have hf' : 0 ≤ ∑ i∈ v\s,d i:=sum_nonneg fun i k=>(by linarith only [hf i k]); have hk' : ∑ i∈s\v,d i ≤ 0:=sum_nonpos fun i k=>(by linarith only [hh i k]); change _≤∑ i∈v,d i-_
  by_cases g:s ⊆ v
  · obtain ⟨i,hi⟩:= sdiff_nonempty.mpr (fun z=> p (Subset.antisymm g z)); have hm:d i≤ ∑ j ∈ v\s,d j:=single_le_sum (f:=d) (fun i w=>by linarith only [hf i w]) hi; linarith only [hm,hf i hi, hh',hF,hk']
  obtain ⟨i,hi⟩:= sdiff_nonempty.mpr g; have hm: ∑ j∈s\v,d j ≤ d i:= by
    rw [←neg_le_neg_iff, ←Finset.sum_neg_distrib]; exact single_le_sum (f:=fun j=> -d j) (fun j k=>neg_nonneg.mpr (by linarith only [hh j k])) hi
  linarith only [hm,hh i hi,hh',hF,hf']

def heatSlice (A : Op n) (t : ℝ) : FC n := (flight A t)⁻¹ • quant (grow A t)

lemma slice_gap {A : Op n}(h : Safe A){t : ℝ} (p : 0 ≤ t) :
    ‖heatSlice A t-lineOp (projector A)‖ ≤ Real.exp (-t/2) := by
  obtain ⟨U,d,rfl⟩:=spectral_exists A h.self
  let A:=spectral U d; let D(i):= Real.exp (t*d i)
  let v:=positive d; let mx:=∑ i∈v,d i; let f(s: Finset n):=∑ i∈s,d i; let E(s:Finset n) := (Real.exp (t*(f s-mx)):ℂ); let V:=quantU U; let P:=projector A
  have pA : P=twist U (cutM v) := by unfold P; rw [projector_spectral U d h]; simp only [spectral]; congr 2; ext i; by_cases g:0<d i <;> simp [v,positive,occ,g]
  have hp : heatSlice A t=twist V (Matrix.diagonal E):=by
     unfold heatSlice flight; rw [top_trace U d h,glacial U d t]; rw [show quant (spectral U fun i=>Real.exp (t*d i)) = twist V (quant (Matrix.diagonal fun i=>(D i:ℂ))) from quant_twist _ _, ←twist_scalar, quant_diag]; apply congrArg; ext i j; by_cases p:i=j
     swap; simp [p];
     subst j; simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq]; unfold E; rw [smul_eq_mul, ←Complex.exp_neg, Complex.ofReal_exp]; unfold mx v positive D f; push_cast; rw [mul_sub]; rw [← Complex.exp_sum,←Complex.exp_add]; congr 1; rw [←mul_sum]; ring
  change ‖heatSlice A t-lineOp P‖ ≤ _; rw [hp,pA,line_twist,cutLine,←map_sub]; rw [twist_formula, show star V.val=(star V).val from rfl]; rw [CStarRing.norm_mul_coe_unitary _ (star V),CStarRing.norm_coe_unitary_mul]; rw [cutM, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]; apply pi_norm_le_iff_of_nonneg (Real.exp_pos _).le|>.2
  intro s; by_cases hs:s=v
  · subst s; simp [E,f,mx]; exact (Real.exp_pos _).le
  rw [if_neg (fun q=>hs (mem_singleton.mp q)),sub_zero,show ‖E s‖=Real.exp (t*(f s-mx)) by unfold E; rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]]; apply Real.exp_le_exp.mpr; have he:f s ≤ mx-1/2:=below h s hs; nlinarith
lemma late_flight {A : Op n} (h : Safe A) : Tendsto (heatSlice A) atTop (𝓝 (lineOp (projector A))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ((eventually_ge_atTop (0:ℝ)).mono fun x p=> slice_gap h p); have hx := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (show 0<(2:ℝ) by norm_num)))) -- tweak
  simpa [Function.comp_def,neg_div] using hx
end YM.CF.Window
