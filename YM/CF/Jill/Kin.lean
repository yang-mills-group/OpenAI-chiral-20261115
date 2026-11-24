import YM.CF.Jill.Tory
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jill
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
variable {N:Side}
def tall(k:Site N):ℝ:= ‖pm k‖ / pinch N
lemma tall_p(k:Site N):1 ≤ tall k:=by
 unfold tall; rw [le_div_iff₀ (pinch_pos _),one_mul]; exact (cohere (k 0)).trans (norm_le_pi_norm (pm k) 0)
lemma pt_p(k:Site N) : 0 < ‖pm k‖ := (pinch_pos _).trans_le ((cohere (k 0)).trans (norm_le_pi_norm (pm k) 0))
private def feeAxis(x:ℤ):ℝ:= ((1+(x.natAbs:ℝ))^2)⁻¹
private lemma fee_fin : Summable feeAxis:=by
 unfold feeAxis; have he:=(summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow (p:=2) |>.mpr one_lt_two); rw [summable_int_iff_summable_nat_and_neg]; constructor <;> simpa [one_div,add_comm] using he
lemma cost_c : ∃ C:ℝ, 0<C∧∀ N:Side,(∑ k:Site N,(tall k^8)⁻¹) ≤ C:=by
 let C:=1+∑' i,feeAxis i
 have b (i:ℤ): 0≤feeAxis i:=by unfold feeAxis; positivity
 have hb:0<C:=lt_of_lt_of_le one_pos (by unfold C; simp only [le_add_iff_nonneg_right]; exact tsum_nonneg b)
 let f {N:Side}(i:Per N):ℝ:=feeAxis (chert i)
 have hp(N:Side):(∑ i:Per N,f i)≤C:=by
   have he:Function.Injective (chert (N:=N)):=fun i j h=>by simpa only [chert_cast] using congr_arg (fun i:ℤ=>(i:Per N)) h
   unfold f; rw [← sum_image he.injOn]; exact (fee_fin.sum_le_tsum _ fun i _=> b i).trans (by unfold C; linarith)
 have hm(N:Side): (∑ i:Site N, ∏ j, f (i j)) ≤ C^4:=by
   unfold Site Four; rw [← Fintype.prod_sum]; have he:=(Finset.prod_le_prod (s:=@univ Axis _) (f:=fun j:Axis=>∑ i:Per N,f i) (g:=fun j:Axis=>C) (fun i _=> sum_nonneg fun _ _=>b _) (fun i _=> hp N)); simpa [Axis] using he
 refine ⟨(2^8)*C^4,by positivity,fun N=> ?_⟩
 refine (le_trans (Finset.sum_le_sum (s:=@univ (Site N) _) (g:=fun i:Site N=> 2^8 * ∏ j, f (i j)) fun i _=> ?_) (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hm N) (by norm_num)))
 let v:=tall i; have he:1 ≤ v:=tall_p _; have hv :0<v:=one_pos.trans_le he
 have ht(j:Axis):1+(chert (i j)).natAbs≤2*v:=by
   let k:= chert (i j); have hx : |2*(k:ℝ)+1|≤v:=by
     unfold v tall; rw [le_div_iff₀ (pinch_pos _)]; -- inspect ! rw changes tall?
     have hh:= b_abs (pm i) j; rw [show pm i j= _ from ch_price (i j),abs_mul,abs_of_pos (pinch_pos _)] at hh; exact hh
   rw [show chert (i j)=k from rfl,show (k.natAbs:ℝ)=|(k:ℝ)| from ?_]; swap
   · simp
   rw [abs_le] at hx; by_cases h:0≤(k:ℝ) <;> first| rw [abs_of_nonneg h]; linarith| rw [abs_of_neg (lt_of_not_ge h)]; linarith
 have hg: ∏ j:Axis,(1+((chert (i j)).natAbs:ℝ))^2≤ ((2*v)^8):=by calc
    _ ≤ ∏ _:Axis,(2*v)^2 := prod_le_prod (fun _ _=> by positivity) (fun j _=>by gcongr; exact ht j)
    _ = _ := by simp [Axis]; ring
 change (v^8)⁻¹≤_; unfold f feeAxis; rw [prod_inv_distrib]; apply (inv_le_inv₀ (pow_pos hv _) (by positivity : 0< (∏ j:Axis,(1+((chert (i j)).natAbs:ℝ))^2)/ 2^8)).mpr (by rw [div_le_iff₀ (by norm_num : (0:ℝ)<2^8)]; exact hg.trans_eq (by ring)) |>.trans; rw [inv_div,div_eq_mul_inv];
-- cardinal
lemma orb_p (p:ℝ)(h:0≤p):∃ A:ℝ,0<A ∧∀ N:Side,(#(univ.filter fun i:Site N=> tall i≤p):ℝ)≤ A:=by
 obtain ⟨C,v,B⟩:=cost_c; refine ⟨C*(1+p)^8,by positivity,fun N=>?_⟩; let X:=univ.filter fun i:Site N=> tall i≤p
 rw [← div_le_iff₀ (show 0<(1+p)^8 by positivity),div_eq_mul_inv]; exact le_trans (by simp : (#X:ℝ)*((1+p)^8)⁻¹ ≤ ∑ i∈X, ((1+p)^8)⁻¹) ((sum_le_sum fun i hi=> (by have hx:tall i≤p:=(mem_filter.mp hi).2; exact inv_le_inv₀ (by positivity) (by have hz:= tall_p i; positivity : 0<(tall i)^8) |>.mpr (pow_le_pow_left₀ (zero_le_one.trans (tall_p _)) (by linarith) 8))).trans ((sum_le_sum_of_subset_of_nonneg (subset_univ X) fun i _ _=> by have he:=tall_p i; positivity).trans (B _)))
end YM.CF.Jill
