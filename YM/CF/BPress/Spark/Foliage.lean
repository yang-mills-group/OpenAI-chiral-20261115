import YM.CF.BPress.Spark.Dorm
/-! Pay anchor cost → rooted-hit cost. Weak NPL conversion at exact heights and support rates in history. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function NormedSpace Finset Filter Lattice Branch Push.AbsoluteSums Grid RG Ledger Pine --
open scoped Topology BigOperators Classical
variable {I:Type}[Fintype I][DecidableEq I]{s:Side}
variable (X:I → Support s) (A:I → Site s) (w:I→ℝ)
def stakeC (B:ℕ)(ε:ℝ):Prop:= ∀ o:Site s,(∑ i:I with A i=o, Real.exp (coverNumber B (X i))*w i)≤ ε -- tune shadow
variable (h:∀ i,A i∈X i) (t: ∀ i, 0≤w i) (B:ℕ)(ε:ℝ)(p:0≤ε)(q:stakeC X A w B ε)
include h t p q
namespace dealer
theorem ωX(_o:Site s): Cash (dorm B ∘ X) w (δPort B) (aPort B ε):=by
 let κ(i:I):= coverNumber B (X i); let U(x:Site s):=score (dorm B∘X) w (δPort B) x; refine ⟨t,fun i=>?_⟩; refine ⟨fun x=>?_ ,(hasSum_fintype _).summable,?_⟩; unfold score; split; exact mul_nonneg (Real.exp_pos _).le (t _); exact le_rfl
 let m(n:ℕ):= Real.exp (-(1:ℝ)/2*(n:ℝ)); let A0 := (αPort B)^4* ε; let S(n:ℕ):= (univ.filter fun z:I=> κ z=n); let Wt(n:ℕ):=halo (prec B*n) {i}; let Z(n:ℕ):= m n*(n+1:ℝ)^4
 have he:0≤ A0:=by unfold A0; positivity
 have ht:Summable Z:= by simpa only [one_mul] using fund_hit 1 1 zero_lt_one zero_le_one
 have hp(n:ℕ):0≤Z n:=by unfold Z m; positivity
 have hX(n:ℕ): (∑ x∈ S n, U i x)≤ A0* Z n:=by
    let f(z:I):=Real.exp (κ z:ℝ)*w z; let P(x:Site s)(v:I):= if A v=x then m n*f v else 0; have hP(x v):0≤ P x v:= ite_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (t ..))) le_rfl; have ht(x): (∑ v∈ S n,P x v)≤ m n* ε:=by
       apply (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> hP x i)).trans; unfold P; rw [←sum_filter,←mul_sum]; exact mul_le_mul_of_nonneg_left (q x) (Real.exp_pos _).le -- tune
    apply le_trans (b:=∑ x∈ S n, ∑ z∈ Wt n,P z x) (sum_le_sum (fun x p=> ?_)); swap
    · change score _ _ _ _ _≤ _; unfold score; dsimp only [Function.comp_apply]; split; swap; · exact sum_nonneg (fun j _=> hP j _)
      next hx =>
         have he:= mem_filter.mp p|>.2; have ht: A x∈ Wt n:= by rw [←he]; apply halo_spec.mpr; refine ⟨i,mem_singleton_self _,((dorm_hit B _ ⟨_,h x⟩).lim i hx (A x) (dorm_sub B _ (h x))).le.trans (dorm_n B _)⟩
         apply le_trans _ (single_le_sum (f:=fun j=>P j x) (fun z _=> hP z _) ht); unfold P; rw [if_pos rfl,←he]; exact honorP B (X x) (w x) (t x)
    rw [sum_comm]; apply le_trans (sum_le_sum (fun z (_:z∈ Wt n)=> ht z)); rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (scope B i n) (mul_nonneg (Real.exp_pos _).le p)).trans; unfold A0 Z; exact Eq.le (by ring)
 rw [tsum_fintype]; change (∑ j,U i j) ≤ _; let t:= univ.image κ; rw [← sum_fiberwise_of_maps_to (t:=t) (g:=κ) _ (U i)]; swap; · intro j (p:j∈(univ:Finset I)); exact show κ j∈t from mem_image_of_mem _ p
 apply (sum_le_sum (fun j (_:j∈t)=> hX j)).trans; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (ht.sum_le_tsum t (fun i _=>hp i)) he -- tune binders
lemma bark: Cash (fun i=> dorm B (X i)) w (δPort B) (aPort B ε):= ωX X A w h t B ε p q 0
end dealer
end YM.CF.BPress.Spark
