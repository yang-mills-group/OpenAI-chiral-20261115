import YM.CF.Onyx.Sun
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia exileE solidGaia)
variable {N:Side}{j:ℕ}{R:ℝ}{x:Offset N}{k:Site N}
def glen (s: Offset N)(k:Site N):Bin:=pm k+s.val
def moor (p:Bin): Gaia:= exileE.symm p
lemma moor_z (p:Bin) : ‖moor p‖ ≤ 2*‖p‖:=by
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
 rw [← Stationary.geode_sum]; refine (sum_le_sum (g:=fun _=>‖p‖^2) fun i _=>?_).trans ?_; change p i^2≤_
 · rw [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (b_abs _ _) _
 simp [Axis]; nlinarith -- check
lemma moor_s {p:Gaia}(h:p ∈ cellH k): ‖p-moor (glen x k)‖≤ 4*pinch N:=by
 have he:= proximity _ h; rw [norm_sub_rev] at he
 apply (norm_sub_le_norm_sub_add_norm_sub p (bark k) _).trans
 have hz:‖bark k-moor (glen x k)‖=‖moor x.val‖:=by rw [norm_sub_rev,show moor (glen x k)-bark k=moor x.val by ext i; change ((pm k+x.val) i)-pm k i=x.val i; simp]
 rw [hz]; have ht: ‖moor x.val‖ ≤ 2*pinch N:= (moor_z _).trans (mul_le_mul_of_nonneg_left x.property (by positivity)); linarith
lemma moor_q:∃ C:ℝ,0<C∧∀ N:Side,∀ M:Finset (Site N),∀ (x:Offset N)(r:ℝ),pinch N≤r→(∀ i∈M,‖glen x i‖ ≤r)→ (M.card:ℝ)≤ C*(r/pinch N)^4 :=by
 refine ⟨(6^4*(Real.pi^2/2))/2^4,by positivity,fun N M x r h p=>?_⟩; let L:= ⋃ i∈M,cellH i; let B:= closedBall (0:Gaia) (6*r); have hp:=pinch_pos N; have hr:=hp.trans_le h
 have ht:L⊆B:=by
   refine Set.iUnion₂_subset ?_; intro i hi q hg
   rw [mem_closedBall_zero_iff]; exact (norm_le_norm_sub_add _ (moor (glen x i))).trans ((add_le_add (moor_s hg) ((moor_z _).trans (mul_le_mul_of_nonneg_left (p i hi) (by norm_num)))).trans (by linarith))
 have hg:volume.real L≤ volume.real B:= measureReal_mono ht (isCompact_closedBall ..).measure_lt_top.ne
 have he:volume L= (M.card:ℝ≥0∞)*(ENNReal.ofReal (2*pinch N))^4:=by
   rw [show L=_ from rfl, measure_biUnion_finset _ (fun i _=>cell_meas i)]; simp only [cellCore,sum_const,nsmul_eq_mul]; exact Ember.clears.set_pairwise _
 rw [show B=_ from rfl,solidGaia (by positivity),Measure.real,he,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity)] at hg
 rw [div_pow,← mul_div_assoc,le_div_iff₀ (pow_pos hp 4)]; have hx:= hg; rw [mul_pow (a:=2)] at hg; linarith -- inspect
lemma dozen : ∃ C:ℝ,0<C∧∀ (N:Side)(x:Offset N)(R:ℝ),0<R→R*pinch N≤1→∑ k:Site N,1/(1+R*‖glen x k‖)^7 ≤ C/(R*pinch N)^4:=by
 obtain ⟨C,g,H⟩:=moor_q; let F(i:ℕ):ℝ:=1/(1+(i:ℝ))^3
 have ht: Summable F:=by
   have he:=(summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow (p:=3) |>.mpr (by norm_num)); simpa [F,add_comm] using he
 let d:=1+∑' i,F i; have hp(i:ℕ):0≤F i:=by unfold F; positivity
 have hv:0<d:=by unfold d; linarith [show 0≤ ∑' i,F i from tsum_nonneg hp]
 refine ⟨d*C,by positivity,fun N x R hr p=>?_⟩
 let V:=C/(R*pinch N)^4; have hm:=pinch_pos N
 let w(k:Site N):= ⌊R*‖glen x k‖⌋₊; let I:= univ.image w; let A(k:Site N):= 1/(1+R*‖glen x k‖)^7
 have hg i:(∑ k∈ univ.filter (fun k=>w k=i),A k) ≤ F i * V:=by
   let M:=univ.filter (fun k=>w k=i); let y:ℝ:=1+(i:ℝ); have hY:0<y:=by unfold y; positivity
   have he := H N M x (y/R) (by rw [le_div_iff₀ hr]; unfold y; have ht:0≤(i:ℝ):=Nat.cast_nonneg _; linarith) (fun k hk=> by
     have he:w k=i:=(mem_filter.mp hk).2; rw [le_div_iff₀ hr]; unfold y; rw [←he,add_comm,mul_comm]; exact (Nat.lt_floor_add_one _).le)
   have hh: ∑ k∈M,A k ≤ ∑ k∈M,1/y^7:=by
      refine sum_le_sum fun k hk=>?_ ; -- tune
      have hh:w k=i:= (mem_filter.mp hk).2; unfold A; unfold y; rw [←hh]; gcongr; exact Nat.floor_le (by positivity)
   refine hh.trans ((show ∑ k∈M,1/y^7 = (#M:ℝ) *(1/y^7) by simp).trans_le ?_); exact (mul_le_mul_of_nonneg_right he (by positivity)).trans_eq (by unfold y V F; rw [add_comm 1 (i:ℝ)]; have hz: 0<(i:ℝ)+1:=(by positivity); field_simp <;> ring)
 have he:Set.MapsTo w (↑(univ:Finset (Site N))) I:=fun i _=>mem_image_of_mem w (mem_univ _)
 change (∑ k,A k) ≤ _; rw [← sum_fiberwise_of_maps_to he] -- tune
 exact (sum_le_sum (g:=fun i=>F i * V) (fun i _=>hg i)).trans (by rw [← sum_mul]; refine (mul_le_mul_of_nonneg_right ((ht.sum_le_tsum I fun i _=> hp i).trans (by unfold d; linarith : _≤d)) (show 0≤V by unfold V; positivity)).trans_eq ?_; unfold V; ring)
end YM.CF.Onyx
