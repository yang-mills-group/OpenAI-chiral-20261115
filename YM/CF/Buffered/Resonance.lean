import YM.CF.Gall.Lamb
/-! Uniform-integrability sharpened row/column costs over the shifted momentum bricks. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Glaze
open YM.CF.Onyx YM.CF.Emu
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia)
variable {v V j:ℕ}{r C:ℝ}

structure CoverBill {N:Side}(s:Offset N)(j:ℕ)(M:Jill.Male)(r C:ℝ)(A:Site N→Peb):Prop where
  far :∀ k:Site N,r*pinch N^2 <disk j M (glen s k) → ‖A k‖ ≤ ‖dip j M (tmap (glen s k))‖
  near :∀ k:Site N,disk j M (glen s k) ≤r*pinch N^2 →‖A k‖≤ C/pinch N

private lemma blanket(H:1≤j)(p:0<r)(u:0<C): ∃ K:Gaia→ℝ, (∀ x,0≤K x) ∧ Integrable K ∧ ∀ {N:Side} (A:Site N→Peb) {M:Jill.Male}(s:Offset N), Even N.val → CoverBill s j M r C A → ∀ i:Site N,∀ x∈ pie 1 i,x ≠ 0 → ‖A i‖^2 ≤ K x := by
 obtain ⟨c,b,hc,g,X⟩:=Onyx.stern H p; obtain ⟨w,e,hw,he,Z⟩:=Onyx.soul j H
 let D:= Real.exp (-1*(6*Real.pi)^2); let F:= e*(4*b+2)+C*(4+2*c)
 have hD:0<D:=Real.exp_pos _; have hF:0<F:=by unfold F; positivity
 refine ⟨fun x:Gaia=>(F^2/D)*pet 1 x, fun x=> mul_nonneg (by positivity) (div_nonneg (Real.exp_pos _).le (sq_nonneg _)),(Onyx.pen one_pos).1.const_mul (F^2/D), fun {N} A {M} s ht H' i x U hx=>?_⟩
 have hM:0<‖x‖:=norm_pos_iff.mpr hx; have hm:=pinch_pos N
 let P:=glen s i; have hg:=Onyx.bend one_pos U s
 rw [one_mul] at hg; change ‖x‖ ≤4*pinch N+2*‖P‖ at hg; have he': Bound Real.pi P:=orb i s ht
 have hD' : D≤tog 1 x:=by
   apply Real.exp_le_exp.mpr; norm_num; gcongr
   refine hg.trans ?_
   have hb:pinch N ≤ Real.pi:=div_le_self Real.pi_pos.le (by exact_mod_cast N.property)
   change ‖P‖≤_ at he'; linarith only [hb,he']
 have hj:‖A i‖ ≤ F/‖x‖:=by
    rw [le_div_iff₀ hM]; by_cases t:r*pinch N^2 < disk j M P
    · have hz : pinch N ≤ b*‖P‖:= (X N M s i ht).2 t; have hh : 0 < ‖P‖:=by nlinarith
      refine (mul_le_mul_of_nonneg_right ((H'.far i t).trans (Z M P he' 1 one_pos).2) hM.le).trans ?_
      rw [div_mul_eq_mul_div, div_le_iff₀ hh]; unfold F
      have hb:0≤ C*(4+2*c)*‖P‖:=(by positivity); nlinarith only [hz,hg,mul_le_mul_of_nonneg_left (show ‖x‖≤4*(b*‖P‖)+2*‖P‖ by linarith) he.le,hb]
    have ht': ‖P‖≤ c*pinch N:=(lt_of_not_ge (fun u=>t ((X N M s i ht).1 u))).le
    refine (mul_le_mul_of_nonneg_right (H'.near i (le_of_not_gt t)) hM.le).trans ?_
    rw [div_mul_eq_mul_div,div_le_iff₀ hm]; unfold F; have hb:0≤ e*(4*b+2)*pinch N:=(by positivity); nlinarith only [mul_le_mul_of_nonneg_left (show ‖x‖≤4*pinch N+2*(c*pinch N) by linarith only [hg,ht']) u.le,hb]
 apply le_trans (pow_le_pow_left₀ (norm_nonneg _) hj 2); change _≤ (F^2/D)*(tog _ _/_); rw [div_pow, ← mul_div_assoc,div_le_div_iff_of_pos_right (pow_pos hM _)]; exact ((mul_le_mul_of_nonneg_left hD' (show 0≤ F^2/D by positivity)).trans' (by rw [div_mul_cancel₀ _ hD.ne']))

lemma pick_ball {α : Type*} [NormedAddCommGroup α] [MeasurableSpace α] [BorelSpace α] (μ:Measure α) [NullSingletonClass μ] (f:α→ℝ) (hf:Integrable f μ) (r:ℝ)(p:0<r) : ∃ l:ℝ,0<l ∧ (∫ x in closedBall 0 l,f x∂μ) ≤ r := by
 let w(n:ℕ):=(1/2:ℝ)^n; have hp(n):0<w n:=by unfold w; positivity
 let K n:=closedBall (0:α) (w n); have he: Antitone K:= fun i j h=> closedBall_subset_closedBall (pow_le_pow_of_le_one (by positivity) (by norm_num) h)
 have ht:Tendsto (fun i=> ∫ x in K i,f x∂ μ) atTop (𝓝 0) := by
   have hz := tendsto_setIntegral_of_antitone (μ:=μ) (s:=K) (f:=f) (fun _=>measurableSet_closedBall) he ⟨0,hf.integrableOn⟩
   rw [show ⋂ n,K n={(0:α)} from ?_] at hz; swap
   · ext x
     constructor
     · intro h; by_contra hn; change ¬ x=0 at hn
       obtain ⟨n,v⟩:= ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num : (1/2:ℝ)<1)).eventually (gt_mem_nhds (show 0<‖x‖ from norm_pos_iff.mpr hn))).exists
       change w n <‖x‖ at v; exact not_lt_of_ge ((show ‖x‖≤w n from by simpa only [K,mem_closedBall,dist_zero_right] using Set.mem_iInter.mp h n)) v
     intro h; rw [Set.mem_singleton_iff.mp h,Set.mem_iInter]; intro n; exact mem_closedBall_self (hp n).le
   simpa using hz
 obtain ⟨n,h⟩:= (ht.eventually (gt_mem_nhds p)).exists; exact ⟨w n,hp n,(show (∫ x in K n, f x∂ μ)<r from h).le⟩

lemma furring(H:1≤j)(p:0<r)(u:0<C)(e:ℝ)(t:0<e): ∃ l:ℝ,0<l ∧ ∀ {N:Side} (A:Site N→Peb) {M:Jill.Male}(s:Offset N), Even N.val→ pinch N ≤ l → CoverBill s j M r C A →∀ w:Finset (Site N), (∀ i∈ w,‖glen s i‖≤l) → (∑ i∈w, ‖A i‖^2) ≤ e*(N.val:ℝ)^4 := by
 obtain ⟨K,hk,hg,h⟩:=blanket H p u
 let a:=2*Real.pi; have hA:0<a:=by unfold a; positivity
 obtain ⟨l,q,L⟩:= pick_ball volume K hg _ (show 0<a^4 * e by positivity)
 refine ⟨l/6,by positivity,fun {N} A {M} s v b F w hs=>?_⟩
 let G:=closedBall (0:Gaia) l
 let f(x:Gaia):=∑ i∈w,(pie 1 i).indicator (fun _=> ‖A i‖^2) x; let y:ℝ:= N.val; have hY:0<y:=nPos _
 have hm:=pinch_pos N
 have hl(i:Site N): Integrable (μ:=volume) ((pie 1 i).indicator (fun _=> ‖A i‖^2)) := (integrable_indicator_iff (pies _ _)).2 (integrableOn_const (by rw [pea one_pos i]; finiteness))
 have hp:(1*2*pinch N)^4 *(∑ i∈w,‖A i‖^2)=∫ x,f x:=by
    unfold f; rw [integral_finsetSum _ (fun i _=> hl i),mul_sum]; apply sum_congr rfl; intro i _; rw [integral_indicator (pies _ _),setIntegral_const,Measure.real,pea one_pos i,ENNReal.toReal_ofReal (by positivity)]; rfl
 have hv: ∫ x,f x ≤a^4 * e:=by
    refine le_trans ((integral_mono_ae (integrable_finsetSum _ (fun i _=>hl i)) (hg.indicator (show MeasurableSet G from measurableSet_closedBall)) ?_).trans_eq (integral_indicator measurableSet_closedBall)) L
    filter_upwards [show ∀ᵐ x:Gaia,x≠0 by rw [ae_iff]; simp] with x hx
    by_cases Q:∃ i∈w,x∈pie 1 i; swap
    · rw [sum_eq_zero (fun i hi=> Set.indicator_of_notMem (show x∉pie 1 i from fun hp=> Q ⟨i,hi,hp⟩) _)]; exact Set.indicator_nonneg (fun t _ => hk t) _
    obtain ⟨i,z,Z⟩:=Q
    rw [sum_eq_single i,Set.indicator_of_mem Z]; swap; · intro t _ v; exact Set.indicator_of_notMem (show x∉pie 1 t from fun h=>Set.disjoint_left.mp (Ember.clears v) h Z) _
    swap; · simp [z]
    have he: x∈G := mem_closedBall.mpr (by rw [dist_zero_right]; exact (Onyx.bend one_pos Z s).trans (by linarith [hs i z]))
    rw [Set.indicator_of_mem he]; exact h A s v F i x Z hx
 rw [←hp] at hv
 have hy:a^4*e / (1*2*pinch N)^4=e*(N.val:ℝ)^4:=by unfold pinch a; field_simp
 rw [←hy]; exact (le_div_iff₀ (by positivity)).2 (by rw [mul_comm]; exact hv)
#print axioms furring
end YM.CF.Buffered.Glaze
