import YM.CF.Emu.Well
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gall
open YM.CF.Onyx YM.CF.Emu
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight)
variable {j:ℕ}{r C:ℝ}
lemma tad(H:1≤j)(p:0<r)(u:0<C):∃ V:ℝ,0<V ∧∀ {N:Side}(A:Site N→Peb){M:Jill.Male}(s:Offset N),Even N.val→ FormU s j M r C A→ (∑ i,‖A i‖^2) ≤ V*(N.val:ℝ)^4:=by
 obtain ⟨c,b,hc,g,X⟩:=stern H p; obtain ⟨w,e,hw,he,Z⟩:=soul j H; let D:= Real.exp (-1*(6*Real.pi)^2); let F:= e*(4*b+2)+C*(4+2*c); let K(x:Gaia):=(F^2/D)*pet 1 x; have hD:0<D:=Real.exp_pos _; have hF:0<F:=by unfold F; positivity
 let a:=2*Real.pi; have hA:0<a:=by unfold a; positivity
 let V:=∫ x,K x
 refine ⟨max (V/a^4) 1,lt_max_of_lt_right one_pos,fun {N} A {M} s ht H' =>?_⟩; let T (i):=pie (1:ℝ) (i:Site N); let f(x:Gaia):=∑ i:Site N,(T i).indicator (fun _=> ‖A i‖^2) x; let y:ℝ:= N.val; have hY:0<y:=nPos _
 have hm:=pinch_pos N
 have hp:(1*2*pinch N)^4 *(∑ i,‖A i‖^2)=∫ x,f x:=by
    unfold f; rw [integral_finsetSum,mul_sum]; apply sum_congr rfl; intro i _; rw [integral_indicator (pies _ _),setIntegral_const,Measure.real,pea one_pos i,ENNReal.toReal_ofReal (by positivity)]; rfl
    intro i _; apply (integrable_indicator_iff (pies _ _)).2 (integrableOn_const ?_); rw [pea one_pos i]; finiteness
 have hv: ∫ x,f x ≤V:=by
    refine integral_mono_ae (integrable_finsetSum _ (fun i _=> (integrable_indicator_iff (pies _ _)).2 (integrableOn_const ?_))) ((Onyx.pen one_pos).1.const_mul (F^2/D)) ?_
    · rw [pea one_pos i]; finiteness
    filter_upwards [show ∀ᵐ x:Gaia,x≠0 by rw [ae_iff]; simp] with x hx; have hM:0<‖x‖:=norm_pos_iff.mpr hx; have hX:0<pet 1 x:=div_pos (Real.exp_pos _) (pow_pos hM _)
    by_cases U:∃ i:Site N,x∈T i; swap; · unfold f; rw [sum_eq_zero (fun i _=> Set.indicator_of_notMem (not_exists.mp U i) _)]; positivity
    obtain ⟨i,U⟩:=U; unfold f; rw [sum_eq_single i,Set.indicator_of_mem U]; swap; · intro t _ v; exact Set.indicator_of_notMem (show x∉T t from fun h=>Set.disjoint_left.mp (Ember.clears v) h U) _
    swap; · simp
    let P:=glen s i; have hg:=bend one_pos U s; rw [one_mul] at hg; change ‖x‖ ≤4*pinch N+2*‖P‖ at hg; have he': Bound Real.pi P:=orb i s ht
    have hD' : D≤tog 1 x:=by apply Real.exp_le_exp.mpr; norm_num; gcongr; refine hg.trans ?_; have hb:pinch N ≤ Real.pi:=div_le_self Real.pi_pos.le (by exact_mod_cast N.property); change ‖P‖≤_ at he'; linarith only [hb,he']
                                                             -- tune
    have hj:‖A i‖ ≤ F/‖x‖:=by
       rw [le_div_iff₀ hM]; by_cases t:r*pinch N^2 < disk j M P
       · have hz : pinch N ≤ b*‖P‖:= (X N M s i ht).2 t; have hh : 0 < ‖P‖:=by nlinarith
         have he := mul_le_mul_of_nonneg_right ((Z M P he' 1 one_pos).2) hM.le; rw [H'.far i t]; refine he.trans ?_; rw [div_mul_eq_mul_div, div_le_iff₀ hh]; unfold F; have hb:0≤ C*(4+2*c)*‖P‖:=(by positivity); nlinarith only [hz,hg,mul_le_mul_of_nonneg_left (show ‖x‖≤4*(b*‖P‖)+2*‖P‖ by linarith) (show 0≤e from ‹0<e›.le),hb]
       have ht': ‖P‖≤ c*pinch N:=(lt_of_not_ge (fun u=>t ((X N M s i ht).1 u))).le -- wrong
       refine (mul_le_mul_of_nonneg_right (H'.near i (le_of_not_gt t)) hM.le).trans ?_; rw [div_mul_eq_mul_div,div_le_iff₀ hm]; unfold F; have hb:0≤ e*(4*b+2)*pinch N:=(by positivity); nlinarith only [mul_le_mul_of_nonneg_left (show ‖x‖≤4*pinch N+2*(c*pinch N) by linarith only [hg,ht']) u.le,hb]
    apply le_trans (pow_le_pow_left₀ (norm_nonneg _) hj 2); change _≤ (F^2/D)*(tog _ _/_); rw [div_pow, ← mul_div_assoc,div_le_div_iff_of_pos_right (pow_pos hM _)]; exact ((mul_le_mul_of_nonneg_left hD' (show 0≤ F^2/D by positivity)).trans' (by rw [div_mul_cancel₀ _ hD.ne'])) -- tune
 refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left (V/a^4) _) (by positivity)); have he : V/(a^4)*y^4= V/(1*2*pinch N)^4:=by unfold a y pinch; have hy':0<(N.val:ℝ):=hY; field_simp
 change _ ≤ V/(a^4)*y^4; rw [he,le_div_iff₀ (by positivity), mul_comm,hp]; exact hv
end YM.CF.Gall
