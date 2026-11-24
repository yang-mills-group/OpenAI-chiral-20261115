import YM.SU5.Reconstruction.Trap.Lantern
/-!
# Forward LIGHT spectrum derived from pacing and bought axiswise knot rotations
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe Measure Real
variable {H D K:Hilbert} {a b : Axis} (S:OS.Semigroup H a)
local notation "μ" v:max => S.ℚmeasure.diagonal v
-- Note sign; implementing boost on translations by U F(x) U†. Thus U†-state's own momentum is boost-image of previous state's.
set_option quotPrecheck false
abbrev Boosts (u:ℝ)(b:Axis)(Q:H.Op) := ∀ x : E4, Q*trans S x = trans S (move a b u x)*Q
def Markets := ∀ (v:Axis)(_:v≠a) (u:ℝ), ∃ Q:H.Op, Pays Q ∧ Boosts S u v Q -- params implicit?
lemma boosts_state (p:b≠a)(u:ℝ)(Q:H.Op)(v:Pays Q)(e:Boosts S u b Q) (x:H) :
    Measure.map (move a b u) (S.ℚmeasure.diagonal x)= S.ℚmeasure.diagonal (star Q x):= by
 apply Measure.ext_of_charFun; funext y
 rw [charFun_apply,integral_map ((smooth_move a b u).measurable.aemeasurable) (by fun_prop),S.joint]
 simp_rw [dual p]; rw [← charFun_apply,S.joint]
 have h(y:E4): trans S (move a b u y) = Q * trans S y * star Q:= by rw [e,mul_assoc,v.2,mul_one]
 change inner ℂ x (trans S _ x)= _; rw [h]; change inner ℂ x (Q (trans S y (Q.adjoint x)))=_; rw [←ContinuousLinearMap.adjoint_inner_left]; rfl
lemma transports {b} (p:b≠a)(u:ℝ)(M:Markets S)(x:H)(y:E4)(h:y∈ (S.ℚmeasure.diagonal x).support):∃ w:H, move a b u y∈ (S.ℚmeasure.diagonal w).support:=by
 obtain ⟨Q,hQ,t⟩:=M _ p u; refine ⟨star Q x,?_⟩; rw [← boosts_state S p u Q hQ t x]; apply mem_support_iff_forall _|>.2; intro t ht
 obtain ⟨V,q,v,e⟩:= _root_.mem_nhds_iff.mp ht; refine lt_of_lt_of_le ?_ (measure_mono q); rw [Measure.map_apply (smooth_move a b u).measurable v.measurableSet]; exact (mem_support_iff_forall _|>.1 h) _ ((v.preimage (smooth_move ..)).mem_nhds e)
-- elementary step: every future boost preserving mass-cost L along ALL other transverse axes implies it is paid BY the leftover value after subtracting that axes.
private lemma points {U V c:ℝ}(p:0≤U)(q:0≤V)(e:∀ r>0,c≤ (U*r+V*r⁻¹)^2) : c≤4*U*V:= by
 have k(u c:ℝ)(h:∀ r>0,c≤(u*r)^2): c≤0:= by
   have g : Tendsto (fun r:ℝ=>(u*r)^2) (𝓝[>] 0) (𝓝 0) := by simpa only [mul_zero, ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] using ((show Continuous (fun (i:ℝ)=> (u*i)^2) by fun_prop).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:=Ioi 0))
   exact ge_of_tendsto g (Eventually.mono self_mem_nhdsWithin fun i q=> h i q)
 rcases p.eq_or_lt with h|p
 · simp [←h]; refine k V c (fun r hr=>?_); simpa only [←h,zero_mul,zero_add, inv_inv] using e r⁻¹ (inv_pos.mpr hr)
 rcases q.eq_or_lt with h|q
 · simp [←h]; exact k U c (fun r hr=> by simpa [←h] using e r hr)
 let s:=sqrt (V/U); have hh:0<s:= sqrt_pos.2 (div_pos q p)
 have ht:s*s=V/U:=mul_self_sqrt (div_nonneg q.le p.le)
 have he:V*s⁻¹=U*s:=by rw [←div_eq_mul_inv, div_eq_iff hh.ne', mul_assoc,ht]; field_simp
 specialize e s hh; rw [he] at e; have hg:= (eq_div_iff p.ne').1 ht; nlinarith [e] -- hg times U
private lemma remainder (x y c:ℝ) (p:|y|≤x)(g:∀ t:ℝ,c≤ (cosh t*x+sinh t*y)^2):
    y^2+c≤ x^2:= by
 let k:=(x+y)/2; let r:=(x-y)/2; obtain ⟨q,h⟩:=abs_le.mp p
 have p:c ≤ 4*k*r:= points (by unfold k;linarith) (by unfold r;linarith) fun i v=> by specialize g (Real.log i); rw [cosh_eq,sinh_eq,Real.exp_log v,Real.exp_neg,Real.exp_log v] at g; refine g.trans_eq ?_; unfold k r; ring
 unfold k r at p; linarith
lemma endLight (M:Markets S)(P:∀ k:Axis,k≠a→ Paces k S) : ConePrice.Forward S := by
 have h (v:Finset Axis)(u:a∉v)(x:H)(t:E4)(p:t∈ (μ x).support) : ∑ b∈v,(t b)^2 ≤ (t a)^2:=by
   induction v using Finset.induction_on generalizing x t with
   | empty=>simp; positivity
   | @insert i k b ih=>
     have v0:i≠a:= fun p=>u (p ▸ Finset.mem_insert_self ..); have hv:a∉k:=fun w=>u (Finset.mem_insert_of_mem w)
     rw [Finset.sum_insert b]; refine remainder _ _ _ (P i v0 x t p) (fun s=>?_); obtain ⟨w,q⟩:= transports S v0 s M x t p; specialize ih hv w _ q
     rw [eye_high v0] at ih; rw [← show ∑ j∈k,(move a i s t j)^2=∑ j∈k,(t j)^2 from Finset.sum_congr rfl (fun j h=> by rw [others (a:=a) (b:=i) s t j (fun p=> hv (p ▸ h)) (fun p=>b (p ▸ h))])]; exact ih
 ext1 x; apply ((S.ℚmeasure).null_pair (ConePrice.closed_front _).isOpen_compl.measurableSet _).1
 refine measure_mono_null (compl_subset_compl.mpr ?_) measure_compl_support
 intro y hy; change ‖SEP a y‖ ≤ y a
 apply le_of_sq_le_sq _ (S.nonneg _ hy); rw [ConePrice.sep_size,EuclideanSpace.real_norm_sq_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]; simp only [add_sub_cancel_right]; exact h _ (Finset.notMem_erase a _) _ _ hy -- check
end YM.Picket
