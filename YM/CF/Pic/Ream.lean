import YM.CF.Flare.Foot
import YM.CF.Delta.Rebase
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Set
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][LinearOrder n][Nonempty n]{P Q R A:Op n}{p q:Wave n}{k v:ℝ}{U:UNI n}
lemma norm_I (e:‖A‖≤1/3):‖invoice A‖ ≤ (Fintype.card n)* (2*‖A‖):=by
 have he(x:ℝ)(h:x∈Icc (0:ℝ) 1): ‖(Fock.beam A x)⁻¹‖ ≤ 2:=by
   apply (inv_close_le (1:UNI n) _).2; change ‖1+(x:ℂ) • A - 1‖≤_; rw [add_sub_cancel_left,norm_smul,Complex.norm_real,Real.norm_of_nonneg h.1]; exact (mul_le_of_le_one_left (norm_nonneg _) h.2).trans e
 have hp(x:ℝ)(h:x∈uIoc (0:ℝ) 1):‖Fock.slope A x‖≤ Fintype.card n * (2*‖A‖):=by
   let B:=(Fock.beam A x)⁻¹; have hh:‖B*A‖≤2*‖A‖:=(norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (he x ((Set.uIcc_of_le (show (0:ℝ)≤1 from zero_le_one)) ▸ (uIoc_subset_uIcc h))) (norm_nonneg _)); exact (norm_sum_le (E:=ℂ) _ _).trans ((sum_le_sum (s:=@Finset.univ n _) (g:=fun _=> 2*‖A‖) fun i _=> (norm_entry (B*A) i i).trans hh).trans_eq (by simp)) -- tune name
 simpa [invoice] using intervalIntegral.norm_integral_le_of_norm_le_const hp
lemma stroke(h:IsStarProjection P)(p:‖P-Q‖ ≤ k)(u:Q*U.val=U.val*cc Q): ‖stage P U.val-U.val‖ ≤ 2*k:=by
 rw [stage_gap h,show P*U.val-U.val*cc P=(P-Q)*U.val+ U.val*(cc Q-cc P) by rw [sub_mul,u,mul_sub]; abel]
 have he:‖U.val‖=1:=CStarRing.norm_of_mem_unitary U.property
 rw [two_mul]; refine (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans ?_) ((norm_mul_le ..).trans ?_)); rw [he,mul_one]; exact p; rw [he,one_mul,norm_sub_rev,←cc_sub, Scroll.norm_cc]; exact p
lemma hatch (h:IsStarProjection P)(p:IsStarProjection Q)(t:‖P-Q‖≤k) : ‖body Q U.val-body P U.val‖ ≤ k+k:=by
 have hx: ‖U.val‖=1:=CStarRing.norm_of_mem_unitary U.property
 rw [body,body,show _-_=(Q-P)*U.val*cc Q +P*U.val*(cc Q-cc P) from ?_]; swap; · rw [sub_mul,sub_mul,mul_sub]; abel
 apply (norm_add_le ..).trans; apply add_le_add <;> apply (norm_mul_le ..).trans
 · refine (mul_le_of_le_one_right (norm_nonneg _) (IsStarProjection.norm_le _ (ccProj p))).trans ((norm_mul_le ..).trans ?_); rw [hx,mul_one,norm_sub_rev]; exact t
 apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ((norm_mul_le ..).trans ?_)); swap; · rw [hx,mul_one]; exact IsStarProjection.norm_le _ h
 rw [←cc_sub, Scroll.norm_cc,norm_sub_rev]; exact t
lemma crew (h:IsStarProjection P)(e: ‖stage P U.val-U.val‖ ≤1/3)(g:IsStarProjection Q)(t:‖P-Q‖≤k): ‖relay P U.val (body Q U.val) -1‖ ≤ (k+k)*2:=by
 obtain ⟨hx,H⟩:= inv_close_le U e
 unfold relay
 have he:body P U.val*(stage P U.val)⁻¹+(1-P)=1:=relay_base h hx
 let B:=body Q U.val-body P U.val; have hh:‖body P B‖≤k+k:=by
   have hg:‖B‖≤k+k:= hatch h g t; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (IsStarProjection.norm_le _ (ccProj h))).trans; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (IsStarProjection.norm_le _ h)).trans hg)
 have hv:body P (body Q U.val)-body P U.val=body P B:=by change _=P*(body Q U.val-body P U.val)*_; rw [mul_sub,sub_mul,body_left h,body_right h]; rfl -- tune binder
 nth_rw 2 [← he]; rw [add_sub_add_right_eq_sub,← sub_mul,hv]; exact (norm_mul_le ..).trans (mul_le_mul hh H (norm_nonneg _) ((norm_nonneg _).trans hh))
-- Q near P. M project amplitude ratio near 1
lemma land (h:IsStarProjection P)(g:IsStarProjection Q)(p:‖P-Q‖≤k)(u:k ≤ 1/3): let F:= P*Q; ‖F*star F+(1-P)-1‖ ≤ k:=by
 intro F; rw [show F*star F+(1-P)-1=P*(Q-P)*P from ?_]; swap
 · unfold F; rw [star_mul,h.2,g.2,←mul_assoc,mul_assoc _ Q Q,g.1, mul_sub,h.1,sub_mul,h.1]; abel
 apply (norm_mul_le ..).trans; exact (mul_le_of_le_one_right (norm_nonneg _) (h.norm_le P)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (h.norm_le P)).trans ((norm_sub_rev ..).trans_le p)))
lemma needle (h:IsStarProjection P)(g:IsStarProjection Q)(w: ‖P-Q‖ ≤ k)(v:k≤ 1/3)(z:Fintype.card n * (2*k)≤1)(hp:Sea P p)(hq:Sea Q q): |‖inner ℂ p q‖-1| ≤ 4*Fintype.card n*k:=by
 let F:=P*Q; let N:=F*star F+(1-P); let A:=inner ℂ p q; have he:‖N-1‖≤k:=land h g w v
 have hg := prismK g h (Delta.trace_near h g (w.trans_lt (v.trans_lt (by norm_num)))) 1 q hq p hp
 simp only [skyGlow,quant_one,act_one,mul_one] at hg; have hz:((‖A‖^2:ℝ):ℂ)=Complex.exp (invoice (N-1)):=by rw [factor _ (he.trans_lt (v.trans_lt (by norm_num))),add_sub_cancel]; exact hg
 have hh :‖invoice (N-1)‖≤Fintype.card n*(2*k):= (norm_I (he.trans v)).trans (by gcongr)
 have hu : ‖((‖A‖^2:ℝ):ℂ)-1‖ ≤ 2*(Fintype.card n*(2*k)):= hz.symm ▸ ((Complex.norm_exp_sub_one_le (hh.trans z)).trans (by gcongr)); rw [← Complex.ofReal_one,←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hu; change |‖A‖-1|≤ _; rw [show ‖A‖^2-1=(‖A‖-1)*(‖A‖+1) by ring,abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖A‖+1)] at hu; exact (le_mul_of_one_le_right (abs_nonneg _) (by simp : 1 ≤ ‖A‖+1)).trans (hu.trans_eq (by ring))
end YM.CF.Pic
