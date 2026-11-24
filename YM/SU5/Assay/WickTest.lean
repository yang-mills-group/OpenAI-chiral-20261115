import YM.SU5.Assay.Spacers
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}{j:Axis}(S:Semigroup H j)
/-! Four signed receipts and heat deficiency. -/
variable {a b C g e:ℝ}{A M:H.Op}{u:H}{z:ℂ}
lemma inner_stamp (p:‖A‖≤C): (inner ℂ u (A u)).re ≤C*‖u‖^2:=
 (Complex.re_le_norm _).trans ((norm_inner_le_norm ..).trans
   ((mul_le_mul_of_nonneg_left (A.le_opNorm u) (norm_nonneg _)).trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring))))
local notation "ω"=> S.wax
lemma dip_swing (r:ℝ)(A:H.Op)(u:H):
 inner ℂ u ((S.sand A r r) u)=inner ℂ (ω r u) (A (ω r u)):=by
 unfold sand
 rw [ContinuousLinearMap.mul_apply,ContinuousLinearMap.mul_apply,←ContinuousLinearMap.adjoint_inner_left,
    ←ContinuousLinearMap.star_eq_adjoint,wax_symm]
lemma dip_self (h:0≤a)(u:H):‖ω a u‖^2=(inner ℂ u (ω (a+a) u)).re:=by
 rw [←inner_self_eq_norm_sq (𝕜:=ℂ),←S.wax_sq h h,ContinuousLinearMap.mul_apply,
   ←ContinuousLinearMap.adjoint_inner_left (ω a) (ω a u) u,←ContinuousLinearMap.star_eq_adjoint,wax_symm];rfl
lemma dip_bound (u:H)(r:ℝ):‖ω r u‖≤‖u‖:=
 ((ω r).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.wax_pay _))
lemma wickTest (s:0≤a)(r:a≤b)(p:0≤g)
    (q:‖ω (a+a)+z•A‖ ≤1+g)(h:‖ω (b-a+(b-a))-ω (b+b)‖≤e)
    (v:M=S.sand A (b-a) (b-a))(u:H):
    (z*inner ℂ u (M u)).re≤(e+g)*‖u‖^2:=by
 let t:=b-a;have ht:=sub_nonneg.mpr r
 have hs:ω (b+b)=S.sand (ω (a+a)) t t:=by
   unfold sand;rw [wax_sq S ht (by linarith),wax_sq S (by linarith) ht,show b-a+(a+a)+(b-a)=b+b by ring]
 have g₁:= inner_stamp (u:=ω t u) q
 rw [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,inner_add_right,inner_smul_right,
     ←S.dip_swing,←S.dip_swing,←v,←hs,Complex.add_re,add_mul,one_mul] at g₁
 have g₂:=inner_stamp (u:=u) h
 rw [ContinuousLinearMap.sub_apply,inner_sub_right,Complex.sub_re,←S.dip_self ht] at g₂
 linarith only [g₁,g₂,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (S.dip_bound u t) 2) p]

lemma op_budget (h:0≤C)(v:∀u:H, ‖inner ℂ u (M u)‖≤C*‖u‖^2):‖M‖≤4*C:=by
 have K(u:H)(p:‖u‖≤2):‖inner ℂ (M u) u‖≤C*4:=by
    rw [←inner_conj_symm,Complex.norm_conj] -- tune
    exact (v u).trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) p 2).trans_eq (by norm_num)) h)
 refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) (fun x u=>?_)
 by_cases p:M x=0; · rw [p,norm_zero]; positivity
 let a:= ‖M x‖; have t:0<a:=norm_pos_iff.mpr p
 let y:=(a⁻¹:ℂ)•M x; have q: ‖y‖=1:=by
    unfold y; rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg t.le];exact inv_mul_cancel₀ t.ne'
 have hx:‖inner ℂ (M x) y‖=a:=by
    unfold y; rw [inner_smul_right,inner_self_eq_norm_sq_to_K,norm_mul,norm_pow,norm_inv,Complex.norm_real,RCLike.norm_ofReal,Real.norm_of_nonneg t.le,abs_of_nonneg t.le,sq,←mul_assoc]; exact congrArg (· *a) (inv_mul_cancel₀ t.ne') |>.trans (one_mul _)
 have hg: ‖Complex.I•y‖=1:=by rw [norm_smul,Complex.norm_I,q,mul_one]
 have D:= congrArg norm (inner_map_polarization' M.toLinearMap x y)
 let E(u:H):=inner ℂ (M u) u
 change ‖inner ℂ (M x) y‖=‖(E (x+y)-E (x-y)-Complex.I*E (x+Complex.I•y)+Complex.I*E (x-Complex.I•y))/4‖ at D
 change a ≤ _; rw [←hx,D,norm_div]
 apply (div_le_iff₀ (by norm_num:0<‖(4:ℂ)‖)).mpr
 refine (norm_add_le ..).trans ((add_le_add (norm_sub_le ..) (le_refl _)).trans ?_)
 have f₁:=K (x+y) ((norm_add_le ..).trans (by rw [u,q];norm_num))
 have f₂:=K (x-y) ((norm_sub_le ..).trans (by rw [u,q];norm_num))
 have f₃:=K (x+Complex.I•y) ((norm_add_le ..).trans (by rw [u,hg];norm_num))
 have f₄:=K (x-Complex.I•y) ((norm_sub_le ..).trans (by rw [u,hg];norm_num))
 unfold E; simp only [norm_mul,Complex.norm_I,one_mul]
 rw [show ‖(4:ℂ)‖=4 by norm_num]
 linarith only [f₁,f₂,f₃,f₄,norm_sub_le (E (x+y)) (E (x-y))]

lemma wickTest_four (t e:ℝ)(p:0<t)(q:0≤e)
 (h:∀z∈({↑t,-↑t,Complex.I*↑t,-Complex.I*↑t}:Finset ℂ),∀u:H,(z*inner ℂ u (M u)).re ≤ (t*e)*‖u‖^2):‖M‖ ≤4*(2*e):=by
 -- h pointwise
 refine op_budget (mul_nonneg (by norm_num) q) fun u=>?_
 let A:=inner ℂ u (M u)
 have u₁:=h (↑t) (by simp) u
 have u₂:=h (-↑t) (by simp) u
 have u₃:=h (Complex.I*↑t) (by simp) u
 have u₄:=h (-Complex.I*↑t) (by simp) u
 simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.neg_re,
  Complex.I_re,Complex.I_im,Complex.mul_im,mul_zero,neg_mul,one_mul] at u₁ u₂ u₃ u₄
 have h₁:|A.re|≤e*‖u‖^2:=abs_le.mpr (by unfold A; constructor <;> nlinarith only [u₁,u₂,p])
 have h₂:|A.im|≤e*‖u‖^2:=abs_le.mpr (by unfold A; constructor <;> nlinarith only [u₃,u₄,p])
 exact (Complex.norm_le_abs_re_add_abs_im A).trans (by linarith only[h₁,h₂])

end YM.OS.Semigroup
