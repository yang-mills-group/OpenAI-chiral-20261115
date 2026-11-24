import YM.CF.Pic.Ream
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][LinearOrder n][Nonempty n]{P Q R A:Op n}{p q:Wave n}{k v:ℝ}{U:UNI n}{a b c:ℂ}
-- section adjustment. avoid derivative of unnormalized value.
lemma gross(h:IsStarProjection P)(g:IsStarProjection Q)(l: U.valᵀ= -U.val)(t:‖P-Q‖≤k)(e: ‖stage P U.val-U.val‖ ≤1/3)(hp:Sea P p)(hq:Sea Q q)(u:k≤1/16)(w:16*Fintype.card n*k+|(a-b).im|≤1)(B:Complex.exp a • p= filled P U.val)(H:Complex.exp b • q=filled Q U.val): let z:=inner ℂ p q; ‖z-1‖ ≤ 48*(Fintype.card n*k+|(a-b).im|):=by
 intro z; have he: filled P U.val≠0:=by rw [←B]; exact smul_ne_zero (Complex.exp_ne_zero _) (norm_pos_iff.mp (by rw [hp.2]; simp))
 let f:= Fock.spark P U.val (body Q U.val); have hv:= crew h e g t; have hm:(k+k)*2 ≤1/3:=by linarith
 have hl:=Delta.polar_hitch h g (t.trans_lt (u.trans_lt (by norm_num))) (inv_close_le U e).1 (hv.trans_lt (hm.trans_lt (by norm_num))) l l he
 have hz: z=Complex.exp (f+a-b):=by
   rw [←B,←H,map_smul,Sea.scalar h hp] at hl
   change Complex.exp b • (z • p)=Complex.exp f • (Complex.exp a • p) at hl; rw [smul_smul,smul_smul] at hl; have hk:=smul_left_injective ℂ (show p≠0 from fun x=> he (by rw [←B,x,smul_zero])) hl; rw [Complex.exp_sub,Complex.exp_add]; field_simp; exact (mul_comm ..).trans hk
 let D:ℝ:= (f+a-b).im; have hb:= norm_I (hv.trans hm)
 have hk:0 ≤ k:= (norm_nonneg _).trans t
 let K:ℝ:=Fintype.card n*k; have hK:0 ≤ K:=by unfold K; positivity
 have hh:‖f‖ ≤8*K:=by
   unfold f Fock.spark; rw [norm_div]; simp only [Complex.norm_ofNat]; refine le_trans (div_le_div_of_nonneg_right hb (by positivity)) ?_
   unfold K; apply (div_le_iff₀ (show (0:ℝ)<2 by norm_num)).mpr; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ)≤2)) (by positivity)) (by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card n)])
 have hd:|D|≤8*K+|(a-b).im|:=by unfold D; rw [add_sub_assoc,Complex.add_im]; exact (abs_add_le ..).trans (add_le_add ((Complex.abs_im_le_norm _).trans hh) le_rfl)
 let y:=pw D; have hD:y=Complex.exp ((D:ℂ)*Complex.I):=rfl
 have hN:‖y-1‖ ≤ 2*(8*K+|(a-b).im|):=by
   have he:‖(D:ℂ)*Complex.I‖=|D|:=by rw [norm_mul,Complex.norm_real,Complex.norm_I,Real.norm_eq_abs,mul_one]
   apply (Complex.norm_exp_sub_one_le (he.trans_le (hd.trans (show _≤1 from ?_)))).trans; rw [he]; exact mul_le_mul_of_nonneg_left hd (by norm_num)
   unfold K; nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card n)]
 have hi:z=(‖z‖:ℂ)* y:=by rw [hz, Complex.norm_exp ,hD, Complex.ofReal_exp,← Complex.exp_add, show ↑((f+a-b).re)+(D:ℂ)*Complex.I=_ from Complex.re_add_im _]
 have ht:1 ≥ ‖z‖:=(norm_inner_le_norm ..).trans (by rw [hp.2,hq.2]; simp)
 have hr:=needle h g t (by linarith) (show Fintype.card n*(2*k) ≤ 1 by nlinarith [abs_nonneg ((a-b).im),Nat.cast_nonneg (α:=ℝ) (Fintype.card n)]) hp hq
 rw [hi,show (‖z‖:ℂ)*y-1=(‖z‖:ℂ)*(y-1)+(((‖z‖-1):ℝ):ℂ) by push_cast; ring]; apply (norm_add_le ..).trans; rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),Complex.norm_real,Real.norm_eq_abs]; refine (add_le_add ((mul_le_of_le_one_left (norm_nonneg _) ht).trans hN) (show |‖z‖-1|≤_ from hr)).trans ?_; unfold K; nlinarith only [hK,(abs_nonneg ((a-b).im))] -- let hK
lemma wire(h:IsStarProjection P)(g:IsStarProjection Q)(p: ‖P-Q‖≤k)(u:k≤1/3):∃ K:Op n, Clad Q P 1 1 K ∧ ‖laneP P 1 K‖ ≤ 2*k:=by
 let d:=P*Q; let x:=d*star d+(1-P); have hf:=land h g p u; obtain ⟨B,e,E⟩:= port_inv x (hf.trans (by linarith))
 let K:= (1:ℝ)⁻¹ • (star d* B*P); refine ⟨K,bridge g h (Delta.trace_near h g (p.trans_lt (u.trans_lt (by norm_num)))) (by simp) zero_lt_one (show d=_ from ?_) e,?_⟩; simp [d]
 have ht: (1-P)*star d=(1-P)*(Q-P)*P:=by unfold d; rw [mul_sub,star_mul,h.2,g.2,show (1-P)*P=0 by rw [sub_mul,one_mul,h.1,sub_self],sub_zero,mul_assoc] -- tune which sub
 have hz:0≤k:= (norm_nonneg _).trans p
 unfold laneP K; rw [inv_one,one_smul, mul_one,←mul_assoc,←mul_assoc,ht]; -- tune
 have hp:‖(1-P)*(Q-P)*P‖ ≤ k:=by apply (norm_mul_le ..).trans; exact (mul_le_of_le_one_right (norm_nonneg _) (h.norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (h.one_sub.norm_le _)).trans ((norm_sub_rev ..).trans_le p)))
 exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (h.norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_mul hp E (norm_nonneg _) hz).trans_eq (by ring))))
end YM.CF.Pic
