import YM.CF.Thera.Hang
/-! # Excitation tilt, any sector
 Weight by λ^k with k the number of holes+particles above tickA.
 Control even when IN THE WRONG TOPOLOGICAL SECTOR as orthogonal projection revision.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 150000
noncomputable section
namespace YM.CF.Velvet
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
open Fock Function Filter NormedSpace Finset
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n][LinearOrder n]
variable (P T:Op n)(z:ℝ)
-- T reference fixed, P arbitrary
/-- small projection trailed by fee, on any n -/
def gate := T+(z^2:ℝ) • (1-T)
def hinge:Op n:= P*(gate T z * gate T z)*P + (1-P)
def panel :Op n:=gate T z*P*(hinge P T z)⁻¹
-- gate not actual fence; full λ^-1 times gate, choose unit
/-- projection along orthogonal -/
def draft :Op n := panel P T z *(P * gate T z)
/-- one particle operator. -/
def castV:= z⁻¹ • gate T z
-- determinant comparison uses log z • traces
variable {P T z}
lemma gate_shine (h:IsStarProjection T)(z):star (gate T z)=gate T z:=by rw [gate,star_add,star_smul,h.one_sub.isSelfAdjoint,h.isSelfAdjoint]; rfl
lemma gate_sq (h:IsStarProjection T)(z:ℝ) :gate T z*gate T z= T+ (z^4:ℝ) • (1-T) := by unfold gate; simp only [mul_add,add_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Porth h,show (1-T)*T=0 from (by rw [sub_mul,one_mul,h.isIdempotentElem,sub_self]),smul_zero,add_zero,h.isIdempotentElem.eq,h.one_sub.isIdempotentElem.eq,zero_add,smul_smul]; ring_nf
lemma hinge_price (h:IsStarProjection P)(p:IsStarProjection T)(z): hinge P T z=1-(1-z^4) • (P*(1-T)*P):=by
 unfold hinge; rw [gate_sq p]; rw [mul_add,Algebra.mul_smul_comm,add_mul,Algebra.smul_mul_assoc,sub_smul,one_smul]; rw [mul_sub,mul_one,sub_mul,h.isIdempotentElem]; abel
lemma hinge_shine (h:IsStarProjection P)(p:IsStarProjection T)(z):star (hinge P T z)=hinge P T z:=by rw [hinge_price h p,star_sub,star_one,star_smul,star_mul,star_mul,h.isSelfAdjoint,p.one_sub.isSelfAdjoint,←mul_assoc]; rfl
lemma hinge_slot (h:IsStarProjection P)(p:IsStarProjection T)(z): Commute P (hinge P T z):=by rw [hinge_price h p]; exact (Commute.one_right P).sub_right ((show Commute P (P*(1-T)*P) from (by unfold Commute SemiconjBy; rw [←mul_assoc,←mul_assoc,h.isIdempotentElem,mul_assoc (P*(1-T)),h.isIdempotentElem])).smul_right _)
lemma gate_unit (h:IsStarProjection T)(e:0<z):gate T z*gate T z⁻¹=1:=by
 unfold gate; simp only [mul_add,add_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Porth h,show (1-T)*T=0 from (by rw [sub_mul,one_mul,h.isIdempotentElem,sub_self]),smul_zero,add_zero,h.isIdempotentElem.eq,h.one_sub.isIdempotentElem.eq,zero_add,smul_smul, inv_pow, inv_mul_cancel₀ (pow_pos e 2 |>.ne'),one_smul]; abel
lemma cast_shine (p:IsStarProjection T)(z:ℝ) :star (castV T z)=castV T z:=by rw [castV,star_smul,gate_shine p]; rfl
lemma cast_back (p:IsStarProjection T)(c:0<z): castV T z*castV T z⁻¹=1:=by unfold castV; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,gate_unit p c,inv_inv,smul_smul,mul_inv_cancel₀ c.ne',one_smul]
section solved
variable [Nonempty n]
lemma hinge_budget (h:IsStarProjection P)(p:IsStarProjection T)(c:0≤z)(l:z≤1): ‖1-hinge P T z‖≤1-z^4:=by
 have hp:0≤1-z^4 := sub_nonneg.mpr (pow_le_one₀ c l)
 rw [hinge_price h p,sub_sub_cancel,norm_smul,Real.norm_of_nonneg hp]; apply mul_le_of_le_one_right hp
 refine (norm_mul_le ..).trans ((mul_le_mul (le_trans (norm_mul_le ..) (mul_le_one₀ ?_ ?_ ?_)) (h.norm_le _) (norm_nonneg _) (by norm_num : (0:ℝ) ≤1)).trans (by simp)); all_goals first | exact h.norm_le _| exact p.one_sub.norm_le _| positivity
lemma hinge_unit (h:IsStarProjection P)(p:IsStarProjection T)(c:0<z)(l:z≤1): IsUnit (hinge P T z):= nearOne ((hinge_budget h p c.le l).trans_lt (sub_lt_self 1 (pow_pos c 4)))
lemma panel_lit (h:IsStarProjection P)(p:IsStarProjection T)(c:0<z)(l:z≤1):let A:=panel P T z; let B:= gate T z*P
 draft P T z=A*star B ∧ star A* B=P ∧ A*P=A ∧ A*star B=B*star A:=by
 intro A B; let f:= hinge P T z; have ht:star B=P*gate T z:=by unfold B; rw [star_mul,h.isSelfAdjoint,gate_shine p]
 have hc:=hinge_unit h p c l
 have hv: star f⁻¹=f⁻¹:=by rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_nonsing_inv,← Matrix.star_eq_conjTranspose, show star f=f from hinge_shine h p z] -- tune
 have hg:P*f⁻¹=f⁻¹*P:=by
   have hh: P*f=f*P:=(hinge_slot h p z).eq; calc
    _ = f⁻¹*(f*P)*f⁻¹ := by rw [←mul_assoc,(live hc).2,one_mul]
    _ = f⁻¹*P := by rw [←hh,←mul_assoc,mul_assoc (f⁻¹*P),(live hc).1,mul_one]
 have hn: B*P=B:=by unfold B; rw [mul_assoc,h.isIdempotentElem]
 have he :A=B*f⁻¹:=rfl; have hy:star A=f⁻¹*star B:=by rw [he,star_mul,hv]
 have hx:star B*B=f*P:=by
   rw [ht]; unfold f hinge B; rw [add_mul, mul_assoc (P*(_*_)),h.isIdempotentElem,sub_mul,one_mul,h.isIdempotentElem,sub_self,add_zero]; simp only [mul_assoc]
 refine ⟨by rw [ht]; rfl,by rw [hy,mul_assoc,hx,←mul_assoc,(live hc).2,one_mul],by rw [he,mul_assoc,←hg, ←mul_assoc,hn],by rw [hy,he,mul_assoc]⟩
lemma draft_lit (h:IsStarProjection P)(p:IsStarProjection T)(c:0<z)(l:z≤1): IsStarProjection (draft P T z) ∧ (draft P T z).trace=P.trace ∧ draft P T z * (gate T z*P)=gate T z*P:=by
 let A:=panel P T z; let B:=gate T z*P; let D:=draft P T z; obtain ⟨(hp:D=A*star B),w,u,q⟩:=panel_lit h p c l
 have hq:D=B*star A:= hp.trans q -- lean?
 have hv:D*B=B:=by rw [hq,mul_assoc,show star A*B=P from w]; unfold B; rw [mul_assoc,h.isIdempotentElem.eq];
 refine ⟨⟨show D*D=D from (?_), show star D=D from ?_⟩,by change D.trace=_; rw [hq,Matrix.trace_mul_comm,show star A*B=P from w],hv⟩
 · nth_rw 2 [hq]; rw [←mul_assoc,hv,←hq];
 · nth_rw 1 [hp]; rw [star_mul,star_star,hq]
lemma gate_clad (h:IsStarProjection P)(p:IsStarProjection T)(c:0<z)(l:z≤1) : Clad P (draft P T z) (castV T z) (castV T z⁻¹) ((z:ℝ) • star (panel P T z)):=by
 let A:=panel P T z; let B:=gate T z*P; let d:=draft P T z; obtain ⟨g,v,(he:d*B=B)⟩:=draft_lit h p c l; obtain ⟨p0,(w:star A*B=P),(u:A*P=A),q⟩:=panel_lit h p c l
 have hp:d*castV T z*P=z⁻¹ • B:=by rw [mul_assoc,castV,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,he];
 have hv:d=B*star A:=p0.trans q
 have hz:P*star A=star A:=by nth_rw 1 [←h.isSelfAdjoint]; rw [←star_mul,u]
 refine ⟨h,g,by rw [cast_shine p]; exact mul_eq_one_comm.mp (cast_back p c),?_,?_,?_,?_⟩
 · rw [hp,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; change _ • (z • (star A* B))= _; rw [w, inv_smul_smul₀ c.ne']
 · rw [hp,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; change _ • (z⁻¹ • (B*star A))=_; rw [smul_inv_smul₀ c.ne',←hv]
 · rw [Algebra.mul_smul_comm,hz]
 · change (z • star A)*d =_; rw [Algebra.smul_mul_assoc,hv,←mul_assoc,w,hz]
lemma gate_trace (h:IsStarProjection P)(p:IsStarProjection T)(c:0<z)(l:z≤1)(x:Wave n)(e:Sea P x):
 ∃ y:Wave n, Sea (draft P T z) y ∧ acts (quant (castV T z)) x= ((‖acts (quant (castV T z)) x‖:ℝ) • y) := by
 let W:= castV T z; let K:= draft P T z; have hX:=gate_clad h p c l; have ht: K*W*P=W*P:= by rw [mul_assoc]; unfold W castV; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,draft_lit h p c l|>.2.2] -- tune
 let Y:=acts (quant W) x; let y:=‖Y‖⁻¹ • Y; have he:acts (quant (throat P K W)) x=Y:=by unfold throat; rw [ht,quant_mul,act_mul]; show acts _ (_)=acts _ _; congr 1; nth_rw 1 [←e.1]; rw [←act_mul,line_quant h,e.1] -- tune
 have hs:0<‖Y‖:= norm_pos_iff.mpr (he ▸ shownF hX e)
 have hu: acts (lineOp K) Y=Y:=he ▸ (by rw [←act_mul,near_c hX,act_mul,e.1]) -- wrong rw goal transport
 exact ⟨y,⟨by unfold y; rw [(acts _).map_smul_of_tower,hu],by unfold y; rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ hs.ne']⟩,(smul_inv_smul₀ hs.ne' _).symm⟩
-- amplitude determination
variable (T P z)
def ante := Real.exp ((Matrix.trace T).re*Real.log z)
def sineW (x:Wave n) := ante T z * ‖acts (quant (castV T z)) x‖
/-- total amplitude log of tilted wave. all determinants same sizes. -/
def trade := (Matrix.trace (T-P)).re*Real.log z + Real.log ‖Matrix.det (hinge P T z)‖ /2
variable {P T z}
-- determinant factoring
lemma cut_pitch {X:Op n}(p:IsStarProjection P)(h:X*P=X)(e:P*X=X) (t:ℝ) : ∃ k:ℕ,P.trace=(k:ℂ) ∧ ∀ t:ℝ, Matrix.det (t • X+(1-P))=(t:ℂ)^k*Matrix.det (X+(1-P)):=by
 obtain ⟨F,W,w⟩:=spot_projection P p
 refine ⟨W.card, w ▸ (by rw [trace_twist,trace_cut]),fun t=>?_⟩; -- t shadow
 rw [show t • X + (1-P)= (t • P+(1-P))*(X+(1-P)) from ?_, Matrix.det_mul]; swap; · rw [mul_add,add_mul,add_mul,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,Porth p,p.one_sub.isIdempotentElem.eq,sub_mul,one_mul,e,sub_self,smul_zero,add_zero,zero_add]
 let f(i:n):ℂ:= if i∈ W then t else 1; congr 1
 rw [w,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; change Matrix.det ((t:ℂ) • twist F _ +(1- twist F _))=_; rw [←twist_scalar, ←map_one (twist F),←map_sub,←map_add, det_twist]; -- tune
 rw [show (t:ℂ) • cutM W+(1-cutM W)=Matrix.diagonal f from (by
    ext i j; by_cases u:i=j; · subst j; by_cases p:i∈W<;> simp [f,p,cutM]
    simp [cutM,u]),Matrix.det_diagonal]; unfold f; rw [prod_ite,prod_const_one,mul_one,prod_const]; simp only [filter_mem_eq_inter,univ_inter]
lemma trace_price (p:IsStarProjection P)(q:IsStarProjection T)(c:0<z)(l:z≤1)(x:Wave n)(h:Sea P x):Real.exp (trade P T z)= sineW T z x:=by
 let E:= gate T z; let f:=hinge P T z; let A:=P*(gate T z*gate T z)*P; let d:=sineW T z x; let W:=castV T z
 obtain ⟨k,t,G⟩:=cut_pitch p (X:=A) (by unfold A; rw [mul_assoc (P*(_*_)),p.isIdempotentElem]) (by unfold A; rw [←mul_assoc,←mul_assoc,p.isIdempotentElem]) 1
 let R:=(acts (quant W)) x; have hp:0< ‖R‖:= norm_pos_iff.mpr fun r=> ?_; swap; · have hs:= congr_arg (acts (quant (castV T z⁻¹))) r; unfold R at hs; rw [←act_mul,←quant_mul,mul_eq_one_comm.mp (cast_back q c),quant_one,map_zero,act_one] at hs; apply (norm_pos_iff.mp ((h.2).symm ▸ zero_lt_one)) hs
 have hx: skyGlow x (W*W) x = (↑(‖R‖^2):ℂ):=by unfold skyGlow; nth_rw 1 [← show star W=W from cast_shine q z]; rw [quant_mul,quant_star,act_mul (star (quant W)),← act_inner]; change inner ℂ (acts _ x) R=_; rw [star_star,Complex.ofReal_pow]; exact inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (x:=R) -- tune
 have he: P*(W*W)*P=(z⁻¹*z⁻¹) • A:= by unfold A W castV; simp_rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,smul_smul]
 rw [Thera.meadow p x h,he,G] at hx
 have hu:‖R‖^2=(z⁻¹*z⁻¹)^k * ‖Matrix.det f‖:=by
    rw [←show ‖((↑(‖R‖^2):ℂ))‖=‖R‖^2 from (by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]),←hx,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)]; rfl
 let r:= hinge_unit p q c l; have hy:0< ‖Matrix.det f‖:=norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det f).mp r).ne_zero
 calc Real.exp (trade P T z) = Real.exp (Real.log (sineW T z x)) := by
       congr 1; have he := congr_arg Real.log hu; rw [Real.log_pow,Real.log_mul (by positivity) hy.ne',Real.log_pow,Real.log_mul (by positivity) (by positivity), Real.log_inv] at he; unfold trade sineW ante -- tune
       rw [Matrix.trace_sub, Complex.sub_re,t,Complex.natCast_re,Real.log_mul (Real.exp_pos _).ne' hp.ne',Real.log_exp]; apply Eq.trans (b:= T.trace.re*Real.log z+ Real.log ‖R‖) _ rfl; norm_num1 at he; unfold f at he; linarith only [he] -- let folded f
      _ =_:= Real.exp_log (mul_pos (Real.exp_pos _) hp)
lemma free_ante (W:Finset n) (c:0<z)(x:Wave n)(p:Sea (cutM W) x): let T:=cutM W; let D:= ante T z • quant (castV T z); star D=D ∧ acts D x=x:=by
 -- usual λ^exc weight
 intro T D
 have hp:=cutM_idp W; refine ⟨?_,?_⟩
 · unfold D; rw [star_smul,←quant_star,cast_shine hp]; rfl
 let U(i:n):ℂ:= if i∈W then (z⁻¹:ℝ) else z; let b:= basisKet W
 have he: castV T z=Matrix.diagonal U:=by
    ext i j; by_cases y:i=j; swap; · simp [castV,gate,T,cutM,y]
    subst j; by_cases e:i∈W<;> simp [castV,gate,T,cutM,U,sq,e,Complex.real_smul]; field_simp
 have hl: ante T z = z^W.card:=by unfold ante T; rw [trace_cut,Complex.natCast_re,Real.exp_nat_mul,Real.exp_log c]
 rw [show x= (x.ofLp W) • b from ?_]; swap
 · have hh:= p.1; rw [cutLine,cut_oneAct] at hh; exact hh.symm
 rw [map_smul]; congr 1; unfold D; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rw [act_smul,hl, he,quant_diag,diag_basis,smul_smul]; change ((↑(z^W.card):ℂ)*(∏ i∈W,U i)) • b=b
 rw [show (∏ i∈W,U i)=((z:ℂ)⁻¹)^ W.card from ?_,inv_pow,Complex.ofReal_pow,mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast c.ne')),one_smul]; refine prod_eq_pow_card (fun _ h=>?_); simp [U, h]
end solved
end YM.CF.Velvet
#print axioms YM.CF.Velvet.gate_trace
#print axioms YM.CF.Velvet.trace_price
#print axioms YM.CF.Velvet.free_ante
