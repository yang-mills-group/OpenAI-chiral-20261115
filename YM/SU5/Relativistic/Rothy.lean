import YM.SU5.Relativistic.Daylen
/-! # budget asymptote even for FULL sea after occupation shear. uniform M. Examining actual z. reuse determinant ledger framing from Frills. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Finset Lattice Laurent Bloch Lat BPress.Spin.Blank Cube Rush SU Fir Nacre Ember Scroll Tulip Tenant Fixed.Extensive
open Papyrus.Granat Thera Dial
open GaugeFlux
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side}{M:Tulip.Male}{j k:ℕ}
local notation "J" => spar j M (1:Bkg (More N))
local notation "χ" => angle true
local notation "O" => Op SpinIdx
local notation "F" => bent true j M.val
lemma l_plus(A B:Momentum→ Op SpinIdx): lens A N+lens B N=lens (fun p=>A p+B p) N:=by
 rw [←sub_neg_eq_add]; rw [show -(lens B N)=lens (fun p=> -B p) N by rw [←neg_one_smul ℝ,l_scale]; simp,l_sub]; simp
lemma l_powB(A:Momentum→ Op SpinIdx) (k:ℕ): lens A N ^ k= lens (fun p=> A p^k) N:=by
 induction k with| zero=> simp [l_one]| succ n h=> rw [pow_succ,h,l_mul]; simp only [pow_succ]
lemma l_rec (A B: Momentum→Op SpinIdx) (k:ℕ): Comb (lens A N) (lens B N) k=lens (fun p=>Comb (A p) (B p) k) N:=by
 induction k with
 | zero=>
    rw [Comb, show (0:Op (Single N))=_ from (show _ = lens (fun _=>(0:Op SpinIdx)) N from ?_),show (fun p=>Comb (A p) (B p) 0)=fun _=>0 from funext (fun p=>rfl)] -- tune
    rw [show (fun _:Momentum=>(0:Op SpinIdx))=fun p=> A p-A p by simp, ←l_sub]; simp
 |succ n ih=> rw [Comb,ih,←l_one,l_sub,l_mul,l_mul,l_mul,l_mul,l_sub,l_mul,l_plus]; rfl
lemma l_zeroEq(A B:Momentum → Op SpinIdx)(h:lens A N=lens B N)(x:Site N): A (mel x)= B (mel x):=by
 unfold BPress.Spin.Blank.lens scalarP at h
 have he:plates N A=plates N B:=by
    apply Matrix.ext; intro i j; let z:Slot:=Classical.arbitrary _
    simpa using congrArg (fun f:Op (Single N)=> f (i,z) (j,z)) h
 unfold plates at he; obtain ht:= (twist _).injective he; ext i j
 have hh:=congrArg (fun f:Op (HopK N)=> f (x,i) (x,j)) ht; simpa only [Rush.mark,jump_apply,Equiv.refl_apply,↓reduceIte] using hh
local notation "Z" => zTar j M
lemma f_native (h: 1≤j)(p:IsStarProjection J)(x:Site N) : IsStarProjection (F (mel x)):=by
 rw [show J=lens F N from nativeP N true j M h] at p; constructor
 · exact l_zeroEq _ _ (show lens _ N=lens F N from (l_mul (N:=N) F F).symm.trans p.isIdempotentElem.eq) x
 exact l_zeroEq _ _ ((l_star _).symm.trans p.isSelfAdjoint.star_eq) x
lemma strip_ge : IsStarProjection χ:=by rw [lid]; exact cutM_idp _
lemma z_cap (h: 1≤ j)(p:IsStarProjection J)(x:Site N) : Z x ≤ 1:=by
 let X:=χ*(1-F (mel x))*χ; have ht:0≤ X:=le_trans (star_mul_self_nonneg ((1-F (mel x))*χ)) (le_of_eq (by rw [star_mul,strip_ge.isSelfAdjoint,(f_native h p x).one_sub.isSelfAdjoint,←mul_assoc,mul_assoc χ,(f_native h p x).one_sub.isIdempotentElem.eq]))
 have he:χ*F (mel x)*χ=Z x • χ:=cube_law N true j M x
 have hx:X=(1-Z x:ℝ) • χ:=by unfold X; rw [mul_sub χ,mul_one,sub_mul,he,strip_ge.isIdempotentElem.eq,sub_smul,one_smul]
 rw [hx,lid, cutM,←Matrix.diagonal_smul] at ht; have hh:=((Matrix.posSemidef_diagonal_iff).mp (Matrix.nonneg_iff_posSemidef.mp ht)) (0:SpinIdx)
 -- complex order
 have he: (0:SpinIdx)∈cup true:=by decide
 have hg:(↑(Z x):ℂ)≤1:=by simpa [he,Complex.real_smul] using hh
 exact hg.1

private def frill (u:ℝ)(k:ℕ):= u+(1-u)^(k+k+1)
private lemma lut(x:Site N): Matrix.det (jeans k χ (F (mel x)))=(↑(frill (Z x) k):ℂ)^(cup true).card:=by
 let z:=Z x; let V:=F (mel x)
 have hx:lace χ V=(1-z:ℝ) • χ:=by unfold lace; rw [mul_sub χ,mul_one,sub_mul, strip_ge.isIdempotentElem.eq,cube_law N true j M x,sub_smul,one_smul]
 let g(i:SpinIdx):ℂ:=if i∈cup true then (frill z k:ℝ) else 1
 have ht: χ^(k+k+1)=χ:=strip_ge.isIdempotentElem.pow_succ_eq (k+k) -- tune
 rw [jeans,hx, show ((1-z:ℝ) • χ)^(k+k+1)=(1-z:ℝ)^(k+k+1) • χ from by rw [smul_pow,ht]]
 rw [show (1:Op SpinIdx)-(1-z:ℝ) • χ+(1-z:ℝ)^(k+k+1) • χ=Matrix.diagonal g from ?_,Matrix.det_diagonal]
 · rw [←prod_filter_of_ne (_ : ∀ i∈ (univ: Finset SpinIdx), g i≠1→i∈cup true), show (univ.filter fun i=>i∈cup true)=cup true by simp,prod_congr (g:=fun _=> (↑(frill z k):ℂ)) rfl (fun i hi=> by simp [g,hi]),prod_const]
   intro i _ hp; by_contra h; exact hp (by simp [g,h])
 rw [lid]; ext i j; by_cases h:i=j
 · subst j; by_cases h:i∈cup true <;> simp [cutM,g,h,frill,Complex.real_smul]
 simp [cutM,g,h,Matrix.one_apply]
lemma l_det (A:Momentum → Op SpinIdx): (lens A N).det=(∏ x:Site N,(A (mel x)).det)^45:=by
 rw [BPress.Spin.Blank.lens,scalarP,Matrix.det_kronecker,Matrix.det_one,one_pow,mul_one, plates,twist_formula,Matrix.det_mul,Matrix.det_mul,mul_right_comm,←Matrix.det_mul,show (overU N SpinIdx).val*star (overU N SpinIdx).val=1 from (overU N SpinIdx).property.2,Matrix.det_one,one_mul]; unfold Rush.mark; rw [Mir.jump_det,slots]
private lemma upCount (h:1≤j)(p:IsStarProjection J) : stunt k (tickA N) J=(45*(cup true).card/2:ℝ)*∑ i:Site N,Real.log (frill (Z i) k):=by
 let Y(p:Momentum):= χ; have hY:lens Y N=tickA N:=((t_lamp N true).symm.trans (t_comp N))
 let G(p:Momentum):=jeans k χ (F p)
 have hG: jeans k (tickA N) J = lens G N:=by
    have hz: J= lens F N:= nativeP N true j M h
    unfold jeans lace; rw [←hY,hz,←l_one,l_sub,l_mul,l_mul,l_sub, l_powB,l_plus]; rfl
 have hx(x:Site N):0<frill (Z x) k:=add_pos_of_pos_of_nonneg (amp j h _ x) (pow_nonneg (sub_nonneg.mpr (z_cap h p x)) _)
 rw [stunt,hG,l_det]; simp_rw [G,lut,norm_pow,norm_prod]
 simp_rw [norm_pow,Complex.norm_real]
 simp only [Real.norm_eq_abs, abs_of_pos (hx _)]
 rw [Real.log_pow,Real.log_prod (fun i _=> (pow_pos (hx i) _).ne')]
 simp_rw [Real.log_pow]; rw [←mul_sum]; push_cast; ring
-- sea direct
private lemma oCount (h:1≤j)(p:IsStarProjection J) : seaPrec j N M=(45*(cup true).card/2:ℝ)*∑ i:Site N,Real.log (Z i):=by
 -- reproduce Frills via contact diagonal
 let Y(p:Momentum):= χ; let G(p:Momentum):=χ*(F p)*χ+(1-χ); let O_:= tickA N
 have hp:IsStarProjection (tickA N):=by rw [←t_comp]; exact cutM_idp _
 have hz:J=lens F N:= nativeP N true j M h
 have hx:O_=lens Y N:=(t_comp N).symm.trans (t_lamp N true)
 have hf(x:Site N):0<Z x:=amp j h M x
 have hu:(O_*J)*star (O_*J)+(1-O_)=lens G N:=by
    rw [star_mul,p.isSelfAdjoint,show star O_=O_ from hp.isSelfAdjoint, ←mul_assoc, mul_assoc O_ J, p.isIdempotentElem.eq,hx,hz,←l_one,l_mul,l_mul,l_sub,l_plus]
 have hv(i:Site N):(G (mel i)).det=(↑(Z i):ℂ)^(cup true).card:=by
    unfold G; rw [cube_law N true j M i,lid]; let f(t:SpinIdx):ℂ:=if t∈cup true then Z i else 1
    rw [show ‖shell j M.val (mel i)‖ • cutM (cup true)+(1-cutM (cup true))=Matrix.diagonal f from (?_),Matrix.det_diagonal]
    · rw [←prod_filter_of_ne (_ : ∀ i∈ (univ: Finset SpinIdx), f i≠1→i∈cup true), show (univ.filter fun i=>i∈cup true)=cup true by simp,prod_congr (g:=fun _=> (↑(Z i):ℂ)) rfl (fun j hi=> by simp [f,hi]),prod_const]; intro i _ hp; by_contra h; exact hp (by simp [f,h])
    ext k l; by_cases h:k=l; subst l; by_cases h:k∈cup true <;> simp [cutM,f,h,Complex.real_smul,zTar]; simp [cutM,h]
 unfold seaPrec OrbT; simp only [ne_eq,add_zero, mul_one, neg_div, neg_neg]; rw [hu,l_det,show (∏ x:Site N,(G (mel x)).det) ^45= (( (∏ x:Site N,(Z x)^(cup true).card) ^45:ℝ):ℂ) from (by push_cast; simp_rw [hv]),Complex.ofReal_re,Real.log_pow,Real.log_prod (fun i _=> (pow_pos (hf i) _).ne')]; simp_rw [Real.log_pow]; rw [←mul_sum]; push_cast; ring
-- uniform low budget (also later for X tail)
lemma stintE(ε:ℝ)(e:0<ε): ∀ᶠ k:ℕ in atTop,∀ z:ℝ, 0<z → z≤1→ (1-z)^k * Real.sqrt z ≤ ε:=by
 let d:= min 1 ε; have hp:0<d:=lt_min zero_lt_one e; let A:=1-d^2; have hv:0≤A:=sub_nonneg.mpr (pow_le_one₀ hp.le (min_le_left ..)); have hx:A<1:=sub_lt_self _ (pow_pos hp _)
 filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one hv hx).eventually (ge_mem_nhds e)] with k v z t f
 obtain g|g:= le_total z (d^2); · exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (sub_nonneg.mpr f) (by linarith))).trans (((Real.sqrt_le_sqrt g).trans_eq (Real.sqrt_sq hp.le)).trans (min_le_right ..))
 exact (mul_le_of_le_one_right (pow_nonneg (sub_nonneg.mpr f) _) ((Real.sqrt_le_sqrt f).trans_eq Real.sqrt_one)).trans ((pow_le_pow_left₀ (sub_nonneg.mpr f) (sub_le_sub_left g 1) _).trans v)
lemma purge (j:ℕ)(h:1≤j)(ε:ℝ)(t:0<ε): ∀ᶠ k:ℕ in atTop,∀ N:Side,∀ M:Tulip.Male, IsStarProjection (spar j M (1:Bkg (More N))) → stunt k (tickA N) (spar j M (1:Bkg (More N))) ≤ seaPrec j N M+ε*N.val^4:=by
 obtain ⟨C,p,u⟩:= bills j h
 let V:ℝ:= 45*(cup true).card/2; have hv:0<V:=div_pos (mul_pos (by norm_num) (by rw [show (cup true).card=2 from by decide]; norm_num)) (by norm_num)
 let q:=ε/(V*C); have hh:0<q:=div_pos t (by positivity)
 filter_upwards [stintE q hh] with k t N M hP; rw [upCount h hP,oCount h hP]
 let W:=zTar (N:=N) j M
 have he(i:Site N): Real.log (frill (W i) k) ≤ Real.log (W i)+q*(hard (W i))⁻¹:=by
    let z:=W i; let r:= (1-z)^(k+k+1); have hf:0<z:=amp j h M _; have hn:z≤ 1:=z_cap h hP _; have hR:0≤r:=pow_nonneg (sub_nonneg.mpr hn) _
    change Real.log (z+r) ≤ _; have ht:z+r=(1+r/z)*z:=by rw [add_mul,one_mul,div_mul_cancel₀ _ hf.ne']
    have hy:0<1+r/z:=by positivity
    have hT: r*Real.sqrt z ≤ q:=(mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (sub_nonneg.mpr hn) (by linarith) (show k ≤ k+k+1 by omega)) (Real.sqrt_nonneg _)).trans (t z hf hn)
    rw [ht, Real.log_mul hy.ne' hf.ne']; let R:=Real.sqrt z; have hp:0<R:=Real.sqrt_pos.mpr hf; have hg:r/z≤ q / R^3:= (div_le_div_iff₀ hf (by positivity)).mpr (by rw [pow_succ R 2, show R^2=z from Real.sq_sqrt hf.le]; nlinarith only [mul_le_mul_of_nonneg_left hT hf.le])
    change Real.log (1+r/z)+Real.log z≤Real.log z + q*(R^3)⁻¹; rw [←div_eq_mul_inv]; linarith only [Real.log_le_sub_one_of_pos hy,hg]
 apply (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> he i)) hv.le).trans; rw [sum_add_distrib, mul_add, ←mul_sum]; apply add_le_add_right; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (u N M) hh.le) hv.le).trans_eq; unfold q; field_simp
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.purge

