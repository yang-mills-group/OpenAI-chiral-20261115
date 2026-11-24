import YM.SU5.Relativistic.Sable
import YM.CF.BPress.Spin.Blank
import YM.SU5.Relativistic.Caffeine
import YM.CF.Fixed.ShellAngle
/-! # soft crater vs that *full* flat price. Use integrability also through pm with no
 leftover disorder. Work on actual torus spectrum exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Papyrus.Granat
open Function Filter NormedSpace Finset Lattice Laurent Bloch Lat Fock Fir Nacre Scroll Thera Tulip Tenant Ember SU SU.Pair Cube Rush Dial Next.Free
open BPress.Spin BPress.Spin.Blank Fixed.Extensive
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
open GaugeFlux
variable {N:Side}{j:ℕ}{M:Tulip.Male}{a b c r:ℝ}
private lemma l_add(A B:Momentum → Op SpinIdx):lens A N+lens B N=lens (fun p=>A p+B p) N:=by
 apply eq_of_sub_eq_zero; rw [add_comm,add_sub_assoc,l_sub]; let L:=lens B N; rw [show (fun p:Momentum=> A p-(A p+B p))=(fun p=>(-1:ℝ) • (B p)) from (?_), ← l_scale]; simp only [neg_smul,one_smul,add_neg_cancel] -- specify ℝ
 ext; simp
private abbrev fund{j:ℕ}{M:Tulip.Male}(a:ℝ)(k:Momentum): Op SpinIdx:=let F:=angle true; let Q:=bent true j M.val k; F*(Q+a^2 •(1-Q))*F+(1-F) -- implicit j m?
private def heft (j:ℕ)(M:Tulip.Male)(x:Site N):ℝ:= ‖shell j M.val (mel x)‖
private def actin (j:ℕ)(M:Tulip.Male)(x:Site N)(a:ℝ):ℝ:=a^2+(1-a^2)*heft j M x
private lemma u_star : IsStarProjection (angle true) := lid true ▸ cutM_idp (cup true) -- reverse?
private abbrev cun := (cup true).card
-- tune
private lemma buck (x:Site N): Matrix.det (fund (j:=j) (M:=M) a (mel x))= (actin j M x a:ℂ)^cun:=by
 let z:=heft j M x; let U:=angle true; let Q:=bent true j M.val (mel x); have hu:U*Q*U=z • U:=cube_law N true j M x
 let V:ℝ:=actin j M x a; have hv : z+a^2*(1-z)=V:=by unfold V actin z; ring
 have he: fund (j:=j) (M:=M) a (mel x)= V • U+(1-U):=by
    change U*(Q+a^2 • (1-Q))*U+(1-U)=_; rw [mul_add,add_mul,hu,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_sub,mul_one,sub_mul,hu,show U*U=U from u_star.isIdempotentElem.eq, ←hv, add_smul,mul_smul,sub_smul,one_smul]
 let f(i:SpinIdx):ℂ:= if i∈cup true then V else 1
 rw [he,show V • U+(1-U)=Matrix.diagonal f by unfold U; rw [lid]; ext i j; by_cases h:i=j; subst j; by_cases h:i∈cup true <;> simp [f,h,cutM,Complex.real_smul]; simp [f,h,cutM], Matrix.det_diagonal]; rw [←prod_filter_of_ne (_ : ∀ i∈ (univ: Finset SpinIdx), f i ≠ 1 → i ∈ cup true), show (univ.filter fun i=> i∈cup true)=cup true by simp]; swap
 · intro i _ h; contrapose! h; simp [f,h]
 rw [prod_congr (g:=fun i=>(V:ℂ)) rfl (fun i e=> if_pos e),prod_const]
private lemma linen (h:1≤j) : Bolt (tickA N) (spar j M (1:Bkg (More N))) a= lens (fund (j:=j) (M:=M) a) N:=by
 have he:spar j M (1:Bkg (More N))=lens (bent true j M.val) N:= nativeP N true j M h
 unfold Bolt; rw [←t_comp]; rw [he,t_lamp, ←l_one,l_sub,l_scale,l_add,l_mul,l_mul,l_sub,l_add]
private lemma axesL (h:1≤j) : Matrix.det (Bolt (tickA N) (spar j M (1:Bkg (More N))) a)= (((∏ x:Site N,(actin j M x a)^cun)^45:ℝ):ℂ):=by
 rw [linen h,BPress.Spin.Blank.lens,scalarP,Matrix.det_kronecker,Matrix.det_one,one_pow,mul_one,plates, twist_formula,Matrix.det_mul,Matrix.det_mul,mul_right_comm,←Matrix.det_mul,show (overU N SpinIdx).val*star (overU N SpinIdx).val= 1 from (overU N SpinIdx).property.2,Matrix.det_one,one_mul,slots]; unfold Rush.mark; rw [Mir.jump_det]; push_cast; simp_rw [buck] -- tune names
private lemma tick (h: 1≤j)(p:∀ x:Site N, 0<actin j M x a) : crater (tickA N) (spar j M (1:Bkg (More N))) a=(45*cun/2:ℝ)*∑ i:Site N,Real.log (actin j M i a):=by
 rw [crater,axesL h,Complex.ofReal_re, Real.log_pow, Real.log_prod (fun i _=> (pow_pos (p i) cun).ne')]; simp_rw [Real.log_pow]; rw [←mul_sum]; push_cast; ring
private lemma halt (Q:IsStarProjection (spar j M (1:Bkg (More N)))) : crater (tickA N) (spar j M (1:Bkg (More N))) 0=seaPrec j N M:=by
 let W:=tickA N; have h:IsSelfAdjoint W:=(show IsStarProjection (tickA N) from (by rw [←t_comp]; exact cutM_idp _)).isSelfAdjoint
 unfold crater Bolt seaPrec OrbT; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_smul,add_zero, mul_one,star_mul,show star (tickA N)=tickA N from h,Q.isSelfAdjoint.star_eq,←mul_assoc, neg_div, neg_neg]; let P:=spar j M (1:Bkg (More N)); change _=Real.log ((W*P*P*W+(1-W)).det.re)/2; rw [mul_assoc W P P,show P*P=P from Q.isIdempotentElem.eq] -- tune
private lemma tau_sum (x:Per N):1≤tauL N.val x.val+tauR N.val x.val:=by unfold tauL tauR; rw [←add_div,le_div_iff₀ (by exact_mod_cast N.property)]; linarith
private abbrev recq (x:ℝ):= (Real.sqrt x)⁻¹
private lemma togetherF {a b:ℝ}(p:0<a)(q:0<b)(h:1≤a+b): recq (a*b)≤ 2*(recq a+recq b):=by
 have ht(x:ℝ)(h:1/2≤x): recq x≤2:=by
    have hx:0<x:=by linarith
    unfold recq; rw [inv_le_comm₀ (by positivity) (by norm_num)] -- type
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
 unfold recq; rw [Real.sqrt_mul p.le,mul_inv] -- simp recq unfold?
 change recq a * recq b≤2*(recq a+recq b)
 obtain e|e:= le_total (1/2:ℝ) a; · apply (mul_le_mul_of_nonneg_right (ht a e) (show 0≤recq b by unfold recq; positivity)).trans (mul_le_mul_of_nonneg_left _ (by norm_num)); linarith [show 0≤recq a by unfold recq; positivity]
 apply (mul_le_mul_of_nonneg_left (ht b (by linarith)) (show 0≤recq a by unfold recq; positivity)).trans; linarith [show 0≤recq b by unfold recq; positivity]
private lemma recipSum (n:ℕ): ∑ i∈ range n, recq (tauL n i) ≤ 2*n:=by
 have he(m:ℕ):∑ i∈range m, recq ((i:ℝ)+1)≤ 2*Real.sqrt m:=by
    induction m with
    | zero=>simp
    | succ m ih=>
       let x:ℝ:=m; let A:= Real.sqrt (x+1); let B:=Real.sqrt x; have hp:0<A:=by unfold A x; positivity
       have hx:A^2=x+1:= Real.sq_sqrt (by unfold x; positivity); have hb:B^2=x:=Real.sq_sqrt (by positivity)
       rw [sum_range_succ]; push_cast; apply (add_le_add_left ih _).trans; change 2*B+A⁻¹≤2*A; apply add_le_of_le_sub_left ?_; apply (inv_le_iff_one_le_mul₀ hp).mpr; nlinarith only [hx,hb,sq_nonneg (A-B)] -- tune order
 rcases Nat.eq_zero_or_pos n with u|u; · subst n; simp
 have p : 0 < (n:ℝ):= Nat.cast_pos.mpr u
 have h(i:ℕ): recq (tauL n i)=Real.sqrt n *recq ((i:ℝ)+1):=by unfold tauL recq; rw [Real.sqrt_div (by positivity), inv_div]; ring
 simp_rw [h]; rw [←mul_sum]; refine (mul_le_mul_of_nonneg_left (he n) (Real.sqrt_nonneg _)).trans_eq ?_; nlinarith [Real.sq_sqrt p.le]
private lemma revTau (N:Side): ∑ i∈range N.val,recq (tauR N.val i)= ∑ i∈range N.val, recq (tauL N.val i):=by
 rw [←sum_range_reflect (fun i=> recq (tauL N.val i))]; refine sum_congr rfl fun i hi=> ?_; apply congrArg recq; unfold tauL tauR; have hp:=mem_range.mp hi; rw [Nat.cast_sub (by omega : i ≤ N.val-1), Nat.cast_sub (show 1≤ N.val from N.property),Nat.cast_one]; ring
private lemma premium (b c z U:ℝ)(p:0<b)(hc:0<c)(hp:0 < U)(h:c*U^2 ≤ z)(f:b≤1):
    Real.log ((b^2)^2+(1-(b^2)^2)*z) ≤ Real.log z+ 4*b*(Real.sqrt (Real.sqrt c))⁻¹ *recq U :=by
 let A:=(b^2)^2+(1-(b^2)^2)*z; let X:=Real.sqrt (Real.sqrt c); let R:=Real.sqrt U; let t:=b/(X*R)
 have hz:0<z:= (by positivity : 0<c*U^2).trans_le h; have hy: (b^2)^2 ≤1:= pow_le_one₀ (sq_nonneg _) (pow_le_one₀ p.le f)
 have hu:0<A:= add_pos_of_pos_of_nonneg (by positivity) (mul_nonneg (by linarith) hz.le)
 have hh:0<X:=by unfold X; positivity
 have hR:0<R:=by unfold R; positivity
 have ht:0<t:= by unfold t; positivity
 have h':(X*R)^4=c*U^2:=by rw [show 4=2*2 by rfl,pow_mul,mul_pow,mul_pow,show X^2=Real.sqrt c from Real.sq_sqrt (by positivity),show R^2=U from Real.sq_sqrt hp.le,Real.sq_sqrt hc.le]
 have he:A≤ (1+t)^4*z:=by
    have hv:=mul_le_mul_of_nonneg_left h (pow_nonneg ht.le 4); rw [← h',←mul_pow,show t*(X*R)=b from div_mul_cancel₀ _ (by positivity)] at hv
    have hy:(b^2)^2*z≥0:=by positivity
    unfold A; nlinarith only [hy,hv, mul_nonneg ht.le hz.le, mul_nonneg (pow_nonneg ht.le 2) hz.le, mul_nonneg (pow_nonneg ht.le 3) hz.le] -- tune
 change Real.log A≤_; have hs:=(Real.log_le_log hu he); rw [Real.log_mul (by positivity : (1+t)^4≠0) hz.ne',Real.log_pow] at hs; push_cast at hs
 have hK:= Real.log_le_sub_one_of_pos (by positivity :0<1+t)
 have hδ:b*X⁻¹*recq U=t:=by unfold t recq R; ring
 change _≤ _+4*b*X⁻¹*_; rw [show 4*b*X⁻¹*recq U=4*t from by rw [←hδ]; ring]; linarith
private lemma norm_support (N:Side):∑ i:Site N,recq (tauL N.val (i 0).val *tauR N.val (i 0).val) ≤8*(N.val:ℝ)^4:=by
 refine (sum_le_sum (fun i _=> togetherF (interval_left (i 0)).1 (interval_right (i 0)).1 (tau_sum _))).trans ?_
 rw [←mul_sum,sum_add_distrib,translationPrice N (fun x=>recq (tauL N.val x.val)), translationPrice N (fun x=>recq (tauR N.val x.val)), period_sum N (fun x=>recq (tauL N.val x)), period_sum N (fun x=>recq (tauR N.val x)),revTau]
 nlinarith only [mul_le_mul_of_nonneg_left (recipSum N.val) (show 0≤(N.val:ℝ)^3 by positivity)]
include j
lemma soft_flat (h:1≤j): ∃ C:ℝ,0 ≤ C∧∀ b:ℝ,0<b→b ≤ 1 → ∀ N:Side,∀ M:Tulip.Male, IsStarProjection (spar j M (1:Bkg (More N)))→ crater (tickA N) (spar j M (1:Bkg (More N))) (b^2) ≤ seaPrec j N M+C*b*(N.val:ℝ)^4:=by
 obtain ⟨c,p,H⟩:= glens j h; let Y:= (Real.sqrt (Real.sqrt c))⁻¹; let D:ℝ:=45*cun/2; have he:0≤Y:=by unfold Y; positivity
 have hd:0≤D:=by unfold D; positivity
 refine ⟨D*32*Y,(by positivity),fun b hb hy N M Q=>?_⟩
 let f(i:Site N):=tauL N.val (i 0).val*tauR N.val (i 0).val
 let z:= heft (N:=N) j M
 have hp(i):0<f i:= mul_pos (interval_left _).1 (interval_right _).1
 have hu(i):c*f i^2 ≤z i:= le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hp i).le ((mode_lower (i 0)).trans (norm_le_pi_norm (pm i) 0)) 2) p.le) (H M N i)
 have hz(i):0<z i:= (mul_pos p (pow_pos (hp i) _)).trans_le (hu i)
 have hB: (b^2)^2≤1:= pow_le_one₀ (sq_nonneg _) (pow_le_one₀ hb.le hy)
 have hx(i:Site N):0<actin j M i (b^2):=add_pos_of_pos_of_nonneg (by positivity) (mul_nonneg (by linarith) (hz i).le)
 have hO(i: Site N):actin j M i 0=z i:=by simp [actin,z]
 rw [tick h hx,←halt Q,tick h (fun i=> by rw [hO]; exact hz i)]; simp_rw [hO]; let G:=4*b*Y
 refine (mul_le_mul_of_nonneg_left (sum_le_sum (g:= fun i=> Real.log (z i)+G*recq (f i)) (fun i _=> premium b c (z i) (f i) hb p (hp _) (hu _) hy)) hd).trans ?_ -- tune
 rw [sum_add_distrib,←mul_sum]; let A:=∑ i, Real.log (z i); change D*(A+G*_)≤D*A+_
 rw [mul_add]; apply add_le_add_right -- wrong
 unfold G; have hm:∑ i, recq (f i)≤8*(N.val:ℝ)^4:=norm_support N; nlinarith only [mul_le_mul_of_nonneg_left hm (show 0≤D*(4*b*Y) by positivity)]
end YM.CF.Papyrus.Granat
#print axioms YM.CF.Papyrus.Granat.soft_flat
