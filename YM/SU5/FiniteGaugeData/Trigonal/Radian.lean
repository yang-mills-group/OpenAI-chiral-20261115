import YM.SU5.FiniteGaugeData.Largo.Vers
/-! # Holomorphic symbol across physical and complex null punctures. -/
set_option autoImplicit false
set_option maxHeartbeats 390000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Window.Trigo
open Function Filter Metric Finset Complex Lattice Laurent Next.Free Bloch Fir Largo
open scoped Topology BigOperators Set Pointwise
variable {p:Momentum}{j:Cover}{a b:Axis}{x:ℂ}{k:ℤ}{n:ℕ}{C:ℝ}
abbrev doorP:= ball (0:Momentum) 1
def rayD(p:Momentum)(j:Cover):Momentum:= p+reciprocal j
abbrev cashQ (p:Momentum)(j:Cover)(a:Axis):ℂ:= let q:=rayD p j; leer q ^ 8 * (2*q a/pass q)
local notation "q"=> rayD p j
-- Real part of the squared-length denominator.
def pShift(x:ℂ)(k:ℤ):ℂ:=x+2*(Real.pi:ℂ)*k
lemma climatic(p:Momentum)(j:Cover)(a:Axis): rayD p j a=pShift (p a) (j a):=rfl
lemma pShrink (h: p∈doorP) (a:Axis):‖p a‖ ≤1:= (norm_le_pi_norm ..).trans (mem_ball_zero_iff.mp h).le
@[simp] lemma pShift_re : (pShift x k).re=x.re+2*Real.pi*k:= by unfold pShift; simp
@[simp] lemma pShift_im : (pShift x k).im=x.im:= by unfold pShift; simp
abbrev axisR(k:ℤ):ℝ:= 1+|(k:ℝ)|
lemma depth (p':k≠0)(h:‖x‖ ≤1): 4 * |(k:ℝ)| ≤ |(pShift x k).re| :=by
 have hu:= Real.pi_gt_three; rw [pShift_re]; have hh:= abs_le.mp ((Complex.abs_re_le_norm x).trans h); rcases p'.lt_or_gt with t|t
 · have ht:(k:ℝ)≤ -1:= (by exact_mod_cast (show k≤ -1 by omega)); rw [abs_of_nonpos (show (k:ℝ)≤0 by linarith)]; nlinarith only [hu,hh.2,ht,neg_le_abs (x.re+2*Real.pi*k)]
 have ht:(1:ℝ) ≤ k:= (by exact_mod_cast (show 1≤ k by omega)); rw [abs_of_nonneg (show (0:ℝ)≤k by linarith)]; nlinarith only [hu,hh.1,ht,le_abs_self (x.re+2*Real.pi*k)]
private lemma im_safe(h:p∈doorP)(a:Axis): ( ((q) a).im)^2 ≤1:=by rw [climatic,pShift_im]; have H:=abs_le.mp ((Complex.abs_im_le_norm (p a)).trans (pShrink h a)); nlinarith
lemma pass_price(p:Momentum)(j:Cover): (pass (rayD p j)).re= ∑ a:Axis,((rayD p j a).re)^2 - ∑ a:Axis, ((rayD p j a).im)^2:=by
 unfold pass; rw [Complex.re_sum, ←sum_sub_distrib]; simp [sq]
variable (h:p∈doorP)(k0:j≠0)
include h k0
private lemma pass_est : 8 ≤ (pass q).re:=by
 obtain ⟨a,e⟩:=Function.ne_iff.mp k0; change j a≠0 at e
 have he:4≤|((q) a).re|:=by rw [climatic]; apply le_trans _ (depth e (pShrink h a)); have hu: (1:ℝ)≤|(j a:ℝ)|:=(by rw [← Int.cast_abs]; exact_mod_cast (show (1:ℤ) ≤ |j a| from by have hx:= abs_pos.mpr e; omega)); linarith
 rw [pass_price]; have hv: (∑ a:Axis,(((q) a).im)^2) ≤ 4:= (le_trans (sum_le_sum fun i _=>im_safe (j:=j) h i) (by simp [Axis])); have hx:= single_le_sum (fun b _=> pow_two_nonneg (((q) b).re)) (mem_univ a); nlinarith only [hx,he,hv,sq_abs (((q) a).re)]
lemma pass_keep: pass q≠0:=by intro t; have hp:= pass_est h k0; rw [t] at hp; norm_num at hp
lemma pass_cut(a:Axis): ‖((q) a)‖≤ ‖pass q‖:= by
 have he: ‖((q) a)‖^2=((q) a).re^2+((q) a).im^2:=by rw [← Complex.normSq_eq_norm_sq]; unfold Complex.normSq; simp [sq]
 have hv: (∑ a:Axis,(((q) a).im)^2) ≤ 4:= (le_trans (sum_le_sum fun i _=>im_safe (j:=j) h i) (by simp [Axis])); have hx:= single_le_sum (fun b _=> pow_two_nonneg (((q) b).re)) (mem_univ a); have hp:= pass_est h k0; have hk:= pass_price p j; have ht:= im_safe (j:=j) h a; nlinarith only [hp,hv,hx,hk,he,ht,Complex.re_le_norm (pass q)]
#print axisR
#print axioms pass_cut
omit h k0
private lemma sctrl : ∃ C:ℝ,1≤C ∧∀ (m:ℤ) (z:ℂ), ‖z‖ ≤ 1 → ‖Largo.hsinc (pShift z m/2)‖ ≤ C/axisR m:=by
 let f(z:ℂ):= Complex.sin (z/2); let g(z:ℂ):= Largo.hsinc (z/2); let h(z):= max ‖f z‖ ‖g z‖
 have hl:Continuous g:= hschi.continuous.comp (continuous_id.div_const _); have hp:Continuous f:=by unfold f; fun_prop
 obtain ⟨C,hC⟩:= ((isCompact_closedBall (0:ℂ) (1:ℝ)).image (hp.norm.max hl.norm)).bddAbove
 let D:= max 1 C; refine ⟨D,le_max_left ..,fun m z hz=>?_⟩; have he:f z=f z:=rfl; have hZ:h z ≤ D:= (hC ⟨z,mem_closedBall_zero_iff.mpr hz,rfl⟩).trans (le_max_right ..)
 by_cases k:m=0; · subst m; simp [pShift,axisR]; exact (le_max_right ..).trans hZ
 have hw:1 ≤ |(m:ℝ)| :=(by rw [←Int.cast_abs]; exact_mod_cast (show (1:ℤ) ≤ |m| from by have h:=abs_pos.mpr k; omega)); let T:= pShift z m; have hb: axisR m ≤ ‖T/2‖:= by rw [norm_div, Complex.norm_ofNat]; unfold axisR; linarith [depth k hz,show |T.re| ≤ ‖T‖ from Complex.abs_re_le_norm T] -- depth not def visible.T
 have hx:‖Complex.sin (T/2)‖= ‖f z‖:=by
    rw [show T/2=z/2+m*(Real.pi:ℂ) from (by unfold T pShift; ring), show ∀ z:ℂ, Complex.sin (z+m*Real.pi)=(-1:ℂ)^m*Complex.sin z from fun z=> m.cast_negOnePow ℂ ▸ Complex.sin_antiperiodic.add_int_mul_eq m,norm_mul]; simp [f]
 have hv:0<axisR m:=by unfold axisR; positivity
 change ‖hsinc _‖ ≤_; rw [haway _ (norm_pos_iff.mp (hv.trans_le hb)),norm_div,hx]; exact div_le_div₀ (by unfold D; positivity) ((le_max_left ..).trans hZ) hv hb
private lemma cth {C A:ℝ}(j:ℤ)(h:1≤C)(t:0≤A)(L:A ≤ C/axisR j): A^8 ≤ C^8 * gateL j:=by
 let B:=axisR j; have p:1≤ B:=by unfold B axisR; simp
 have e:0<B:=zero_lt_one.trans_le p; have hx: B^2 ≤ B^8:= pow_le_pow_right₀ p (by omega: 2≤8); apply (pow_le_pow_left₀ t L 8).trans; rw [div_pow,div_eq_mul_inv,gateL]; -- tune equality natabs
 refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (by positivity); change _≤ B^8; refine le_trans ?_ hx; unfold B axisR; simp
lemma notes(a:Axis):∃ D:Cover→ℝ,(∀ i,0≤D i) ∧Summable D∧∀ i:Cover,i≠0→∀ p∈doorP, ‖cashQ p i a‖ ≤ D i:=by
 obtain ⟨C,h,t⟩:= sctrl; let D:= (C^8)^4; let g(i:Cover):= D*wick i*2; have hp(i):0≤ D*wick i:= mul_nonneg (by unfold D; positivity) (prod_nonneg (fun j _=>(gate_pp _).le)); refine ⟨g,fun i=>mul_nonneg (hp i) (by norm_num), (wickL.mul_left _).mul_right _,fun j v q' p=> ?_⟩
 let B:=rayD q' j; have hv:= pass_keep p v; have hb:‖2*B a/pass B‖ ≤ 2:=by rw [norm_div,norm_mul, Complex.norm_ofNat,div_le_iff₀ (norm_pos_iff.mpr hv)]; exact mul_le_mul_of_nonneg_left (pass_cut p v a) (by norm_num)
 unfold cashQ; dsimp only; rw [norm_mul]; refine mul_le_mul ?_ hb (norm_nonneg _) (hp _); unfold leer; rw [norm_pow,norm_prod, ←prod_pow]; unfold D wick; exact (prod_le_prod (s:=@univ Axis _) (fun j _=>by positivity) (fun a _=> cth (j a) h (norm_nonneg _) (by rw [climatic]; exact t _ _ (pShrink p _)))).trans_eq (by simp [prod_mul_distrib,Axis])
#print axioms notes
def paperC(p:Momentum)(j:Cover)(a:Axis):ℂ:= if j=0 then 0 else cashQ p j a
def Palm (a:Axis)(p:Momentum):ℂ:=∑' x:Cover, paperC p x a
lemma dues(a:Axis):∃ D:Cover→ℝ, Summable D ∧∀ i:Cover,∀ p∈doorP,‖paperC p i a‖ ≤ D i:=by
 obtain ⟨v,t,u,g⟩:= notes a; refine ⟨v,u,fun i p h=>?_⟩; unfold paperC; split; · rw [norm_zero]; exact t i
 exact g _ (by assumption) _ h -- indentation
lemma shape(a:Axis):DifferentiableOn ℂ (fun x=>paperC x j a) doorP:=by
 unfold paperC; split; · fun_prop
 next he=>
 unfold cashQ leer; dsimp only; intro x k; simp_rw [div_eq_mul_inv]; apply DifferentiableWithinAt.fun_mul; · unfold rayD; fun_prop
 refine DifferentiableWithinAt.fun_mul ?_ ?_; · unfold rayD; fun_prop
 exact ((differentiableAt_inv (pass_keep k he)).comp_differentiableWithinAt x (by unfold pass rayD; fun_prop))
lemma Palm.cont(a:Axis):ContinuousOn (Palm a) doorP:=by obtain ⟨v,p,t⟩:= dues a; exact continuousOn_tsum (fun _=> (shape a).continuousOn) p t
lemma Palm.diff(a:Axis){f:ℂ→Momentum}{s:Set ℂ}(Z:IsOpen s)(h: Set.MapsTo f s doorP)(u:DifferentiableOn ℂ f s):DifferentiableOn ℂ (Palm a∘f) s:=by obtain ⟨D,p,r⟩:= dues a; exact differentiableOn_tsum_of_summable_norm p (fun i:Cover=> (shape (j:=i) a).comp u h) Z (fun i z p=>r i _ (h p))
-- extended (pass p*M(p)) across nulls.
def AcornT(p:Momentum):Momentum:= (fun a=> pass p*(Palm a p)+leer p^8*(2*p a))
lemma blueberry(h:p∈doorP)(a:Axis): Palm a p+cashQ p 0 a= melody p a:=by
 -- tsum update
 obtain ⟨D,k,t⟩:= dues a; let v(j:Cover):= paperC p j a; have he:Summable v:= Summable.of_norm_bounded k (fun i=> t i _ h); let w:= cashQ p 0 a
 change (∑' i:Cover,v i)+w= _ -- parens need
 unfold melody; have hk: (fun i:Cover=> cashQ p i a)= (fun i:Cover=> v i+ (Pi.single (0:Cover) w:Cover→ℂ) i):=by funext i; by_cases g:i=0<;>simp [g,v,w,paperC]
 change _=(∑' i:Cover,cashQ p i a); rw [hk]; rw [Summable.tsum_add he (hasSum_pi_single ..).summable, tsum_pi_single]
lemma AcornT.billing (h:p∈doorP)(k:pass p≠0) : AcornT p= (pass p) • melody p:=by
 funext a; rw [Pi.smul_apply,smul_eq_mul,←blueberry h,mul_add]; change _+ _=_+_; congr 1; unfold cashQ
 rw [show rayD p 0=p from ?_]; field_simp
 unfold rayD; simp [show reciprocal (0:Cover)=0 from (by ext; simp [reciprocal])]
lemma AcornT.null (k:pass p=0): AcornT p= (leer p^8*2) • p:=by funext a; simp only [AcornT,k,zero_mul,zero_add,Pi.smul_apply,smul_eq_mul,mul_assoc]
@[fun_prop] lemma differPass:Differentiable ℂ pass:=by unfold pass; fun_prop
@[fun_prop] lemma differ_leer:Differentiable ℂ leer:=by unfold leer; fun_prop
@[fun_prop] lemma leer_c:Continuous leer:= differ_leer.continuous
lemma AcornT.film{X:ℂ→Momentum}{s:Set ℂ}(Z:IsOpen s)(h:Set.MapsTo X s doorP)(t:DifferentiableOn ℂ X s):DifferentiableOn ℂ (AcornT∘X) s:=by
 apply differentiableOn_pi.mpr; intro a; unfold AcornT; refine ((differPass.comp_differentiableOn t).mul (Palm.diff a Z h t)).add ?_; exact (((differ_leer.comp_differentiableOn t).pow _).mul ((differentiableOn_const _).mul (differentiableOn_pi.mp t a)))
lemma AcornT.cont:ContinuousOn AcornT doorP:=by
 apply continuousOn_pi.mpr; intro a; unfold AcornT; apply (differPass.continuous.continuousOn.mul (Palm.cont _)).add; fun_prop
#print axioms AcornT.billing
#print axioms AcornT.cont
#print axioms AcornT.film
end YM.CF.Window.Trigo
