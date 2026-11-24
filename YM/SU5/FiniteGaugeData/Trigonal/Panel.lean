import YM.SU5.FiniteGaugeData.Trigonal.Gash
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option linter.unusedSimpArgs false
namespace YM.CF.Window.Trigo
open Function Filter Finset Metric
open Laurent Lattice Next.Free Bloch Fir Lat ArchiveK Largo WithLp MeasureTheory Complex
open scoped Topology BigOperators Set Pointwise InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra μFin
set_option quotPrecheck false
section
private lemma globe_zero{f:ℂ→ℂ}(h:Differentiable ℂ f)(p:∀ᶠ x:ℝ in 𝓝[>] 0,f x=0): f= fun _=>0:=by
 refine DifferentiableOn.analyticOnNhd h.differentiableOn isOpen_univ |>.eq_of_frequently_eq analyticOnNhd_const (z₀:=(0:ℂ)) ?_
 intro t; have hp:Tendsto ((↑):ℝ→ℂ) (𝓝[>] (0:ℝ)) (𝓝[≠] 0):= by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; · exact continuous_ofReal.continuousAt.continuousWithinAt
    filter_upwards [self_mem_nhdsWithin] with i u; exact fun e=> (Set.mem_Ioi.mp u).ne' (by exact_mod_cast (show (i:ℂ)=0 from e))
 obtain ⟨x,l,z⟩:= (p.and (hp.eventually t)).exists; exact z l
private lemma seer_{I:Type*}(u:Finset I)(f g:I→ℂ)(p:Injective f)(h:(fun x:ℂ=>∑ i∈u, g i *Complex.exp (x*f i))=fun _=>0): ∀ i∈u,g i=0:=by
 classical
 induction u using Finset.induction_on generalizing g with
 | empty=> simp
 | insert a u t ih=>
    let Z(i):= g i*(f i-f a); have he(x:ℂ):∑ i ∈ insert a u, g i*Complex.exp (x*f i)=0:=congrFun h x
    have hv(x:ℂ):∑ i ∈ insert a u,g i*f i*Complex.exp (x*f i)=0:=by
       let w(i:I)(x:ℂ):= g i*Complex.exp (x*f i); have H(i:I): HasDerivAt (w i) (g i*f i*Complex.exp (x*f i)) x:=by
          let W:= hasDerivAt_id' x; unfold w; rw [mul_assoc,mul_comm (f i)]; simpa only [one_mul] using (HasDerivAt.cexp (W.mul_const (f i))).const_mul (g i) -- tune
       have ht:= HasDerivAt.fun_sum (u:=insert a u) fun i _=> H i; change HasDerivAt (fun x:ℂ=> ∑ i ∈ insert a u, g i* _) _ x at ht; rw [h] at ht; exact ht.unique (hasDerivAt_const ..) -- tune ht W
    have hp(x:ℂ):(∑ i∈u,Z i*Complex.exp (x*f i))=0:=by
       suffices hz: (∑ i∈ insert a u,Z i*Complex.exp (x*f i))=0 by simpa [Z,t] using hz
       refine Eq.trans (b:=(∑ i∈insert a u, g i*f i*Complex.exp (x*f i)) - f a*(∑ i∈insert a u, g i * Complex.exp (x*f i))) ?_ (by rw [he,hv,mul_zero,sub_self]); rw [mul_sum,←sum_sub_distrib]; unfold Z; apply sum_congr rfl; intro;intro; ring
    specialize ih Z (funext hp); have hk(i:I)(h:i∈u): g i=0:= (mul_eq_zero.mp (ih i h)).resolve_right (sub_ne_zero.mpr (p.ne (fun h'=>t (h' ▸ h))))
    intro i h; rcases Finset.mem_insert.mp h with rfl |h; · specialize he 0; rw [sum_insert t, sum_eq_zero (fun i h=>by rw [hk i h,zero_mul])] at he; simpa using he
    exact hk i h
lemma flashN {I:Type*}(u:Finset I)(f g:I→ℂ)(p:Injective f)(h:∀ᶠ x:ℝ in 𝓝[>] 0, (∑ i∈u,g i *Complex.exp ((x:ℂ)*f i))=0): ∀ i∈u,g i=0:= seer_ u f g p (globe_zero (by fun_prop) h)
abbrev DotX (p: Momentum)(x:Cover):ℂ:= Complex.I*∑ i,p i*(x i:ℂ)
lemma scaleDot(p:Momentum)(t:ℂ)(x:Cover): mode (t • p) x=Complex.exp (t* DotX p x):=by
 apply congrArg Complex.exp; simp only [DotX,Pi.smul_apply,smul_eq_mul,mul_assoc, ← mul_sum]; ring
lemma PriceSep(a b:E4)(p:Injective (fun x:Cover=> inner ℝ (emitX x) a)): Injective (fun x:Cover=> DotX (needleQ a b) (-x)):=by
 have hp(z:Cover): (DotX (needleQ a b) (-z)).im = -(inner ℝ (emitX z) a):=by
    unfold DotX needleQ pliance; simp only [Complex.mul_im,Complex.re_sum,I_re,I_im,zero_mul,one_mul,zero_add,Complex.mul_re,Pi.neg_apply,Pi.add_apply,brushQ,tmap, Complex.ofReal_re,Complex.add_re,Int.cast_neg,Complex.ofReal_im,Pi.smul_apply,smul_eq_mul,Complex.neg_re, Complex.neg_im,intCast_im,intCast_re]; rw [pis,← sum_neg_distrib]; exact sum_congr rfl (fun i _=>by dsimp only [emit_axis]; ring) -- tune
 intro i j e; exact p (neg_injective (hp i ▸ hp j ▸ congrArg Complex.im e))
#print axioms flashN
#print axioms PriceSep
end
end YM.CF.Window.Trigo
