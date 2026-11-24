import YM.SU5.Relativistic.Krum
import YM.SU5.Relativistic.Frills
/-! # ultraviolet Gram powers. L² control especially singular inverse even after arbitrary shear order; low-tail. Four dimensions. Uniform M. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Finset Fock Thera Lattice Laurent Bloch Lat BPress.Spin.Blank Cube Rush SU Fir Ember Scroll Tulip Fixed.Extensive
open Papyrus.Granat
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {N:Side}
private abbrev slit (t:ℝ) := Real.sqrt (Real.sqrt t)
private abbrev hiT(t:ℝ) := (slit t)^3
private lemma slit_p{t:ℝ}(p:0<t): 0<slit t:=by unfold slit; positivity
private lemma slit_v{t:ℝ}(p:0≤t): slit t^4=t:=by unfold slit; rw [show 4=2*2 by norm_num,pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt p]
private lemma slit_m {a b:ℝ}(p:a≤b):slit a ≤ slit b:= Real.sqrt_le_sqrt (Real.sqrt_le_sqrt p)
private lemma slit_q{a:ℝ}(p:0≤a)(b:ℝ): hiT (a*b)=hiT a*hiT b:=by unfold hiT slit; rw [Real.sqrt_mul p,Real.sqrt_mul (Real.sqrt_nonneg _),mul_pow]
private lemma slit_c (n:ℕ) : ∑ i∈ range n, (hiT (tauL n i))⁻¹ ≤ 4*n:=by
 rcases Nat.eq_zero_or_pos n with g|g; · subst n; simp
 have he(m:ℕ): ∑ i∈range m, (hiT ((i:ℝ)+1))⁻¹ ≤ 4*slit m:=by
    induction m with
    | zero=>simp only [range_zero,sum_empty,Nat.cast_zero]; simp [slit]
    | succ m ih=>
      let A:=slit ((m:ℝ)+1); let B:= slit m
      have ht:0<A:=slit_p (by positivity); have hb:0≤ B:=Real.sqrt_nonneg _
      have hx:B≤ A:=slit_m (by linarith)
      have hv:A^4-B^4=1:=by unfold A B; rw [slit_v (by positivity),slit_v (by positivity)]; ring
      rw [sum_range_succ]; apply (add_le_add_left ih _).trans; push_cast
      change 4*B+(A^3)⁻¹≤4*A; apply add_le_of_le_sub_left; apply (inv_le_iff_one_le_mul₀ (pow_pos ht _)).mpr
      let D:= B^3+A*B^2+A^2*B+A^3; have he1:D≤4*A^3:=by
         have t:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hx 2) ht.le; have h:=mul_le_mul_of_nonneg_left hx (sq_nonneg A); have q:=pow_le_pow_left₀ hb hx 3; unfold D; linarith only [t,h,q] -- t A*A^2 etc normalizer
      have hm:(A-B)*D=A^4-B^4:=by unfold D; ring
      rw [←hv, ←hm]; exact (mul_le_mul_of_nonneg_left he1 (sub_nonneg.mpr hx)).trans_eq (by ring)
 let V:ℝ:=n; have hx:0<V:= Nat.cast_pos.mpr g
 have hd(i:ℕ): hiT (tauL n i)= hiT ((i:ℝ)+1)*(hiT n)⁻¹:= by unfold tauL hiT slit; rw [Real.sqrt_div (by positivity),Real.sqrt_div (by positivity),div_pow,div_eq_mul_inv]
 simp_rw [hd,mul_inv, inv_inv,←sum_mul]; apply (mul_le_mul_of_nonneg_right (he n) (pow_nonneg (slit_p hx).le _)).trans_eq; unfold V; rw [mul_assoc, ←pow_succ',show slit (n:ℝ)^(3+1)=_ from slit_v hx.le]
private lemma slit_r (N:Side) : ∑ i∈ range N.val,(hiT (tauR N.val i))⁻¹ ≤ 4*N.val:=by
 rw [←sum_range_reflect _]; refine le_trans (le_of_eq (b:=∑ i∈range N.val,(hiT (tauL N.val i))⁻¹) ?_) (slit_c _)
 apply sum_congr rfl; intro i h; congr 2; have he:i ≤ N.val-1:=by have hx:=mem_range.mp h; omega
 unfold tauL tauR; rw [Nat.cast_sub he,Nat.cast_sub (show 1 ≤ N.val from N.property),Nat.cast_one]; ring -- tune
private def fare (x: Per N):ℝ:= tauL N.val x.val*tauR N.val x.val
private lemma fare_p(x:Per N): 0 < fare x:= mul_pos (interval_left _).1 (interval_right _).1
private lemma siteSum (N:Side) : ∑ i: Per N,(hiT (fare i))⁻¹≤ (64:ℝ)*N.val:=by
 let a(i:Per N):=tauL N.val i.val; let b(i:Per N):=tauR N.val i.val
 have hx(t:ℝ)(p:1/2≤t): (hiT t)⁻¹≤8:=by
    have hp:0<t:=by linarith
    have hh:=slit_p hp; have hv: (1/2:ℝ)≤ slit t:=by apply (pow_le_pow_iff_left₀ (by norm_num) hh.le (by omega: (4:ℕ)≠0)).1; rw [slit_v hp.le]; linarith -- tuner
    apply (inv_le_iff_one_le_mul₀ (pow_pos hh 3)).mpr; nlinarith only [pow_le_pow_left₀ (by norm_num) hv 3]
 have ht(i:Per N): (hiT (fare i))⁻¹≤ 8*((hiT (a i))⁻¹+(hiT (b i))⁻¹):=by
    have he:0<a i:=(interval_left _).1; have hp:0<b i:=(interval_right _).1
    have h:0≤(hiT (a i))⁻¹:=by unfold hiT slit; positivity
    have g:0≤(hiT (b i))⁻¹:=by unfold hiT slit; positivity
    rw [fare,slit_q he.le,mul_inv]; obtain z|z:=le_total (1/2:ℝ) (a i); · apply (mul_le_mul_of_nonneg_right (hx (a i) z) g).trans; linarith
    have hv:1/2≤b i:=by
      have hx:1≤a i+b i:=by unfold a b tauL tauR; rw [← add_div,le_div_iff₀ (show 0<(N.val:ℝ) by exact_mod_cast N.property)]; linarith
      linarith
    apply (mul_le_mul_of_nonneg_left (hx (b i) hv) h).trans; linarith
 apply (sum_le_sum (fun i _=>ht i)).trans; rw [←mul_sum,sum_add_distrib,period_sum N (fun x=> (hiT (tauL N.val x))⁻¹),period_sum N (fun x=> (hiT (tauR N.val x))⁻¹)]; linarith only [slit_c N.val,slit_r N]
abbrev zTar (j:ℕ)(M:Tulip.Male)(x:Site N):=‖shell j M.val (mel x)‖
lemma amp (j:ℕ)(h:1≤j)(M:Tulip.Male)(x:Site N):0 < zTar j M x:=by
 obtain ⟨c,p,u⟩:= glens j h; exact (mul_pos p (pow_pos (norm_pos_iff.mpr (pm_nonzero x)) _)).trans_le (u M N x)
-- exponent 3/2
abbrev hard (z:ℝ):= (Real.sqrt z)^3
lemma bills (j:ℕ)(h:1≤j): ∃ C:ℝ,0<C∧∀ N:Side,∀ M:Tulip.Male,∑ i:Site N,(hard (zTar j M i))⁻¹ ≤ C*(N.val:ℝ)^4:=by
 obtain ⟨c,t,u⟩:= glens j h; let V:=(hard c)⁻¹; have hp':0<V:=by unfold V hard; positivity
 refine ⟨V*64^4,by positivity,fun N M=>?_⟩
 let z:= zTar (N:=N) j M
 have he(i:Site N)(d:Axis): c * fare (i d)^2 ≤ z i := le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fare_p _).le ((mode_lower (i d)).trans (norm_le_pi_norm (pm i) d)) _) t.le) (u _ _ _)
 let f(x: Per N):= hiT (fare x); have fp(x):0<f x:=pow_pos (slit_p (fare_p _)) _
 let q(i:Site N):= ∏ d:Axis,(f (i d))⁻¹
 have ht(i:Site N): (hard (z i))⁻¹≤ V*q i:=by
    let s:=z i/c; have hg:=amp j h M i; have hx:0<s:=div_pos hg t
    have hp(d:Axis): fare (i d) ≤ Real.sqrt s:=by
       have hq: fare (i d)^2 ≤ s:= (le_div_iff₀ t).mpr (by rw [mul_comm]; exact he i d)
       exact (Real.le_sqrt_of_sq_le hq) -- name
    have hy:q i ≥ ∏ d:Axis,(hiT (Real.sqrt s))⁻¹:= prod_le_prod (fun _ _=> by unfold hiT slit; positivity) (fun d _=> inv_anti₀ (fp _) (pow_le_pow_left₀ (slit_p (fare_p _)).le (slit_m (hp d)) _))
    rw [prod_const,card_univ,Fintype.card_fin, inv_pow] at hy -- inv_pow direction; tune
    apply le_trans _ (mul_le_mul_of_nonneg_left hy hp'.le); apply le_of_eq; unfold V; rw [←mul_inv]; congr 1; unfold hiT hard; rw [←pow_mul,pow_mul' _ _ _,slit_v (Real.sqrt_nonneg _), ←mul_pow]; apply congrArg (fun x:ℝ=> x^3); rw [←Real.sqrt_mul t.le,_root_.mul_comm]; unfold s; rw [div_mul_cancel₀ _ t.ne']
 apply (sum_le_sum (g:=fun x=>V*q x) (fun i _=> ht i)).trans; rw [←mul_sum]; apply le_trans (mul_le_mul_of_nonneg_left _ hp'.le) (le_of_eq (mul_assoc ..).symm)
 unfold q; rw [← Fintype.prod_sum (fun (i:Axis) (j:Per N)=> (f j)⁻¹),prod_const,card_univ,Fintype.card_fin]; exact (pow_le_pow_left₀ (sum_nonneg (fun i _=> (inv_pos.mpr (fp i)).le)) (siteSum N) _).trans_eq (mul_pow ..)
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.bills
