import YM.SU5.Velvet.LowTide
import YM.SU5.Fineness.Chalice
import YM.CF.Onyx.Pay
import YM.CF.Continuum.GraspPolar
/-! # Fourier measures for absolute pricing. Match this *actual history*, flat probes (singles below unconditional calibration of symbols).
    Uniform inverse-square summability OPEN (shrinking ball). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 140000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Velvet
open Function Filter Metric NormedSpace Lattice Wilson Laurent Finset Lat Ember Jill Rush Cube Fock Peaks
open Fir Next.Free Bloch SU Tulip Dial Spire Flare Kea
open Window (polarWork polarLift polarClad)
open scoped Topology NNReal ENNReal Matrix Matrix.Norms.L2Operator BigOperators MatrixOrder Kronecker ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{N:Side}
-- use actual Pad ability from late rung & i
lemma clear_canvas : tax (N:=N) emptyC=(1:Bkg N) :=by
 funext i
 change waveG skyV=1
 apply Subtype.ext; apply Subtype.ext; change Matrix.diagonal _ = (1:Op SU.F); ext a b; by_cases e:a=b; · subst b; simp [phase_z,skyV]
 simp [e]
def freckles (N:Side)(j:ℕ)(M:Jill.Male)(i:Site N):ℝ:=Jill.disk j M (pm i)
def fretField (N:Side)(j:ℕ)(M:Jill.Male):=field (too N) j M
lemma coasting (u:Pad j N)(M:Jill.Male) : spar j M (1:Bkg (More N))= Dofu N (field (too N) j M):=by unfold spar; rw [←clear_canvas,u.2 emptyC]
lemma mass_valid (i:Site N): Bound Real.pi (pm i):=(pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun x=>abs_le.mpr ⟨(pm_zone i x).1.le,(pm_zone i x).2⟩
lemma falls_down (p:1≤j)(i:Site N)(M:Jill.Male): 0< freckles N j M i:=by obtain ⟨c,d,h0,h,H⟩:=Jill.zip p; apply lt_of_lt_of_le ?_ (H M _ (mass_valid i)).1; have hv:=Jill.pt_p i; positivity
lemma meadow_stats (N:Side)(j:ℕ)(p:1≤j)(M:Jill.Male)(e:Even N.val)(i:Stag N) :
 let P:=field (too N) j M i; let d:= freckles N j M i.1
 IsStarProjection P ∧ P.trace=2 ∧ d≤1 ∧ Aop*P*Aop=d • Aop ∧
 P*Aop*P=d • P ∧ minA*(1-P)*minA=d • minA :=by
 let A:= Aop; intro P d; have hd:0<d:= falls_down p i.1 M; have hg:=crestQ j M (too N) e i; unfold high_d at hg; rw [too_u] at hg -- tune
 have ht:= hg.1; have hs: A*P*A=d • A:=hg.2.2.1
 let x:=Window.polarClad ht hg.2.1 hs hd; refine ⟨ht,hg.2.1.trans ?_,?_,hs,?_,hg.2.2.2⟩
 · exact dateA ..
 · have hh : ‖A‖=1:=Window.projector_norm_fact; have he:= (norm_mul_le (A*P) A); rw [hs,norm_smul,hh,mul_one,mul_one,Real.norm_of_nonneg hd.le] at he; exact he.trans ((norm_mul_le ..).trans (by rw [hh,one_mul]; exact ht.norm_le _))
 have he:=x.left; unfold polarLift at he; simp only [mul_one, Algebra.smul_mul_assoc, ←mul_assoc] at he; change d⁻¹ • (P*Aop*Aop*P) = P at he; rw [mul_assoc P Aop Aop,AOne] at he; nth_rw 3 [←he]; rw [smul_inv_smul₀ hd.ne'] -- left P rw duplicates!
-- density lemma
abbrev binSc (N:Side)(t:ℝ):Finset (Site N):=univ.filter fun i=>‖pm i‖≤t
def invRa (N:Side)(i:Site N):= (‖pm i‖^2)⁻¹
private lemma rinse (N:Side) (i:Site N) : pinch N ≤ ‖pm i‖:=by have h:= tall_p i; unfold Jill.tall at h; simpa using (le_div_iff₀ (pinch_pos _)).mp h
private lemma dyadic (k:ℕ)(t:ℝ)(c:0<t){C:ℝ}(p:0<C) (L:∀ (N:Side)(a:ℝ),pinch N≤a → ( (binSc N a).card:ℝ) ≤ C*(a/pinch N)^4)(N:Side) (h:t < pinch N*2^k): (∑ i∈binSc N t,invRa N i) ≤ 8*C*t^2 / pinch N ^4:=by
 have hp:=pinch_pos N
 induction k generalizing t with
 | zero=> rw [pow_zero,mul_one] at h; rw [show binSc N t=∅ from Finset.eq_empty_iff_forall_notMem.mpr (fun i u=> not_lt_of_ge ((rinse N i).trans (mem_filter.mp u).2) h),sum_empty]; positivity
 | succ k ih=>
   by_cases e:t<pinch N; · rw [show binSc N t=∅ from Finset.eq_empty_iff_forall_notMem.mpr (fun i u=> not_lt_of_ge ((rinse N i).trans (mem_filter.mp u).2) e),sum_empty]; positivity
   let a:=t/2; have ha:0<a:= half_pos c; have hz:a≤t:=half_le_self c.le; let T:=binSc N t; let S:= binSc N a; have hT:S⊆T:=fun i p=> mem_filter.mpr ⟨mem_univ _,le_trans (mem_filter.mp p).2 hz⟩
   let y:=pinch N; have hx:(∑ i∈ T\ S,invRa N i) ≤ 4*C*t^2 / y^4:= by
      have hb:= L N t (le_of_not_gt e); calc
       _ ≤ ∑ i∈T \ S,(a^2)⁻¹ := sum_le_sum (fun i u=> inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le (le_of_not_ge (fun v=> (mem_sdiff.mp u).2 (mem_filter.mpr ⟨mem_univ _,v⟩))) 2))
       _ ≤ (T.card:ℝ)*(a^2)⁻¹ :=by rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (show T\S ⊆ T from sdiff_subset))) (by positivity)
       _ ≤ _:= (mul_le_mul_of_nonneg_right hb (show 0≤ (a^2)⁻¹ by positivity)).trans_eq (by unfold y a; field_simp; ring)
   change (∑ i∈ T,_) ≤ _; rw [←sum_sdiff hT]; apply (add_le_add hx (ih a ha (by unfold a; rw [pow_succ', ←mul_assoc y] at h; linarith only [h]))).trans; unfold a y; field_simp; nlinarith only [show 0≤C*t^2 by positivity]
lemma moor_recip : ∃ C:ℝ,0<C ∧ ∀ (N:Side)(a:ℝ),0<a→ (∑ i∈binSc N a,invRa N i) ≤ C*a^2*(N.val:ℝ)^4:=by
 obtain ⟨C,p,W⟩:=Onyx.moor_q; refine ⟨8*C/Real.pi^4,by positivity,fun N a t=>?_⟩; obtain ⟨k,p'⟩: ∃ k:ℕ,a< pinch N * 2^k := ((Filter.Tendsto.const_mul_atTop (pinch_pos N) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))).eventually (eventually_gt_atTop a)).exists -- tune
 apply (dyadic k a t p (fun N b q=> W N _ (zeroF _) b q (fun i hi=>by simp only [Onyx.glen,zeroF,add_zero]; exact (mem_filter.mp hi).2)) N p').trans_eq
 unfold pinch; field_simp
lemma fret_budget (p:1≤j):∃ C:ℝ,0<C ∧ ∀ (N:Side)(a:ℝ)(M:Jill.Male),0<a→ (∑ i∈binSc N a,(freckles N j M i)⁻¹) ≤ C*a^2*(N.val:ℝ)^4:=by
 obtain ⟨D,v,Q⟩:= moor_recip; obtain ⟨c,d,t,u,H⟩:= Jill.zip p; refine ⟨c⁻¹*D,by positivity,fun N a M h=>?_⟩
 apply le_trans (b:=∑ i∈binSc N a,c⁻¹*invRa N i) (sum_le_sum (fun i _=>?_)); swap; · have hv:= Jill.pt_p i; exact (inv_anti₀ (show 0< c*‖pm i‖^2 by positivity) (H M _ (mass_valid i)).1).trans (Eq.le (by unfold invRa; rw [mul_inv])) -- tune mul_inv comm
 rw [←mul_sum]; apply le_trans (mul_le_mul_of_nonneg_left (Q N a h) (by positivity)); exact Eq.le (by ring)
-- spin determinants
/-- mass after hinge -/
def coin (d z:ℝ):= d+ z^4*(1-d)
lemma coin_p {d z:ℝ}(p:0<d)(q:d≤1):0<coin d z:=add_pos_of_pos_of_nonneg p (mul_nonneg (by positivity) (by linarith only [q]))
lemma coin_gap {P:Op SpinIdx}{d:ℝ}(h:IsStarProjection P)(p:P*Aop*P=d • P)(z:ℝ): hinge P Aop z=coin d z • P+(1-P):=by
 rw [hinge_price h A_id,mul_sub,mul_one,sub_mul,h.isIdempotentElem.eq,p]; unfold coin; module
lemma coin_fee {P:Op SpinIdx}{d:ℝ}(h:IsStarProjection P)(p:P*Aop*P=d • P)(z:ℝ)(t:P.trace=2): Matrix.det (hinge P Aop z)=(coin d z:ℂ)^2:=by
 obtain ⟨k,v,w⟩:=cut_pitch h h.isIdempotentElem.eq h.isIdempotentElem.eq z
 rw [t] at v; have hk:k=2:=by exact_mod_cast v.symm
 rw [coin_gap h p,w,hk]; rw [show P+(1-P)=1 from (by abel),Matrix.det_one,mul_one] -- tune
lemma hinge_spectrum (g:Pad j N)(M:Jill.Male)(z:ℝ): let P:=spar j M (1:Bkg (More N)); let Q:= (fun i:Stag N=> hinge (field (too N) j M i) Aop z)
 hinge P (tickA N) z= Dofu N Q :=by
 intro P Q; unfold P; rw [coasting g,landP]; unfold Q hinge gate; let A:= field (too N) j M; let Z:=fun _:Stag N=>Aop; let T:=Dofu N; let H:=Z+ z^2 • (1-Z)
 have he: T (A*(H*H)*A+(1-A))= hinge (T A) (T Z) z:=by unfold T H hinge gate; simp only [map_add,map_sub,map_mul,map_one,map_smul]
 exact he.symm
lemma flat_determinant (p:1≤j)(g:Pad j N)(M:Jill.Male)(z:ℝ):
 let P:= spar j M (1:Bkg (More N)); trade P (tickA N) z = ∑ i:Stag N, Real.log (coin (freckles N j M i.1) z):=by
 let d(i:Stag N):= freckles N j M i.1; intro P
 let X(i:Stag N):=((coin (d i) z:ℝ):ℂ); have h(i:Stag N):0<coin (d i) z:=coin_p (falls_down p i.1 M) (meadow_stats N j p M g.1 i).2.2.1
 have hg :Matrix.det (hinge P (tickA N) z)= ∏ i: Stag N,X i^2 :=by rw [hinge_spectrum g]; change Matrix.det (twist _ (arch _))=_; rw [det_d,det_a]; exact prod_congr rfl fun i _=>by let u:=meadow_stats N j p M g.1 i; exact coin_fee u.1 u.2.2.2.2.1 z u.2.1 -- cast?
 have ht: (tickA N).trace=P.trace:=by unfold P; rw [coasting g]; exact meanV ..
 have hu(i:Stag N):‖X i^2‖ = coin (d i) z ^2 :=by unfold X; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (h i).le]
 unfold trade; rw [hg,norm_prod,Matrix.trace_sub,ht,sub_self,Complex.zero_re,zero_mul,zero_add]; simp_rw [hu]; rw [Real.log_prod (fun i _=> pow_ne_zero 2 (h i).ne'),sum_div]; simp only [Real.log_pow,Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] -- syntactic target
 rfl
lemma anchor_comparison (p:1≤j)(g:Pad j N)(M:Jill.Male) : Cascade.angleFin M N j =∑ i:Stag N, Real.log (freckles N j M i.1) :=by
 let P:= spar j M (1:Bkg (More N)); have hE:P=Dofu N (field (too N) j M):=coasting g M; have h:IsStarProjection P:= hE ▸ idol _ _ _ g.1
 obtain ⟨v,hv⟩ :∃ v,Sea P v:=by
    obtain ⟨U,s,w⟩:=spot_projection P h; refine ⟨Fock.wedge U.val s,?_,wedge_norm ..⟩; rw [w,act_twistLine,inner_self_eq_norm_sq_to_K,wedge_norm]; simp
 rw [show Cascade.angleFin M N j=Real.log ‖inner ℂ (mateK _) v‖ from (Eq.symm (by simpa only [add_zero, skyGlow,quant_one,act_one] using Thera.orb_snap P (tickA N) 0 v hv (mateK _) (tickB _) h (cut_t _) (Eq.trans (meanV (too N) j M) (congrArg Matrix.trace hE.symm)))),apex (too N) g.1 _ M v (hE ▸ hv)]; simp_rw [too_u]; exact Real.log_prod (fun i _=> show disk _ _ _≠0 from (falls_down p i.1 M).ne')
lemma flat_earn (p:1≤j) : ∃ C:ℝ, 0<C ∧ ∀ (N:Side)(g:Pad j N)(M:Jill.Male)(z:ℝ), trade (spar j M (1:Bkg (More N))) (tickA N) z ≤ Cascade.angleFin M N j + C*z^4*(N.val:ℝ)^4 :=by
 obtain ⟨c,t,Hc⟩:= fret_budget p; refine ⟨45*c*Real.pi^2,by positivity,fun N g M z=>?_⟩
 let d:= freckles N j M; have hd(i):0<d i:= falls_down p i M
 let X(i):= (d i)⁻¹; let Y:=∑ i:Site N,X i; have hY: Y ≤ c*Real.pi^2*(N.val:ℝ)^4:=by simpa only [show binSc N Real.pi=univ from (Finset.ext fun i=> by rw [binSc,mem_filter]; exact ⟨And.left, fun u=>⟨u,mass_valid i⟩⟩)] using Hc N Real.pi M Real.pi_pos
 have hp: ∑ i:Stag N,z^4* X i.1= z^4*(Y*45):=by rw [←mul_sum,Fintype.sum_prod_type]; simp only [sum_const,card_univ,slots,nsmul_eq_mul,Nat.cast_ofNat]; rw [←mul_sum,mul_comm 45];
 rw [anchor_comparison p g,flat_determinant p g]; apply le_trans (b:=∑ i:Stag N,(Real.log (d i.1) + z^4*X i.1)) (sum_le_sum fun i _=>?_); swap
 · let y:=d i.1; have ht:0<y:= hd i.1; have h:= (meadow_stats N j p M g.1 i).2.2.1; have hh:0<coin y z:= coin_p ht h; rw [←sub_le_iff_le_add',←Real.log_div hh.ne' ht.ne']; refine (Real.log_le_sub_one_of_pos (div_pos hh ht)).trans ?_; change _ ≤ z^4*y⁻¹; unfold coin; rw [add_div,div_self ht.ne',div_eq_mul_inv]; nlinarith [show 0≤ z^4 by positivity,show y*y⁻¹=1 from mul_inv_cancel₀ ht.ne'] -- need
 rw [sum_add_distrib,hp]; refine add_le_add_right (le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hY (show (0:ℝ)≤45 by norm_num)) (show 0≤z^4 by positivity)) (Eq.le ?_)) _; ring -- tune
end YM.CF.Velvet
#print axioms YM.CF.Velvet.meadow_stats
#print axioms YM.CF.Velvet.flat_earn
