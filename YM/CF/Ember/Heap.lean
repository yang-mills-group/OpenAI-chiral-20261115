import YM.CF.Ember.Drab
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Lat Lattice Metric MeasureTheory Finset Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
private lemma cooler {a b C:ℝ}(ha:0<a)(h:a/2≤b)(hc:0≤C)(n:ℕ): C/b^n ≤ C*2^n/a^n:=
 (div_le_div_of_nonneg_left hc (pow_pos (by linarith : 0<a/2) n) (pow_le_pow_left₀ (by linarith) h _)).trans_eq (by rw [div_pow]; field_simp)
structure MapH {N:Side}(F:Gaia→ℝ)(A B e:ℝ)(f:Site N→ℝ):Prop where
 core(k:Site N)(h:‖bark k‖≤ 10*A*pinch N): ‖f k‖≤B/pinch N^4
 scale(k:Site N)(h:A*pinch N≤‖bark k‖): ‖f k-F (bark k)‖≤ e*( (‖bark k‖^3)⁻¹ +pinch N/(‖bark k‖^5) )
lemma frosted {F:Gaia→ℝ}{r:ℝ}(S:SnowH F r){A B e:ℝ}(a:1≤ A)(b:0≤ B)(d:0≤ e):∃ D:ℝ,∀ {N:Side},∀ f:Site N→ℝ,Even N.val→8*A*pinch N≤1→ MapH F A B e f→‖(∑ k,f k)/(N.val:ℝ)^4-r*Real.log N.val‖≤ D:=by
 obtain ⟨C,hc,H⟩:=S.chill; let T:=8*A
 have ha : 1≤T:=by unfold T; linarith
 have hy:T-A≥2:=by unfold T; linarith
 let A':=2*C+32*e
 let W:=8*e+A'
 have hA:0≤A':=by unfold A'; positivity
 have hw:0≤W:=by unfold W; positivity
 refine ⟨cartWeight*(B*T^4*(Real.pi^2/2)+ W*volume.real boundsEarth+C*volume.real boundsEarth+W*(2*Real.pi^2))+‖-r*Real.log (T*Real.pi)‖,?_⟩
 intro N f hN hs M
 let l:=pinch N; let μ:=T*l
 let B':=closedBall (0:Gaia) 1; let L:=closedBall (0:Gaia) μ; let Z:=orbShell μ; let Y:=boundsEarth \ B'; let g:= plants f
 have hl:0<l:=pinch_pos N
 change μ≤1 at hs; have he0:l≤μ:=by unfold μ; nlinarith
 have hl0:= hl.trans_le he0
 have hG : B'⊆boundsEarth:=fun x h=>orbs (by simpa [B'] using h)
 have hlb : L⊆ B':= closedBall_subset_closedBall hs
 have hQ:Y⊆boundsEarth:=fun _ h=> h.1
 have hz := fortunate f hN
 have hb1: ‖∫ p in L,g p‖≤B*T^4*(Real.pi^2/2):=by
   have hm : ∀ᵐ p ∂volume.restrict L, ‖g p‖≤ B/l^4 :=by
     filter_upwards [arboretum hN measurableSet_closedBall (hlb.trans hG)] with p ⟨hp,k,hk⟩
     have hx:‖p‖≤μ:= by simpa [L] using hp
     rw [show g p=f k from flora f _ hk]; apply M.core
     have hz:= (norm_sub_norm_le (bark k) p).trans (proximity _ hk); change ‖bark k‖-‖p‖≤ 2*l at hz; change _≤10*A*l; change ‖p‖≤8*A*l at hx; nlinarith
   refine (norm_setIntegral_le_of_norm_le_const_ae ((isCompact_closedBall ..).measure_lt_top) hm).trans_eq ?_; rw [solidGaia hl0.le]; unfold μ; field_simp
 have hY : MeasurableSet Y:= earth_meas.diff measurableSet_closedBall
 let K(p:Gaia):=8*e/(‖p‖^3); let J(p:Gaia):=A'*μ/(‖p‖^5)
 have ht(p:Gaia)(hp:μ≤‖p‖)(k:Site N)(hk:p∈cellH k):‖g p-F p‖≤ K p+J p:=by
   let r:=‖p‖; let x:=bark k
   have hxy:‖x-p‖≤2*l:=proximity _ hk
   have hr:=hl0.trans_le hp
   have hw : ‖x-p‖≤r/2:=by change 8*A*l≤r at hp; nlinarith
   have he:‖p‖-‖x‖ ≤ ‖x-p‖:=by rw [norm_sub_rev]; exact norm_sub_norm_le ..
   have hs:r/2≤‖x‖:=by change r-‖x‖ ≤ _ at he; linarith
   have hg := (H p hr).2 x hw
   have hf := M.scale k (by change _≤‖x‖; change A*l≤ ‖x‖; change T*l≤ r at hp; change r-‖x‖ ≤ _ at he; nlinarith)
   have hy := norm_add_le (f k-F x) (F x-F p)
   change ‖f k-F x‖≤ e*((‖x‖^3)⁻¹+l/‖x‖^5) at hf
   rw [← one_div (‖x‖^3),mul_add,mul_div_assoc',mul_one,mul_div_assoc'] at hf -- tune
   rw [show g p=f k from flora _ _ hk]
   refine (norm_sub_le_norm_sub_add_norm_sub (f k) (F x) (F p)).trans ?_
   refine (add_le_add hf hg).trans ?_
   let R:=‖p‖
   refine (add_le_add (add_le_add (cooler hr hs d _) (cooler hr hs (mul_nonneg d hl.le) _)) (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hc.le) (by positivity : 0≤ R^5))).trans ?_
   change e*2^3/‖p‖^3+e*l*2^5/‖p‖^5+C*(2*l)/‖p‖^5≤ K p + J p
   unfold K J
   ring_nf; unfold A'
   -- check form
   nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he0 hc.le) (show 0≤ ‖p‖⁻¹^5 by positivity),mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he0 d) (show 0≤ ‖p‖⁻¹^5 by positivity)]
 have hb2 : ‖∫ p in Y,g p‖≤ W*volume.real boundsEarth+C*volume.real boundsEarth:=by
   rw [← add_mul]
   have hh: ∀ᵐ p ∂volume.restrict Y, ‖g p‖≤ W+C:=by
      filter_upwards [arboretum hN hY hQ] with p ⟨hp,k,hk⟩
      have hy : 1 ≤ ‖p‖:= le_of_lt (lt_of_not_ge (fun hc=> hp.2 (by simpa [B'] using hc)))
      have hg:=hs.trans hy
      have ho:0<A'*μ∨ 0≤A'*μ:= Or.inr (mul_nonneg hA hl0.le)
      have hR : K p+J p≤ W:= add_le_add (div_le_self (by positivity : 0 ≤ 8*e) (one_le_pow₀ hy)) ((div_le_self (ho.elim le_of_lt id) (one_le_pow₀ hy)).trans (mul_le_of_le_one_right hA hs))
      exact (norm_le_norm_sub_add _ _).trans (add_le_add ((ht p hg k hk).trans hR) ((H p (hl0.trans_le hg)).1.trans (div_le_self hc.le (one_le_pow₀ hy)))) -- tune
   exact (norm_setIntegral_le_of_norm_le_const_ae ((measure_mono hQ).trans_lt (lt_top_iff_ne_top.mpr earth_oaks)) hh).trans (mul_le_mul_of_nonneg_left (measureReal_mono hQ earth_oaks) (by linarith))
 have hh3 : ‖∫ p in Z,g p-F p‖≤ W*(2*Real.pi^2):=by
   have hg(n:ℕ)(a:ℝ):IntegrableOn (fun p:Gaia=>a/‖p‖^n) Z volume:= geoS hl0 _ (show Continuous (fun _ : Gaia=> a) from continuous_const) _
   have hK: IntegrableOn K Z volume:=hg _ _; have hJ :IntegrableOn J Z volume:=hg _ _
   apply (norm_integral_le_of_norm_le (f:=fun p=>g p-F p) (μ:=volume.restrict Z) (g:=fun p=> K p+J p) (hK.add hJ) ?_).trans
   swap
   · filter_upwards [arboretum hN shell_meas (show Z ⊆ boundsEarth from fun _ h=> shell_on h)] with p ⟨hp,k,hk⟩; exact ht p hp.1.le _ hk
   rw [integral_add hK hJ]; unfold K J; simp_rw [div_eq_mul_inv,integral_const_mul]; rw [show Z=_ from rfl,(peel_p μ hl0 hs).1,peelH hl0 hs]; unfold W; rw [add_mul (8*e) A' (2*Real.pi^2)]; apply add_le_add
   · exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) (by linarith)) (by positivity)
   have hh : A'*μ*(2*Real.pi^2*(μ⁻¹-1))=A'*(2*Real.pi^2)*(1-μ):=by field_simp
   rw [hh]; exact mul_le_of_le_one_right (by positivity) (by linarith)
 have hF:=S.fare hl0 hs
 have hde : boundsEarth=(L∪Z) ∪ Y:=by rw [show Z=B'\L from shell_def,Set.union_sdiff_cancel hlb]; exact (Set.union_sdiff_cancel hG).symm
 have hs0 : (∫ p in boundsEarth,g p)=(∫ p in L,g p)+(∫ p in Z,g p)+(∫ p in Y,g p):=by
    conv_lhs=> rw [hde]
    have hx:L∪Z=B':=by rw [show Z=B'\L from shell_def,Set.union_sdiff_cancel hlb]
    rw [setIntegral_union (s:=L∪Z) (t:=Y) ?_ hY ?_ (hz.mono_set hQ),setIntegral_union (s:=L) ?_ shell_meas (hz.mono_set (hlb.trans hG)) (hz.mono_set (fun _ he=>shell_on he))]
    · rw [shell_def]; exact Set.disjoint_sdiff_right
    · rw [hx]; exact Set.disjoint_sdiff_right
    rw [hx]; exact hz.mono_set hG
 have hI: (∫ p in Z,g p-F p)= (∫ p in Z,g p)-(∫ p in Z,F p):=integral_sub (hz.mono_set (fun _ he=> shell_on he)) (S.pay hl0)
 have hpI : μ⁻¹=(N.val:ℝ)/(T*Real.pi):=by unfold μ l pinch; ring_nf; rw [inv_inv]; ring
 have hE : (∑ k,f k)/(N.val:ℝ)^4-r*Real.log N.val=cartWeight*((∫ p in L,g p)+(∫ p in Y,g p)+(∫ p in Z,g p-F p))+ -r*Real.log (T*Real.pi):=by
    rw [hpI,Real.log_div (nPos N).ne' (mul_ne_zero (by linarith) Real.pi_pos.ne')] at hF
    change cartWeight*(∫ p in Z,F p)=_ at hF
    rw [fullF _ hN,hs0,hI]; linarith
 rw [hE]
 refine (norm_add_le ..).trans (add_le_add_left ?_ _); rw [norm_mul,Real.norm_of_nonneg cart_weight_pos.le]
 refine mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans ((add_le_add hb1 hb2).trans_eq (by ring))) hh3)) cart_weight_pos.le
end YM.CF.Ember
