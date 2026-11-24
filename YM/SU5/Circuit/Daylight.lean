import YM.SU5.Circuit.Borealis
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06 MeasureTheory
open YM.Stationary (Gaia cartWeight)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Classical -- indicator
variable {N: Side}{M:Bed}{η σ C R D:ℝ}{q:Clip}
def april (R:ℝ)(A:Site N→ℂ)(x:Gaia):=∑ i:Site N, (pie R i).indicator (fun _=> A i) x
variable {x:Gaia}{k:Site N}
private lemma shoutX (h:x∈ pie R k)(F:Site N→ℂ): april R F x=F k:=by
 rw [april,sum_eq_single k]; · rw [Set.indicator_of_mem h]
 · intro i l v; rw [Set.indicator_of_notMem (show x∉pie R i from fun g=>Set.disjoint_left.mp (Ember.clears v) g h|>False.elim)] -- tune
 simp
private lemma voidX (h:∀ k:Site N,x∉pie R k)(F:Site N→ℂ): april R F x=0:=sum_eq_zero fun i _=>Set.indicator_of_notMem (h _) _
private lemma polarX (F:Site N→ℂ)(p:0<R): (∫ x:Gaia,april R F x)= (R*2*pinch N)^4 • (∑ i,F i):=by
 unfold april; rw [integral_finsetSum, Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [integral_indicator (pies _ _),setIntegral_const,Measure.real,pea p i,ENNReal.toReal_ofReal (by have he:=pinch_pos N; positivity)]
 intro i _; apply (integrable_indicator_iff (pies _ _)).2 (integrableOn_const ?_); rw [pea p i]; finiteness
private lemma april_a (A:Site N→ℂ)(R:ℝ): AEStronglyMeasurable (april R A) volume:=by let F(i:Site N):=(pie R i).indicator (fun _=>A i); rw [show april R A=∑ i,F i by ext1 i; exact (Finset.sum_apply _ _ _).symm]; exact Finset.aestronglyMeasurable_sum (Finset.univ:Finset (Site N)) (fun i _=>(show AEStronglyMeasurable (fun _:Gaia => A i) volume from aestronglyMeasurable_const).indicator (pies R i))

abbrev plaid (M:Bed)(R D:ℝ)(a b:TypeFace 2)(N:Side)(x:Cover)(k:Site N) :ℂ := charK (rubyOff N) k x* mist M R D a b k
lemma polarSong (M:Bed)(a b:TypeFace 2)(N:Side)(x:Cover)(D:ℝ)(h:0<R): chant M R D a b x N=(cartWeight:ℂ)*(∫ s, april R (plaid M R D a b N x) s):=by
 rw [polarX _ h]; change _*songOf _ x= (cartWeight:ℂ)*(_ • songOf (mist M R D a b (N:=N)) x)
 rw [Complex.real_smul,←mul_assoc]; congr 1; unfold pinch Stationary.cartWeight stageVolume; push_cast; have hp: (Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_ne_zero
 have hs:= side_ne N; field_simp
lemma dressCode(q:Clip)(η:ℝ)(U:0<σ)(V:0<C)(a b:TypeFace 2):∃ B:ℝ,0<B∧∀ {N:Side}{M:Bed},M.covered σ C→ Floor M q N η C → Even N.val → ∀ k:Site N, ‖Cov M (rubyM k) a b‖ ≤ B:=by
 obtain ⟨c,B,p,d,H⟩:= costume (Q:=q) (η:=η) U V 0 a b; refine ⟨B,d,fun {N} {M} W S e k=>?_⟩; by_cases hg:ruby k=0; · rw [routine hg,apex_zero]; simpa using d.le
 let i:Topaz q σ η C:=⟨_,_,S,W,e,k,norm_pos_iff.mpr hg,1,one_pos⟩; have ht:= (H i 0 (by simpa)).2; simp only [Topaz.hop,raf,mul_zero,spark,zero_smul,add_zero,zpow_zero,mul_one] at ht; exact ht
lemma dollars (p:0<R)(d:0<D)(V:R*pinch N≤1)(i:Site N)(U:Even N.val): let z:= ruby i; let y:= meter.low/D/4; ∀ x∈pie R i,‖Complex.exp (-(soft R D:ℂ)*divisor 1 (rubyM i))‖ ≤ Real.exp (8^2*y^2)* tog (y^2) x:=by -- near split ‖x‖ ≤4+2Ru; if ≥8 then ‖x‖≤4Ru.
 intro z y x e; have h:= Onyx.bend p e (rubyOff N); let A:= (divisor 1 (rubyM i)).re; have he:0 < meter.low:= meter.low_pos; have hy:0<y:=by unfold y; positivity
 have hX: meter.low^2*‖z‖^2 ≤ A:=by refine le_trans (mul_le_mul_of_nonneg_left (abut z) (by positivity)) (divisor_real_bounds 1 (ruby_spin i U)).1
 have hz:0≤ A:= (mul_nonneg (sq_nonneg _) (sq_nonneg _)).trans hX
 have hp':‖x‖≤4+2*R*‖z‖:=by change ‖x‖≤ R*(4*pinch N+2*‖z‖) at h; linarith
 rw [Complex.norm_exp, tog,← Real.exp_add]; apply Real.exp_le_exp.mpr; simp only [Complex.mul_re, Complex.neg_re,Complex.neg_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,neg_zero,sub_zero]; change -(soft R D)*A ≤ _; by_cases hk : ‖x‖ ≤ 8
 · nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hk 2, mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hk 2) (sq_nonneg y), mul_nonneg hz (show 0 ≤ soft R D by unfold soft; positivity)]
 push Not at hk; have hh:‖x‖≤4*R*‖z‖:=by linarith only [hk,hp']
 have hB: y^2*‖x‖^2 ≤ soft R D*A:= calc _ ≤ y^2*(4*R*‖z‖)^2 := by gcongr
                                           _ = soft R D*(meter.low^2*‖z‖^2):= by unfold y soft; ring
                                           _ ≤ _:= mul_le_mul_of_nonneg_left hX (show 0 ≤ soft R D by unfold soft; positivity)
 nlinarith only [hB,sq_nonneg y]
lemma day(q:Clip)(η:ℝ) (u:0<σ)(v:0<C)(p:0<D)(a b:TypeFace 2):∃ f:Gaia→ℝ, Integrable f∧ ∀ {N: Side}{M:Bed}{R:ℝ},0<R→ R*pinch N≤1→ Even N.val→M.covered σ C→Floor M q N η C→ ∀ x:Cover,∀ y: Gaia, ‖april R (plaid M R D a b N x) y‖≤ f y:=by
 obtain ⟨c,hc,C⟩:=dressCode q η u v a b; let F:=meter.low/D/4; have hp:0<F:=div_pos (div_pos meter.low_pos p) (by norm_num); let B:=Real.exp (8^2*F^2)
 refine ⟨fun y=> c*B*tog (F^2) y,(pearl (pow_pos hp _)).1.const_mul (c*B),fun {N} {M} {R} h e z m k i s=>?_⟩; by_cases j:∃ i:Site N,s ∈ pie R i; swap; · rw [voidX (not_exists.mp j) _,norm_zero]; unfold tog B; positivity
 obtain ⟨w,hw⟩:=j; rw [shoutX hw]; unfold plaid mist; rw [norm_mul,norm_mul,show ‖charK (rubyOff N) w i‖=1 from mode_real (rubyM w) _ (ruby_pigment w),one_mul]
 exact (mul_le_mul (dollars h p e w z s hw) (C m k z w) (norm_nonneg _) (show 0 ≤ B* tog (F^2) s by unfold tog B; positivity)).trans_eq (by ring)
abbrev inspiration (a b:TypeFace 2) (y:ℝ)(x p:Gaia):ℂ:= burn x p*((tog y p:ℂ)*Boreas p a b)
def hotK(a b:TypeFace 2)(y:ℝ)(x:Gaia):ℂ:=(cartWeight:ℂ)*∫ s:Gaia,inspiration a b y x s
variable {P:ℕ→Side}{Y:ℕ→ℝ}{Z:ℕ→Bed}{k':∀ i,Site (P i)}{z:ℕ→Cover}
variable (T:Yard P Y)(A:∀ i,Floor (Z i) q (P i) η C)(L:∀ i,(Z i).covered σ C)(u:0<σ)(v:0<C){X:Gaia}(H:Tendsto (fun i=>riseX (Y i) (z i)) atTop (𝓝 X))
include T A L u H
lemma crescendo (U:Gaia)(h:U≠0)(d: Tendsto (fun i=> duel (Y i) (rubyOff (P i)) (k' i)) atTop (𝓝 U))(p:0<D)(a b:TypeFace 2) : Tendsto (fun i=> plaid (Z i) (Y i) D a b (P i) (z i) (k' i)) atTop (𝓝 (inspiration a b (D^2)⁻¹ X U)):=by
 have he:= skyman T d A L u h
 have ht := haloV T d
 let B(i):=Complex.exp (-(soft (Y i) D:ℂ)*divisor 1 (rubyM (k' i)))
 have hw(i):-(soft (Y i) D:ℂ)*divisor 1 (rubyM (k' i))=-( (Y i:ℂ)^2* divisor 1 (rubyM (k' i)))*((D^2)⁻¹:ℝ) := by unfold soft; push_cast; ring
 have hp : Complex.exp (-((‖U‖:ℂ)^2)*((D^2)⁻¹:ℝ))=(tog (D^2)⁻¹ U:ℂ):=by unfold tog; rw [Complex.ofReal_exp]; push_cast; ring_nf
 have hg:Tendsto B atTop (𝓝 (tog (D^2)⁻¹ U:ℂ)):=by simp_rw [B, hw,← hp]; exact Complex.continuous_exp.continuousAt.tendsto.comp (ht.neg.mul_const _)
 let F(k:Gaia×Gaia):= burn k.1 k.2
 have hd: Tendsto (fun i=> charK (rubyOff (P i)) (k' i) (z i)) atTop (𝓝 (burn X U)):= (((show Continuous F by unfold F burn; fun_prop).tendsto (X,U)).comp (H.prodMk_nhds d)).congr fun i=> (cartR _ _ (T.pos i) _).symm
 exact hd.mul (hg.mul (he a b))
include v in
lemma daylightK (p:0<D)(a b:TypeFace 2) : Tendsto (fun i=> chant (Z i) (Y i) D a b (z i) (P i)) atTop (𝓝 (hotK a b (D^2)⁻¹ X)) :=by
 obtain ⟨U,f,V⟩:= day q η u v p a b
 simp_rw [show ∀ i, chant (Z i) (Y i) D a b (z i) (P i)= _ from fun i=> polarSong _ _ _ _ _ _ (T.pos i)]; unfold hotK; apply Tendsto.const_mul ; apply tendsto_integral_filter_of_dominated_convergence U (Eventually.of_forall fun _=> april_a ..) _ f; swap
 · filter_upwards [T.water.eventually (gt_mem_nhds one_pos)] with i e; exact ae_of_all _ fun z'=> V (T.pos i) (le_of_lt e) (T.even i) (L i) (A i) _ _
 filter_upwards [T.cells,(show ∀ᵐ x:Gaia,x≠0 by rw [ae_iff]; simp)] with x h w
 let Z'(i:ℕ):Site (P i):= if U:∃ k:Site (P i), x∈ pie (Y i) k then U.choose else 0
 have ht:∀ᶠ i in atTop,x∈pie (Y i) (Z' i):= h.mono fun i d=>by unfold Z'; rw [dif_pos d]; exact d.choose_spec
 exact (crescendo T A L u H x w (T.facing ht _) p a b).congr' (ht.mono fun i e=> (shoutX e _).symm)
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.daylightK
