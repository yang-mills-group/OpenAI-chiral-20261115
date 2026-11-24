import YM.CF.Onyx.Roll
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{r R C w:ℝ}{M:Male}{a:Axis}
def charK(s:Offset N)(k:Site N)(z:Cover):=mode (tmap (glen s k)) z
-- choice d such that R*extent d ≃ π/v where v ≠0 axis. hence multiplier gap
private def phase_v(x:ℝ):ℂ:=Complex.exp (Complex.I*(x:ℂ))
def drum(d:ℝ):ℂ:= phase_v (d) -∑ i∈range 8,debt i* phase_v (-(i:ℝ)*d)
lemma forth (a:Axis)(d:ℤ)(z:Cover)(k:Site N)(s:Offset N): charK s k z= phase_v (-(extent N d * (z a))) * charK s (k+march N a d) z:=by
 unfold charK; rw [← Kea.wage (march_a d s k a),show tmap (_+_) = tmap (glen s k)+ tmap (beam a (extent N d)) from funext fun i=>Complex.ofReal_add .., mode_phase]
 have he: mode (tmap (beam a (extent N d))) z=phase_v (extent N d*z a):=by unfold mode phase_v; rw [sum_eq_single a]; simp [step,beam,tmap]; intro i _ h; simp [step,beam,tmap,h]; simp -- tune
 rw [he,phase_v,phase_v]; simp only [Complex.ofReal_neg,mul_neg,Complex.exp_neg]; rw [mul_left_comm,mul_comm (_⁻¹),mul_inv_cancel₀ (Complex.exp_ne_zero _),mul_one] -- tune
lemma toll : ∑ i∈range 8,bead 8 (-1) i*(-1:ℝ)^i=255:=by
 let B(i:ℕ):=bead 8 (-1) i; have he(j:ℕ)(h:j<8): ∑ i∈range 8,B i*(i:ℝ)^j=(-1)^j:=bead_p _ _ h _; change ∑ i∈range 8,B i*(-1:ℝ)^i=_
 have h1:=he 0 (by decide); have h2:=he 1 (by decide); have h3:=he 2 (by decide); have h4:=he 3 (by decide); have h5:=he 4 (by decide); have h6:=he 5 (by decide); have h7:=he 6 (by decide); have h8:=he 7 (by decide); clear he
 norm_num [sum_range_succ] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢; linarith -- tune
lemma ore : drum Real.pi=-256:=by
 have hv: phase_v Real.pi=-1:= by rw [phase_v,mul_comm]; exact Complex.exp_pi_mul_I
 have he(i:ℕ):phase_v (-(i:ℝ)*Real.pi)= (((-1:ℝ)^i:ℝ):ℂ):=by
   unfold phase_v; push_cast; rw [show Complex.I*(-(i:ℂ)*(Real.pi:ℂ))= (i:ℂ)*(-((Real.pi:ℂ)*Complex.I)) from (by ring),Complex.exp_nat_mul, Complex.exp_neg,Complex.exp_pi_mul_I]; simp
 unfold drum; simp_rw [he,debt,←Complex.ofReal_mul,←Complex.ofReal_sum]; rw [toll,hv]; norm_num -- tune
-- bound weighted oscill
variable {A:Site N→Peb}{s:Offset N}
def liv (F:Site N→Peb)(s:Offset N)(z:Cover):=∑ k:Site N,charK s k z • F k
lemma setK(F:Site N→Peb)(a:Axis)(s:Offset N)(d:ℤ)(z:Cover):liv (odds F a d) s z=drum (extent N d*z a) • liv F s z:=by
 have ht(n:ℤ): (∑ k:Site N,charK s k z • F (k+march N a n))= phase_v (- (extent N n*z a)) • liv F s z:=by
    calc
      _= ∑ k:Site N,phase_v (-(extent N n*z a)) • (charK s (k+march N a n) z • F (k+march N a n)):=by apply sum_congr rfl; intro i _; rw [smul_smul, ← forth]
      _= _:=by rw [← Finset.smul_sum]; exact congrArg _ (Equiv.sum_comp (Equiv.addRight (march N a n)) (fun i=>charK s i z • F i))
 unfold liv odds drum; rw [sub_smul,sum_smul]; simp_rw [smul_sub, Finset.smul_sum,sum_sub_distrib, mul_smul]; rw [sum_comm (s:=@univ (Site N) _) (t:=range 8)]; congr 1
 · rw [ht]; rw [show -(extent N (-d)*_)= (extent N d*(z a)) by unfold extent; push_cast; ring,liv,Finset.smul_sum]
 refine sum_congr rfl fun i hi=> ?_
 rw [sum_congr rfl (fun k _=>smul_comm _ (debt i) _),← Finset.smul_sum,ht,march_t]; rw [show -(((i:ℤ):ℝ)*extent N d*(z a))= -(i:ℝ)*(extent N d*z a) by push_cast; ring,liv,Finset.smul_sum,Finset.smul_sum]
lemma cymbal (x:ℕ→ℝ)(h:Tendsto x atTop (nhds Real.pi)) : ∀ᶠ i in atTop, 1 ≤ ‖drum (x i)‖ := by
 have hg:Continuous drum:=by unfold drum phase_v; fun_prop
 have ht: 1 < ‖drum Real.pi‖:=by rw [ore]; norm_num
 exact ((hg.continuousAt.tendsto.comp h|>.norm).eventually (lt_mem_nhds ht)).mono fun _ u=> le_of_lt u
lemma rain (H:1≤j)(p:0<r)(t:0<C)(u:1≤w)(a:Axis):∃ V:ℝ,0<V∧∀ {N: Side}{A:Site N→Peb}{M:Male}{s:Offset N}{R y:ℝ}, Even N.val→FormU s j M r C A→0<R→R*pinch N≤1→0<y→8*w/R<zone→∀ d:ℤ,|extent N d| ≤ w/R→∀ z:Cover,1 ≤ ‖drum (extent N d*z a)‖→ ‖liv (flow s j M y A) s z‖ ≤ V/(R^5*pinch N^4):=by
 obtain ⟨B,D,g,v,P⟩:=serene H p u a; obtain ⟨c,h,K⟩:=gleam H p t a _ w g (lt_of_lt_of_le one_pos u); obtain ⟨L,q,S⟩:=dozen; refine ⟨max D c * L,mul_pos (lt_max_of_lt_left v) q,fun {N} {A} {M} {s} {R y} hN f hr hR e l d ht z hb=>?_⟩
 let G:=flow s j M y A; have hp:=pinch_pos N; let W:= max D c; have hw:0<W:=lt_max_of_lt_left v
 apply le_trans (le_mul_of_one_le_left (b:=‖liv G s z‖) (norm_nonneg (liv G s z)) hb); rw [← norm_smul, ←setK]; apply (norm_sum_le (s:=Finset.univ) (f:=fun k=>charK s k z • odds G a d k)).trans; refine (sum_le_sum (g:=fun k=>W/R*(1/(1+R*‖glen s k‖)^7)) ?_).trans ?_
 · intro i _; rw [norm_smul, show ‖charK s i z‖=1 from mode_real _ _ (tmap_physical _),one_mul]; rcases le_total B (R*‖glen s i‖) with h|h
   · exact (P hN f hr hR e l d ht i h).trans (by unfold W; gcongr; exact le_max_left ..)
   exact (K hN f hr hR e d ht i h).trans (by unfold W; gcongr; exact le_max_right ..)
 rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (S N s R hr hR) (by positivity : 0 ≤ W/R)).trans_eq (by unfold W; field_simp)
end YM.CF.Onyx
