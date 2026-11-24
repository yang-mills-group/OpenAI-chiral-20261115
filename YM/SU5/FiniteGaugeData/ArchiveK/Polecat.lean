import YM.SU5.FiniteGaugeData.ArchiveK.Zephyr
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open MeasureTheory.Measure
variable (G:E4≃ₗᵢ[ℝ] E4) (p q:Space3) (x:E4) (a:Axis)
local notation "Ω"=> E4 ≃ₗᵢ[ℝ] E4
local notation "X"=> pulseG G
local notation "T"=> sailX G
local notation "P"=> seedX G
local notation "Γ"=> emitX
local notation "S"=> depthG G
local notation "Σ"=> crestG G
abbrev gust (G:Ω) (p:Space3) (x:Cover):ℂ:=mode (pulseG G p) x
lemma gust_R(v:Cover) : gust G p v=rise (pulseG G p) (emitX v):=by unfold rise gust mode; simp [emitX, ofReal_intCast]
lemma gust_z {p:Space3}{v:Cover} : gust G p v≠0:= mode_ne _ _
@[fun_prop] lemma gust_safe(v:Cover): Continuous (fun p=> gust G p v):=by unfold gust mode; have he:=pulse_cont G; fun_prop
lemma emitted(x:Cover): gust G p (-x)= (gust G p x)⁻¹:=mode_opposite _ _
lemma billS : S (sailX G)=1 :=by unfold depthG; rw [real_inner_self_eq_norm_sq,sail_size]; norm_num
lemma GustZ(v:Cover) : star (gust G p v) = ((Real.exp ((-2)*‖p‖*S (Γ v)):ℝ):ℂ) * gust G p (-v):=by
 rw [gust_R,gust_R,iron_q,iron_q, emit_neg]; unfold depthG crestG; let R:= ‖p‖; let a:= inner ℝ (P p) (Γ v); let b:= inner ℝ T (Γ v); change star (coastE a* ↑(Real.exp (-R*b)))= _* (coastE _* _); rw [star_mul,coast_inv]; have hz (v:ℝ): star (v:ℂ)=(v:ℂ):= Complex.conj_ofReal v; simp_rw [hz,inner_neg_right]; rw [mul_comm _ (coastE _*_ )]; change _= (coastE (-a)* ↑(Real.exp (-R*-b))) *↑(Real.exp (-(2:ℝ)*R*b)); rw [mul_assoc, ← ofReal_mul,←Real.exp_add]; ring_nf
variable {G}{D m:ℕ}(K:ZephyrG G D m)
local notation "zₕ"=> runeX K 3
include K
lemma Gust_t : gust G p (runeX K 3)= ((Real.exp (-(D:ℝ)*‖p‖):ℝ):ℂ):=by
 rw [gust_R,iron_q,rune_p, ← sail_basis]; unfold depthG crestG; rw [real_inner_smul_right,real_inner_smul_right,sail_zero,real_inner_self_eq_norm_sq,sail_size]; simp [mul_comm]; -- maybe billS not unfolded; tune
lemma gust3(p:Space3) : leer (pulseG G p)^8≠0:=by
 apply pow_ne_zero; unfold leer; apply Finset.prod_ne_zero_iff.mpr (fun i _=> ?_); by_cases h:p=0; · subst p; change hsinc _ ≠ 0; have hv:= seed_size 0 G; rw [norm_zero,norm_eq_zero] at hv; unfold pulseG; rw [norm_zero,hv]; simp [brushQ,Fir.tmap,hzero]
 let v:=(pulseG G p i)/2; change hsinc v≠0; have hv:0<v.im:=by
    unfold v pulseG; have ht:=norm_pos_iff.mpr h; have he:=K.flat i; unfold brushQ Fir.tmap; have hg:0<T i:=by linarith only [he]
    simp; positivity
 have hh:v≠0:=fun t=> by rw [t,Complex.zero_im] at hv; linarith
 rw [haway _ hh]; apply div_ne_zero _ hh; intro v; obtain ⟨u,r⟩:= Complex.sin_eq_zero_iff.mp v; rw [r] at hv; norm_num at hv
-- inject all for E cap condition short integer tang
lemma Gust_in {r:ℝ} (z:4*r ≤ m) (u:‖p‖ ≤ r)(v:‖q‖ ≤ r)(e:∀ y:Cover, gust G p y=gust G q y): p=q:=by
 have hm:0<(D:ℝ):= Nat.cast_pos.mpr K.unitC; have hp: ‖p‖=‖q‖:=by
    have he:=e zₕ; rw [Gust_t p K,Gust_t q K] at he; have hx:= Real.exp_injective (Complex.ofReal_injective he)
    exact mul_left_cancel₀ (neg_ne_zero.mpr hm.ne') hx
 let w:= P p- P q; have hw : S w=0:=by unfold w depthG; rw [inner_sub_right,← real_inner_comm T,← real_inner_comm T,sail_zero,sail_zero,sub_self]; -- tune
 have hx(i:Cover) : ∃ x:ℤ, inner ℝ w (Γ i)=τ*x:=by
    have he:=e i; rw [gust_R,gust_R,iron_q,iron_q, hp] at he; let f:= Γ i; let hK:coastE (inner ℝ (P p) f) =coastE (inner ℝ (P q) f):= mul_right_cancel₀ (show (((Real.exp (-‖q‖ *S _):ℝ):ℂ))≠0 from by exact_mod_cast (Real.exp_pos _).ne') he; let v:= inner ℝ w f; have h0:coastE (inner ℝ w f)=1:=by unfold w; rw [inner_sub_left,sub_eq_add_neg,coast_add,hK,mul_comm,coast_dual]; -- precedence
    obtain ⟨z,hz⟩:= Complex.exp_eq_one_iff.mp h0; refine ⟨z,?_⟩; have hy:=congr_arg Complex.im hz; simp only [mul_im, Complex.I_im,Complex.I_re,ofReal_re,ofReal_im,intCast_im,intCast_re,mul_re,mul_zero,zero_mul,one_mul,mul_one, zero_add] at hy; -- tune unfolding τ
    unfold τ; norm_num at hy; exact hy.trans (by ring)
 let F(i:Axis) : Cover:= Pi.single i 1; have hE(i:Axis):emitX (F i)= YM.basis i := by apply PiLp.ext; intro j; simp [F,Pi.single_apply,YM.basis_eq,emit_axis] -- tune
 choose x X' using hx; let z':Cover:= fun i=> x (F i); have h0:w=τ • Γ z':=by apply PiLp.ext; intro i; have ht := X' (F i); rw [hE, real_inner_comm,YM.basis_inner] at ht; exact ht
 have he:‖w‖ ≤2*r:= by apply (norm_sub_le ..).trans; rw [seed_size,seed_size]; linarith only [u,v]; -- tune
 rw [h0, norm_smul,Real.norm_of_nonneg tau_pos.le] at he; by_cases Q:z'=0; · rw [Q,emit_origin,smul_zero] at h0; have hh: P p=P q:=sub_eq_zero.mp h0; exact congr_arg Prod.fst ((upright G).injective hh)
 exfalso; apply K.apart z' (by by_contra h; have hu:=hinder m z' h; nlinarith only [show 1<τ from (by unfold τ; linarith [Real.pi_gt_three]), hu, z, he, u,norm_nonneg p, norm_nonneg (emitX z')]) Q; unfold depthG at *; rw [h0,real_inner_smul_right] at hw; exact (mul_eq_zero.mp hw).resolve_left tau_pos.ne' -- tune op
#print axioms Gust_in
end YM.CF.Window.ArchiveK
