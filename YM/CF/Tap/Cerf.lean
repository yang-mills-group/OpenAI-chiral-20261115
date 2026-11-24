import YM.CF.Tap.Mantel
import YM.CF.Ember.Mount
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
abbrev bout(i:Axis)(t:ℝ):Momentum:=(t:ℂ) • step i
lemma bout_zero (i:Axis):bout i 0=0:=by simp [bout]
lemma bout_h(i:Axis)(t:ℝ)(h:‖t‖≤1):bout i t∈baseCube:=by
 refine ⟨?_,fun j=>?_⟩
 · funext j; change star ((t:ℂ)* _)=_; by_cases h:j=i <;>simp [bout,h]
 by_cases k:j=i; subst j; simp [bout]; exact h.trans (by linarith [Real.pi_gt_three]); simp [bout,k,Real.pi_pos.le]
lemma bout_v(i:Axis):∀ᶠ t in 𝓝 0,bout i t∈baseCube:=by filter_upwards [ball_mem_nhds (0:ℝ) one_pos] with t ht using bout_h i t (mem_ball_zero_iff.mp ht|>.le)
abbrev boot (j:ℕ)(M:Male)(p:Momentum):Pal:= bar j M.val p ⊗ₖ 1
lemma boot_o (j:ℕ)(M:Male):boot j M 0=1-bins Slot:=by simp only [boot,bins, Fir.bar_origin,sub_eq_add_neg,op_kron_neg,Matrix.add_kronecker,Matrix.one_kronecker_one]
def taxi(i:Axis):Op SpinIdx:= (1/2:ℂ) • (grading * Fir.zen (step i))
variable (j:ℕ)(h:1≤j)(M: Male)
def boom(i:Axis): Pal:= taxi i⊗ₖ 1
private lemma boot_t(p:Momentum):bins Slot* boot j M p=fuel Slot j M.val p:=by simp only [bins,boot,fuel,op_kron_mul,mul_one]
lemma boom_A(i:Axis):bins Slot * boom i=petal i⊗ₖ (1:Op Slot):=by
 simp only [boom,bins,taxi,op_kron_mul,one_mul,Matrix.mul_smul, ← mul_assoc, show Aop*grading=Aop from (BZ.atom 0).plusChir, petal]; congr 1
 rw [show Fir.zen (step i)=Complex.I • gammaOp i from by unfold Fir.zen; rw [sum_eq_single i]; simp; intro _ _ h; simp [h]; simp,Matrix.mul_smul]; module
-- bound all j precost
private abbrev Bix:Type:={x:ℝ // x≠0∧‖x‖≤1}
private def tourK :Tax Bix:=⟨fun i=>‖i.val‖,1,fun i=>norm_pos_iff.mpr i.property.1,fun i=>i.property.2⟩
private lemma firmM (i:Axis):Move tourK fun l _=>bout i l.val:=by
 refine Move.left (fun x=> bout_h i _ x.property.2) one_pos fun t=>?_ ; rw [one_mul]; unfold bout; exact (pi_norm_le_iff_of_nonneg ((tourK.pos t).le)).mpr (fun j=>by by_cases k:j=i; rw [k]; simp only [Pi.smul_apply,Lattice.step_apply,ite_true,smul_eq_mul,mul_one,Complex.norm_real]; exact le_rfl; simp [k,(tourK.pos t).le])
include h
private lemma barF (i:Axis):Act tourK 2 fun t _=> bar j M.val (bout i t.val)-bar j M.val 0-(t.val:ℂ) • taxi i:=by
 let W(t:Bix)(z:ℂ):=bout i t.val
 let T:= (firmM i); have ht:= T.glass (fun _=>M.val) (fun _=>M.property) j h
 have hv : Act tourK 2 fun t z=> Fir.zen (skin j M.val (W t z))-(1/2:ℂ) • Fir.zen (W t z):=by
    simp_rw [Fir.zen,Finset.smul_sum,←sum_sub_distrib,smul_smul (1/2:ℂ),← sub_smul]; exact Act.finiteSum univ _ (fun a _=>(T.coldS (fun _=>M.val) (fun _=> M.property) j h a).smul (Act.anchor tourK (Complex.I • gammaOp a)))
 have h':=Act.add (p:=2) (ht.smul (Act.anchor tourK grading)) ((Act.anchor tourK grading).mul hv); convert h' using 1; ext1 t; ext1 z; unfold bar W taxi bout; simp only [Fir.skin_origin,zen_zero, mul_zero,Fir.shell_origin, zenS]; rw [mul_sub,Matrix.mul_smul,Matrix.mul_smul]; module
lemma barox(i:Axis):HasDerivAt (fun s=> boot j M (bout i s)) (boom i) 0:=by
 let F(s:ℝ):= bar j M.val (bout i s); let V(s:ℝ):=(F s-F 0)-s • taxi i
 have hp:HasDerivAt V 0 0:=by
   rw [hasDerivAt_iff_tendsto_slope,tendsto_zero_iff_norm_tendsto_zero]; obtain ⟨a,C,ha,hc,H⟩:=barF j h M i
   let L(t:ℝ):= C*‖t‖
   have hz:L 0=0:=by simp [L]
   have hg:Tendsto L (𝓝 0) (𝓝 (L 0)):= Continuous.tendsto (show Continuous L by unfold L; fun_prop) _
   rw [hz] at hg
   refine squeeze_zero' (g:=L) (Eventually.of_forall (fun t=>norm_nonneg _)) ?_ (hg.mono_left nhdsWithin_le_nhds)
   filter_upwards [self_mem_nhdsWithin,(Eventually.filter_mono (nhdsWithin_le_nhds) (ball_mem_nhds (0:ℝ) one_pos))] with t k ht; let x:Bix:=⟨t,k,(mem_ball_zero_iff.mp ht).le⟩; have hh:=norm_pos_iff.mpr x.property.1
   have he : ‖V t‖≤C*(‖t‖^2):=by
      unfold V F; rw [←Complex.coe_smul,bout_zero]; have hp:= (H x 0 (by simpa)).2; rw [_root_.zpow_ofNat] at hp; exact hp
   rw [slope_def_module, sub_zero,show V 0=0 from (by simp [V]),sub_zero, norm_smul,norm_inv]; refine (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ?_; change 0<‖t‖ at hh; unfold L; field_simp
 let Y(z:ℝ):= z • taxi i+ F 0; have he : HasDerivAt Y (taxi i) 0:=by simpa only [one_smul] using ((((hasDerivAt_id' (0:ℝ)).smul_const (taxi i)).add_const (F 0)))
 have hl : HasDerivAt F (taxi i) 0:=by rw [show F=V+Y by ext1 t; simp only [Pi.add_apply,Y,V]; abel]; exact (hp.add he).congr_deriv (by simp)
 let L: Op SpinIdx →ₗ[ℂ] Pal:={ toFun:=fun A=>A⊗ₖ 1,map_add':=fun _ _=>Matrix.add_kronecker ..,map_smul':=fun _ _=>Matrix.smul_kronecker .. }
 exact (L.restrictScalars ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hl
lemma Ps_b (i:Axis):∀ᶠ z in 𝓝 0, let P:=boot j M (bout i z); P*P=P ∧ star P=P:=by
 filter_upwards [bout_v i] with z hz; obtain ⟨hp,he⟩:=firm_bar j M.val M.property (base_subset_realCube zone_pos hz); exact ⟨(by simp only [boot,op_kron_mul,hp, mul_one]), by rw [boot,op_star_kron,he,star_one]⟩
end YM.CF.Tap
