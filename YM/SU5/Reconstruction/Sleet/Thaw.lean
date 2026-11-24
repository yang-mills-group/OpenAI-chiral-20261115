import YM.SU5.Reconstruction.Sleet.Spend
/-! # Removing ghosts via the missing lane -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter Metric Function MeasureTheory Spectral Analysis
open scoped Topology ComplexOrder NNReal ENNReal InnerProductSpace Real Classical ComplexConjugate
open Complex CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis OS Semigroup
variable {Γ : AddSubgroup ℝ} (d:Dense (Γ:Set ℝ))
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a)(X:Players Γ H)
  (g:∀ (u:Γ)(t:ℝ≥0),(X.play u).comp (S.E t)=(S.E t).comp (X.play u))
local notation "ℜ"=> Real.toNNReal
variable (f:H)
private lemma funds_thermal (s:ℝ≥0)(x y:H): inner ℂ x (S.E s y)= inner ℂ (S.E s x) y:=by nth_rw 1 [← S.sym]; exact ContinuousLinearMap.adjoint_inner_right ..
-- fixed-time version of voucher gives continuity at zero in b
private lemma icicle (t:Shard Γ){r:Γ} (C:ℝ)(h:Reflex S X f r C): ContinuousAt (radiation S X f (r+t.val+t.val)) 0:=by
 obtain ⟨F,p,u⟩:= Voucher.wear thermal _ C (h t) thermal_pos; let U:= (𝓝 (0:Γ))
 let J(c:Γ):= (((t.val+c):Γ):ℝ); have hJ: J 0= thermal t:=by simp [J,thermal]
 have hT:Tendsto J U (𝓝 (thermal t)):= by rw [← hJ]; unfold U; refine (show Continuous J from ?_).tendsto _; unfold J; fun_prop
 let I(c:Γ):= r+(t.val+c)+t.val; let s:= r+t.val+t.val; have ht:I 0=s:=by simp [I,s]
 let R:= radiation S X f
 have hp: ContinuousAt (fun i:Γ=> R (I i) i) 0:=by
    apply ( (p.1 _ (assigned_ground (thermal_pos t))).continuousAt.comp_of_eq ((show Continuous (fun i:Γ=> ((J i):ℂ)) from by unfold J; fun_prop).continuousAt) ?_ ).congr ?_ -- orientations?
    · rw [hJ]
    filter_upwards [hT.eventually (lt_mem_nhds (thermal_pos t))] with w k; let v:Shard Γ:=⟨t.val+w,k⟩
    show F (J w)= R (I w) w
    rw [show J w= thermal v from rfl,u]; unfold tiltTest; dsimp only [v]; rw [add_comm t.val, add_sub_cancel_right]; unfold I; rw [add_comm t.val]
 have hd:Tendsto (fun i:Γ=> ‖R s i-R (I i) i‖) U (𝓝 0):=by
    let Q(i:Γ):= S.E (Real.toNNReal (I i:ℝ)) f; let y:=S.E (Real.toNNReal (s:ℝ)) f
    have hz:Tendsto Q U (𝓝 y):= by
       unfold y; rw [← ht]
       apply (S.continuousE f).continuousAt.tendsto.comp (((continuous_real_toNNReal.comp continuous_subtype_val).comp (show Continuous I from by unfold I;fun_prop)).continuousAt.tendsto)
    refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (Eventually.of_forall fun i=> ?_) (g:=fun i=> ‖y-Q i‖*‖f‖) (by simpa using ((tendsto_const_nhds (x:=y)).sub hz).norm.mul_const ‖f‖)
    unfold R radiation; rw [funds_thermal S _ f,funds_thermal S _ f,←inner_sub_left]; rw [← X.wins H i f]; exact norm_inner_le_norm ..
 change Tendsto (R s) _ _
 have v:= ((tendsto_zero_iff_norm_tendsto_zero).2 hd).add hp.tendsto
 simp_rw [ht,zero_add,sub_add_cancel] at v; exact v

include g in
private lemma coolsLives (s:Γ)(h:ContinuousAt (radiation S X f s) 0): f∈ X.lives H:= by
 let m:= (ℜ (s:ℝ))/2; have hu:m+m=ℜ (s:ℝ):=by unfold m; simp
 let y:=S.E m f; let P:=X.pi_c
 have p:ContinuousAt (fun i:Γ=>inner ℂ y (X.play i y)) 0:=by
    apply h.congr; apply Eventually.of_forall; intro i; let u:=S.time m m; rw [hu] at u; unfold radiation; rw [u, ContinuousLinearMap.comp_apply, funds_thermal S, show S.E m (X.play i f)= X.play i (S.E m f) from DFunLike.congr_fun (g i m).symm f]
 have hw : inner ℂ y (P y)= inner ℂ y y:= X.retain (innerSL ℂ y) y p
 have q : inner ℂ (P y) (P y)=inner ℂ y y:=by rw [←hw]; unfold P; nth_rw 1 [← X.pi_adj]; rw [ContinuousLinearMap.adjoint_inner_left,X.pi_idem]
 have hk:y∈ X.lives H := ((X.lives H).mem_iff_norm_starProjection y).2 (le_antisymm (Submodule.norm_starProjection_apply_le ..) ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (le_of_eq ?_)))
 · apply Submodule.starProjection_eq_self_iff.mp
   refine (S.whole m).eq_of_inner_right ℂ ?_; intro x; rw [←funds_thermal S,←funds_thermal S,show S.E m ((X.lives H).starProjection f)= P y from DFunLike.congr_fun (X.commutes_c (S.E m) (g · m)) f,X.pi_fixer hk]
 change ‖y‖^2 = ‖P y‖^2; rw [← inner_self_eq_norm_sq (𝕜:=ℂ),←inner_self_eq_norm_sq (𝕜:=ℂ),q]
include g d in
lemma Reflex.lit {r:Γ}{C:ℝ}(h:Reflex S X f r C): f∈ X.lives H:=by
 obtain ⟨q,b⟩:= (thermal_course d).rich 1 (by norm_num); exact coolsLives S X g f _ (icicle S X f (q 0) _ h)
end YM.ConePrice.Storm
