import YM.CF.Moen.Temps
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Moen.Space
open Function Filter Topology Metric Finset
open scoped Classical BigOperators
variable {E: Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {r:ℝ}
abbrev rangeB(E:Type*)[NormedAddCommGroup E](r:ℝ):= {x:E//‖x‖ ≤ r}
lemma bow(h:0<r)(f:rangeB E r→ rangeB E r)(p:Continuous f):∃ x,f x=x:=by
 let n:=Module.finrank ℝ E; let I:=Fin n; let C:= Option (Option I); let W:E≃L[ℝ] (I→ℝ):=ContinuousLinearEquiv.ofFinrankEq (by simp [I,n]); let a:=‖W.toContinuousLinearMap‖*r+1; have hu:0<a:=by unfold a; positivity
 let t:ℝ:=2*a*(n+1); have hx:0<t:=by unfold t; positivity
 let b(x:rangeB E r)(i:I):=(W x.val i+a)/t; have hk(x:rangeB E r)(i:I):0≤ b x i∧ b x i≤(n+1:ℝ)⁻¹:=by
    have he: ‖W x.val i‖≤ a:= (norm_le_pi_norm (W x.val) i).trans ((W.toContinuousLinearMap.le_opNorm _).trans ((mul_le_mul_of_nonneg_left x.property (norm_nonneg _)).trans (le_add_of_nonneg_right zero_le_one))); rw [Real.norm_eq_abs,abs_le] at he; refine ⟨div_nonneg (by linarith [he.1]) hx.le,(div_le_iff₀ hx).mpr ?_⟩; unfold t; field_simp; nlinarith [he.2] -- tune
 let d(x:rangeB E r):Option I→ℝ:= fun i=>i.elim 0 (b x); have ht(x):∑ i:Option I,d x i ≤1:=by
    rw [Fintype.sum_option]; change 0+∑ i:I,b x i≤1; rw [zero_add]; refine (sum_le_sum fun j _=>(hk x j).2).trans ?_; simp only [I,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; rw [←div_eq_mul_inv,div_le_one (by positivity)]; linarith
 let l(x:rangeB E r):Δ C:=⟨fun i=> i.elim (1-∑ i:Option I,d x i) (fun j=> d x j),fun i=>by cases i with
    |none=> exact sub_nonneg.mpr (ht x)
    |some i=> cases i; exact le_rfl; next i=> exact (hk x i).1,
    by rw [Fintype.sum_option]; change 1-_+_=_; exact sub_add_cancel ..⟩
 have hl:Continuous l:=by
    have hp(i:I):Continuous fun x=> b x i:=by dsimp only [b]; fun_prop
    have hv(i:Option I):Continuous fun x=>d x i:=by cases i; exact continuous_const; exact hp _
    apply Continuous.subtype_mk; apply continuous_pi; intro i; cases i; exact continuous_const.sub (continuous_finsetSum _ (fun j _=> hv j)); exact hv _
 let k(y:Δ C):= W.symm (fun i:I=> y.val (.some (.some i))*t-a); have hy(i): k (l i)=i.val:=by apply W.injective; unfold k; rw [W.apply_symm_apply]; funext j; change (W _ _+a)/t*t-a=_; rw [div_mul_cancel₀ _ (ne_of_gt hx),add_sub_cancel_right]
 let d'(x:E):rangeB E r:=⟨(r / max ‖x‖ r) • x,by rw [norm_smul,Real.norm_of_nonneg (by positivity)]; refine (mul_le_mul_of_nonneg_left (le_max_left ‖x‖ r) (by positivity)).trans_eq (div_mul_cancel₀ _ (ne_of_gt (lt_of_lt_of_le h (le_max_right ..))))⟩; have he(x:rangeB E r):d' (k (l x))=x:=Subtype.ext (by rw [hy]; change (r/_ ) • _=_; rw [max_eq_right x.property,div_self (ne_of_gt h),one_smul])
 obtain ⟨x,w⟩:=spen (l ∘ f ∘ d' ∘ k) (hl.comp (p.comp ((Continuous.subtype_mk (Continuous.smul (continuous_const.div (continuous_norm.max continuous_const) (fun i=>ne_of_gt (h.trans_le (le_max_right ..)))) continuous_id) _).comp (W.symm.continuous.comp (continuous_pi (fun i=>((((continuous_apply _).comp continuous_subtype_val).mul continuous_const).sub continuous_const))))))) (by simp [C]); refine ⟨d' (k x),?_⟩; exact (he _).symm.trans (congrArg (d'∘k) w)
end YM.CF.Moen.Space
