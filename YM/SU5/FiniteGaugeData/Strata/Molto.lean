import YM.SU5.FiniteGaugeData.Strata.Tigresse
/-! # Haar no-one, mixed tensor spectrum -/
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.Strata
open Function Filter Finset MeasureTheory Metric SU Sods Kea Matrix
open scoped Topology ComplexOrder Matrix Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra
local notation "μ"=> SU.group.probHaar
variable {I:Type*}[Fintype I][DecidableEq I]
section
abbrev foldMo(A:Op I)(U:E):= A ⊗ₖ (matter U).val
def Seal(A:Op I)(U:E):ℂ:= (1-foldMo A U).det
lemma Seal.legal(A:Op I):Continuous (Seal A):=by apply Continuous.matrix_det; apply Continuous.sub continuous_const; apply continuous_matrix; rintro ⟨i,j⟩ ⟨u,v⟩; exact continuous_const.mul (matter_cont.matrix_elem j v)
lemma Seal.pool(z a:ℝ):AnalyticAt ℝ (fun x=> pw (x*a)) z:=by unfold pw BZ.phase; simp_rw [Complex.exp_eq_exp_ℂ]; exact (NormedSpace.exp_analytic (𝕂:=ℝ) _).comp (((Complex.ofRealCLM.analyticAt _).comp (analyticAt_id.mul analyticAt_const)).mul analyticAt_const)
private lemma Sealer(z:ℝ) {A B:ℝ→Op I} (h:∀ i j:I,AnalyticAt ℝ (fun x=> A x i j) z)(p:∀ i j:I, AnalyticAt ℝ (fun x=>B x i j) z) (i j:I) : AnalyticAt ℝ (fun x=>(A x*B x) i j) z:=by simp_rw [Matrix.mul_apply]; exact univ.analyticAt_fun_sum fun k _=>(h i k).mul (p k j)
lemma Seal.wire(x:TF)(U W:E)(z:ℝ): ∀ i j:Slot, AnalyticAt ℝ (fun t=> (matter (U*fly x W t)).val i j) z :=by
 have hp(i:Slot)(t:ℝ):freqD (chargeW x t) i=t*freqD x i:=by obtain ⟨j,i|i⟩:=i <;> simp [freqD,chargeW] <;> ring -- rcases fail
 let B(t):=(matter (waveG (chargeW x t))).val; let C:=Op Slot
 have he(i j): AnalyticAt ℝ (fun x=>B x i j) z:=by unfold B; simp_rw [matD,Matrix.diagonal_apply]; by_cases h:i=j; rw [h]; simpa only [ite_true,Function.comp_apply,hp] using Seal.pool z (freqD x j); simp_rw [if_neg h]; exact analyticAt_const
 intro i j; simp_rw [fly,map_mul,show ∀ u v:UNI Slot, (u*v).val=u.val*v.val from fun _ _=>rfl]; exact Sealer z (A:=fun _=>(matter U).val) (fun _ _=>analyticAt_const) (Sealer z (B:=fun _=>(matter W⁻¹).val) (Sealer z (A:=fun _=>(matter W).val) (fun _ _=>analyticAt_const) he) (fun _ _=>analyticAt_const)) i j
lemma Seal.hotel(A:Op I)(x:TF)(W U:E): AnalyticOnNhd ℝ (fun z=>Seal A (U*fly x W z)) Set.univ:=by
 intro z p; unfold Seal foldMo; simp_rw [det_apply]; apply Finset.analyticAt_fun_sum; intro f w; rcases Int.units_eq_one_or f.sign with h|h <;> rw [h]; swap; · simp_rw [Units.smul_def,Units.val_neg,Units.val_one,neg_smul,one_smul]; apply AnalyticAt.neg; apply Finset.analyticAt_fun_prod; intro i hi; exact analyticAt_const.sub (analyticAt_const.mul (Seal.wire x U W z (f i).2 i.2))
 simp_rw [Units.smul_def,Units.val_one,one_smul]; exact univ.analyticAt_fun_prod fun i _=> analyticAt_const.sub (analyticAt_const.mul (Seal.wire x U W z (f i).2 i.2))
-- spectrum-charge avoiding via finite elementary ray.
abbrev rayM:TF:=⟨fun i=>if i=0 then -4 else 1,by change (∑ i : Fin 5, if i=0 then (-4:ℝ) else 1)=0; norm_num [Fin.sum_univ_succ]⟩
lemma noteMo(i:Slot):freqD rayM i≠0:=by
 obtain ⟨_, ⟨⟨i,j⟩,h⟩|i⟩:=i
 · change ite (i=0) (-4:ℝ) 1 + ite (j=0) (-4:ℝ) 1 ≠0; split <;> split <;> norm_num
 change - ite (i=0) (-4:ℝ) 1 ≠0; split <;> norm_num
lemma beat_su(t:ℝ)(i:Slot): freqD (chargeW rayM t) i=t* freqD rayM i:=by
 have p(i:Slot)(x:TF) : freqD (chargeW x t) i=t*freqD x i:=by obtain ⟨j,i|i⟩:=i <;> simp [freqD,chargeW] <;> ring
 exact p i _
lemma Seal.avoid {σ:ℝ}(h:σ≠0)(S:Set ℂ)(p:S.Finite):∀ᵐ t:ℝ, pw (t*σ)∉ S:=by
 haveI:= p.to_subtype; have he(i:S):∃ t:ℝ,pw (t*σ)-i.val≠0:=by
   by_contra! P; have he: i.val=1:=(sub_eq_zero.mp (P 0)|>.symm).trans (by rw [zero_mul, phase_z]); specialize P (Real.pi/σ); rw [div_mul_cancel₀ _ h,pw,BZ.phase, Complex.exp_pi_mul_I,he] at P; norm_num at P
 filter_upwards [(ae_all_iff (p:=fun t:ℝ=> fun i:S=> pw (t*σ)-(i.val)≠0)).mpr (fun i=>singer _ (fun t _=> (Seal.pool ..).sub analyticAt_const) (he i))] with t hx w; exact hx ⟨_,w⟩ (sub_self _)
lemma Seal.free (A:Op I):∃ x,Seal A x≠0:=by
 obtain ⟨t,d⟩:= (eventually_all.mpr (fun i:Slot=> Seal.avoid (neg_ne_zero.mpr (noteMo i)) (spectrum ℂ A) (Matrix.finite_spectrum A))).exists
 let u:=chargeW rayM t; let f:= pw ∘ freqD u; let Y(i:Slot):= (1:Op I) - f i • A
 refine ⟨waveG u,?_⟩; unfold Seal foldMo; rw [matD,show (1:Op (I×Slot))-A ⊗ₖ _=Matrix.blockDiagonal Y from ?_,Matrix.det_blockDiagonal]; swap
 · ext ⟨a,i⟩ ⟨b,j⟩; by_cases h:i=j; · subst j; simp [blockDiagonal_apply,one_apply,Y,mul_comm,f]; -- tune
   simp [blockDiagonal_apply,one_apply,Matrix.diagonal_apply_ne,h]; -- tune
 refine Finset.prod_ne_zero_iff.mpr fun i _=>?_ ; let z:=f i; let ζ:= pw (t*(-freqD rayM i)); have he:z*ζ=1:=by change pw _ * pw _=1; rw [←phase_a,beat_su,mul_neg,add_neg_cancel,phase_z]
 have hX: algebraMap ℂ (Op I) ζ= ζ • (1:Op I):= Algebra.algebraMap_eq_smul_one ζ; have hx:IsUnit (algebraMap ℂ (Op I) ζ-A):=by exact not_not.mp (d i) -- compl compl
 have p:Y i= algebraMap ℂ (Op I) z*(algebraMap ℂ (Op I) ζ-A):=by unfold Y; rw [_root_.mul_sub,←map_mul,he,map_one, ← Algebra.smul_def]; -- tune
 rw [p]; refine ((Matrix.isUnit_iff_isUnit_det _).mp ?_).ne_zero; exact ((isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul (he.trans_ne one_ne_zero))).map _).mul hx
lemma solo(A:Op I): ∀ᵐ x∂μ, IsUnit (1-foldMo A x):=(tent (Seal A) (Seal.legal A) (Seal.hotel A) (Seal.free A)).mono (fun _ p=> (Matrix.isUnit_iff_isUnit_det ..).mpr (isUnit_iff_ne_zero.mpr p))
end
section
variable [Nonempty I]
abbrev pillar (n:ℕ):ℝ:= (n:ℝ)+1
def massN {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (w:ℕ→E)(n:ℕ):E:= (pillar n)⁻¹ • (∑ i∈Finset.range (n+1),w i)
lemma densityMo (U:UNI I)(k:IsUnit (1-U.val)): Tendsto (massN (fun n=> U.val^n)) atTop (𝓝 0):=by
 let E:=U.val; obtain ⟨v,hv⟩:= k; let R:Op I:=↑(v⁻¹); let S:=massN (fun n=>E^n); let B:= ‖R‖
 have he(n:ℕ):‖S n‖≤ (2* B)/(pillar n):=by
    let Y:=E^(n+1); let W:=∑ i∈Finset.range (n+1),E^i; have hz:W=(1-Y)*R:=by rw [←geom_sum_mul_neg,←hv,mul_assoc,Units.mul_inv]; rw [mul_one] -- tune
    have hp:‖Y‖ = 1:=tone (U^(n+1)) -- defeq coe.pow Prop not def
    have hF:0<(pillar n):=by unfold pillar; positivity
    have ht:‖1-Y‖ ≤ 2:= (norm_sub_le ..).trans (by rw [hp,norm_one]; norm_num)
    change ‖(pillar n)⁻¹ • W‖ ≤ _; rw [hz,norm_smul_of_nonneg (inv_nonneg.mpr hF.le),←inv_mul_eq_div]; exact mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg R))) (by positivity)
 apply squeeze_zero_norm he; simpa only using (show Tendsto (fun n=>2* B/pillar n) atTop (𝓝 0) from Filter.Tendsto.const_div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) (2*B)) -- tune
#print axioms solo
#print axioms densityMo
end
end YM.CF.Strata
