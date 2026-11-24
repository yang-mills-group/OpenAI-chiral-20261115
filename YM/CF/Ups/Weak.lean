import YM.CF.Ups.Mid
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.CF.TopPS
open Filter MeasureTheory Function Topology Metric
open scoped Topology BigOperators ENNReal InnerProductSpace
open InnerProductSpace
variable {α E F:Type}[MeasurableSpace α](μ:Measure α)[IsFiniteMeasure μ][NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E] [NormedAddCommGroup F][InnerProductSpace ℝ F][FiniteDimensional ℝ F] [CompleteSpace F]
local notation "ξ"=> Lp E 2 μ
variable (A:ℕ→Lp E 2 μ)(X:Lp E 2 μ)(Q:∀ y:Lp E 2 μ, Tendsto (fun i=> inner ℝ (A i) y) atTop (𝓝 (inner ℝ X y))) {D C:ℝ}(p:∀ i:ℕ,∀ᵐ x∂μ, ‖A i x‖ ≤ D)
local notation "Γ"=> E→L[ℝ] F
variable (AK:ℕ→ α→ E→L[ℝ] F)(M:∀ i,AEStronglyMeasurable (AK i) μ)(V:α→E→L[ℝ] F)(B:∀ i,∀ᵐ x∂μ,‖AK i x‖ ≤ C)(h:∀ᵐ x∂μ,Tendsto (fun i=>AK i x) atTop (𝓝 (V x)))
include Q
private lemma integ_V (V:α→Γ) (hv:AEStronglyMeasurable V μ){C:ℝ}(b:∀ᵐ x∂μ,‖V x‖ ≤ C): let f(i:ξ):F:=∫ x,V x (i x)∂μ
                  Tendsto (fun i=> f (A i)) atTop (𝓝 (f X))∧(∀ p:ξ, Integrable (fun x:α=> V x (p x)) μ):=by
 intro f; have hx(C':ξ):Integrable (fun x:α=> V x (C' x)) μ:= Integrable.mono' (((Lp.memLp C').integrable (by norm_num)).norm.const_mul C) (Continuous.comp_aestronglyMeasurable (show Continuous fun p:(Γ) × E =>p.1 p.2 from continuous_fst.clm_apply continuous_snd) (hv.prodMk (Lp.memLp C').1)) (b.mono fun x q=> ((V x).le_opNorm _).trans (mul_le_mul_of_nonneg_right q (norm_nonneg _))) -- tune API
 refine ⟨?_ ,hx⟩
 let S:= stdOrthonormalBasis ℝ F; let N:=Fin (Module.finrank ℝ F)
 have ht(Y:F): Tendsto (fun i=>inner ℝ Y (f (A i))) atTop (𝓝 (inner ℝ Y (f X))):=by
    let L (x:α):= ContinuousLinearMap.adjoint (V x) Y; have h:MemLp L 2 μ:=MemLp.of_bound ((Continuous.comp_aestronglyMeasurable (g:=fun f:E→L[ℝ]F=> ContinuousLinearMap.adjoint f Y) (by fun_prop) hv)) (C*‖Y‖) (b.mono fun x q=> ((ContinuousLinearMap.adjoint (V x)).le_opNorm Y).trans (by rw [ContinuousLinearMap.adjoint.norm_map]; exact mul_le_mul_of_nonneg_right q (norm_nonneg _)))
    have hC(i:ξ):inner ℝ Y (f i)=inner ℝ i (h.toLp L):=by unfold f; rw [← real_inner_comm i,L2.inner_def]; rw [← integral_inner (hx i) Y]; refine integral_congr_ae ((MemLp.coeFn_toLp h).mono fun x q=>?_ ); dsimp only; rw [q]; exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm -- unfold f
    simp_rw [hC]; exact Q _
 have hu(i:ξ):f i=∑ j,S.repr (f i) j • S j:= (S.sum_repr _).symm
 conv_rhs=> rw [hu X]
 nth_rw 1 [show (fun i=>f (A i))= _ from funext fun i=> hu (A i)]
 exact tendsto_finsetSum _ fun i _=> Filter.Tendsto.smul (show Tendsto (fun j:ℕ=> S.repr (f (A j)) i) atTop (𝓝 (S.repr (f X) i)) from by simp_rw [S.repr_apply_apply]; exact ht _) tendsto_const_nhds
include B p h M
lemma shell_P : Integrable (fun x:α=>V x (X x)) μ ∧ Tendsto (fun i=>∫ x,AK i x (A i x) ∂μ) atTop (𝓝 (∫ x,V x (X x)∂μ)):=by
 have hv:AEStronglyMeasurable V μ:= aestronglyMeasurable_of_tendsto_ae _ M h -- API
 have hx:∀ᵐ x∂μ,‖V x‖ ≤ C:=by filter_upwards [ae_all_iff.mpr B,h] with x v h; exact le_of_tendsto h.norm (Eventually.of_forall v)
 obtain ⟨q,hQ⟩:=integ_V μ A X Q V hv hx; let f(z:ℕ)(x:α):=AK z x (A z x)- V x (A z x)
 have ht(i:ℕ):Integrable (fun x:α=>AK i x (A i x)) μ:= (integ_V μ A X Q (AK i) (M i) (B i)).2 _
 have hT(i:ℕ):Integrable (f i) μ:=(ht i).sub (hQ _)
 have he(i:ℕ)(x:α): ‖f i x‖ ≤ ‖AK i x -V x‖*‖A i x‖:= (AK i x-V x).le_opNorm _
 have hZ(i:ℕ)(x:α)(v: ‖A i x‖≤D) : ‖f i x‖≤ ‖AK i x-V x‖*D:= (he ..).trans (mul_le_mul_of_nonneg_left v (norm_nonneg _))
 have hs:∀ᵐ x∂μ,Tendsto (fun i=> f i x) atTop (𝓝 0):=by
    filter_upwards [ae_all_iff.mpr p,h] with x p hz; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun i=>norm_nonneg _) (fun i=>hZ _ _ (p i)) ?_; simpa using (hz.sub_const (V x)).norm.mul_const D
 have ha(i:ℕ): ∀ᵐ x∂μ, ‖f i x‖ ≤ (C+C)*D:=(hx.and ((B i).and (p i))).mono fun x v=> (hZ _ _ v.2.2).trans (mul_le_mul_of_nonneg_right ((norm_sub_le ..).trans (add_le_add v.2.1 v.1)) ((norm_nonneg _).trans v.2.2))
 have h0:= tendsto_integral_of_dominated_convergence (fun _=>(C+C)*D) (fun i=>(hT i).1) (integrable_const _) ha hs; refine ⟨hQ _,?_⟩; rw [integral_zero] at h0; have hx:= h0.add q; rw [zero_add] at hx; apply hx.congr fun i=>?_; unfold f; change (∫ x,_-_∂μ)+(∫ x,_ ∂μ)=_; rw [integral_sub (ht i) (hQ _),sub_add_cancel]
omit B h M
lemma shade (s:α→E)(u:∀ᵐ x∂μ,Tendsto (fun i=> A i x) atTop (𝓝 (s x))) : (⇑X)=ᵐ[μ] s :=by
 let f(i:ℕ):=⇑(A i); have ht:∀ᵐ x∂μ,‖s x‖≤D:=by filter_upwards [ae_all_iff.mpr p,u] with x v h; exact le_of_tendsto h.norm (Eventually.of_forall v)
 have hs:MemLp s 2 μ:= .of_bound (aestronglyMeasurable_of_tendsto_ae _ (fun i=>(Lp.memLp (A i)).1) u) D ht; rw [show X=hs.toLp s from ?_]; exact hs.coeFn_toLp
 apply ext_inner_left ℝ; intro y; have v:=fun i:ℕ=> L2.integrable_inner (𝕜:=ℝ) y (A i)
 have h0:∀ᵐ x∂μ,Tendsto (fun i=> inner ℝ (y x) (A i x)) atTop (𝓝 (inner ℝ (y x) ((hs.toLp s) x))):=by
    filter_upwards [hs.coeFn_toLp,u] with x e v; rw [e]; exact tendsto_const_nhds.inner v
 have hv:= tendsto_integral_of_dominated_convergence (fun x=> ‖y x‖*D) (fun i=>(v i).1) (((Lp.memLp y).integrable (by norm_num)).norm.mul_const _) (fun i=> (p i).mono fun x p=> (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left p (norm_nonneg _))) h0
 apply tendsto_nhds_unique ?_ hv; simp_rw [← L2.inner_def] at *; rw [real_inner_comm]; exact (Q y).congr fun i=> real_inner_comm .. -- tune
end YM.CF.TopPS
