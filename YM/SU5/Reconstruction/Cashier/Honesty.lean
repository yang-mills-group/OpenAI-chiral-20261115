import YM.SU5.Reconstruction.Anvil.OpCoin
import Mathlib.Analysis.InnerProductSpace.Dual
/-! # WOT honesty of our Limits (extract plain subsequences). -/
set_option autoImplicit false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup ConePrice Topology ComplexConjugate TopologicalSpace
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {ι:Type*}{H:Hilbert}
private lemma relay (f:ℕ→H→ℂ) {C:ℝ} (e:0<C)(t:∀ i x y, dist (f i x) (f i y)≤ C*dist x y)(h:ℕ→H)(p:DenseRange h)(v:∀ i,CauchySeq (fun n=> f n (h i))):∀x:H,CauchySeq (fun n=> f n x):=by
 intro x; rw [Metric.cauchySeq_iff]; intro ε i
 obtain ⟨y,hg⟩:=Metric.denseRange_iff.mp p x (ε/(4*C)) (by positivity)
 obtain ⟨N,j⟩:= Metric.cauchySeq_iff.mp (v y) (ε/2) (by positivity)
 refine ⟨N,fun a ha b hb=>?_⟩; have he(n:ℕ): dist (f n x) (f n (h y))<ε/4:=by
    apply lt_of_le_of_lt (t n x (h y)); apply lt_of_lt_of_le (mul_lt_mul_of_pos_left hg e); apply le_of_eq; field_simp
 exact (dist_triangle4 _ (f a (h y)) (f b (h y)) _).trans_lt (by linarith only [he a,he b,dist_comm (f b x) (f b (h y)),j a ha b hb])

private lemma limits {A:ℕ→H.Op}{C:ℝ}(p:0≤C)(h:∀i, ‖A i‖ ≤ C)(e:∀ x y:H, CauchySeq (fun i=>inner ℂ (A i x) y)):
    ∃ B:H.Op, ‖B‖≤ C∧Limited atTop A B:=by
 let v(i:ℕ) (x y:H):=inner ℂ (A i x) y
 choose B hB using fun x y=> cauchySeq_tendsto_of_complete (e x y)
 have he (x y) : Tendsto (fun i=> v i x y) atTop (𝓝 (B x y)):= hB x y
 have hp(x y): ‖B x y‖ ≤ (C*‖x‖)*‖y‖:= le_of_tendsto' (he x y|>.norm) fun i=> (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))) (norm_nonneg _))
 let L (x:H) : H →ₗ[ℂ] ℂ := {
  toFun:=B x
  map_add' y z:= by refine tendsto_nhds_unique (he x _) ?_; simpa only [v,inner_add_right] using ((hB x y).add (hB x z)) -- simp? goal function on v form
  map_smul' c y:=by apply tendsto_nhds_unique (he x _); simpa only [v,inner_smul_right,smul_eq_mul, RingHom.id_apply] using ((hB x y).const_mul c) }
 let Z(x:H): H→L[ℂ]ℂ:= (L x).mkContinuous (C*‖x‖) (hp x)
 let D(x:H):H:=(InnerProductSpace.toDual ℂ H).symm (Z x); have hD (x y:H):inner ℂ (D x) y=B x y:= InnerProductSpace.toDual_symm_apply
 let K : H→ₗ[ℂ] H:= {
   toFun := D
   map_add' x y:=by
      apply ext_inner_right ℂ; intro u; rw [inner_add_left,hD,hD,hD]; refine tendsto_nhds_unique (hB (x+y) u) ?_; simpa only [inner_add_left,map_add] using! (hB x u).add (hB y u)
   map_smul' c x := by
      rw [RingHom.id_apply]; apply ext_inner_right ℂ; intro u; rw [inner_smul_left,hD,hD]; apply tendsto_nhds_unique (hB (c • x) u); simpa only [map_smul,inner_smul_left] using! (hB x u).const_mul ((starRingEnd ℂ) c) }
 have hf(x:H): ‖K x‖≤ C*‖x‖:= by change ‖D x‖≤ _; unfold D; rw [LinearIsometryEquiv.norm_map]; exact LinearMap.mkContinuous_norm_le _ (by positivity) _
 refine ⟨K.mkContinuous C hf,LinearMap.mkContinuous_norm_le _ p hf, ⟨⟨C,p,Eventually.of_forall h⟩,fun x y=>?_⟩⟩
 have ht:= Complex.continuous_conj.continuousAt.tendsto (x:=B y x)|>.comp (hB y x)
 change Tendsto _ _ (𝓝 (inner ℂ x (D y)))
 rw [← hD y x] at ht; simpa only [Function.comp_def, inner_conj_symm] using ht

lemma Limited.extract [SeparableSpace (H:Type)] (A:ℕ→H.Op) {C:ℝ}(p:0≤C)(h:∀i, ‖A i‖ ≤ C):∃ ψ:ℕ→ℕ,StrictMono ψ ∧ ∃ B:H.Op, ‖B‖≤C ∧ Limited atTop (A ∘ ψ) B:=by
 let x:=denseSeq (H : Type)
 let X i (y z:H):= inner ℂ (A i y) z
 have ht(i:ℕ)(y z:H): ‖X i y z‖ ≤ C*‖y‖*‖z‖:= (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))) (norm_nonneg _))
 let T (k:ℕ×ℕ):= Metric.closedBall (0:ℂ) (C*‖x k.1‖*‖x k.2‖)
 let Y(i:ℕ)(b:ℕ×ℕ):=X i (x b.1) (x b.2)
 let Hx:=pi univ T
 obtain ⟨B,g,ψ,Tb,Hb⟩:= (isCompact_univ_pi (show ∀ i,IsCompact (T i) from fun _=> isCompact_closedBall ..)).tendsto_subseq (fun i=> show Y i∈ Hx from fun j _=> mem_closedBall_zero_iff.mpr (ht i _ _)) -- order
 have hy(z:ℕ)(y:H): CauchySeq (fun n=> X (ψ n) y (x z)):= relay (fun n p=> X (ψ n) p (x z)) (C:=C*‖x z‖+1) (by positivity) (fun i y w=> by
    simp only [dist_eq_norm,X]; rw [←inner_sub_left,←map_sub]; calc
      _ ≤ _ := ht (ψ i) (y-w) (x z)
      _ ≤ _:=by nlinarith [norm_nonneg (y-w)]) x (denseRange_denseSeq _) (fun i=> Tendsto.cauchySeq (show Tendsto _ _ (𝓝 (B (i,z))) from (tendsto_pi_nhds.mp Hb (i,z)))) y
 refine ⟨ψ,Tb,limits p (fun i=>h (ψ i)) (fun y=>?_ )⟩
 exact relay (fun n p=> X (ψ n) y p) (C:=C*‖y‖+1) (by positivity) (fun i z t=>by simp only [dist_eq_norm,X,←inner_sub_right]; exact (ht _ y _).trans (by nlinarith [norm_nonneg (z-t)])) x (denseRange_denseSeq _) (fun i=> hy i y)

lemma Limited.convertible (l:Filter ι) [NeBot l] {C:ℝ}(p:0≤C) {A:ι→H.Op}{B:H.Op}(h:Limited l A B)(w:∀ᶠ i in l, ‖A i‖ ≤ C): ‖B‖ ≤ C:= by
 apply ContinuousLinearMap.opNorm_le_bound _ p; intro x; have ht(y:H): ‖inner ℂ y (B x)‖ ≤ ‖y‖ * (C*‖x‖):= le_of_tendsto (h.confirms y x|>.norm) (w.mono fun i p=>(norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((A i).le_opNorm x).trans (mul_le_mul_of_nonneg_right p (norm_nonneg _))) (norm_nonneg _)))
 have hh:=ht (B x); rw [inner_self_eq_norm_sq_to_K] at hh; change ‖((‖B x‖:ℂ)^2)‖≤_ at hh; rw [norm_pow,Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hh; have hx:0≤ C*‖x‖:=by positivity
 nlinarith [norm_nonneg (B x)]
end YM.Anvil
#print axioms YM.Anvil.Limited.extract
#print axioms YM.Anvil.Limited.convertible
