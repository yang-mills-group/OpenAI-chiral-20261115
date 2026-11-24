import YM.SU5.Reconstruction.Cashier.Honesty
import YM.SU5.Reconstruction.Crease.House
import YM.SU5.Reconstruction.Crease.Sensor
/-! # WOT in our Hilbert; need no more separability in the module. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter Metric Topology MeasureTheory Spectral Analysis InnerProductSpace ComplexConjugate TopologicalSpace Anvil
open scoped Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {ι:Type*}{H:Hilbert}
lemma Limit_World (u:Ultrafilter ι){A:ι→H.Op}{C:ℝ}(p:0≤C)(h:∀i, ‖A i‖ ≤ C): ∃ B:H.Op, ‖B‖≤ C∧Limited u A B:=by
 have e(x y:H):∃ c:ℂ,Tendsto (fun i=>inner ℂ (A i x) y) u (𝓝 c):= by
   let G:= Metric.closedBall (0:ℂ) (C*‖x‖*‖y‖); let a(t:ι):=inner ℂ (A t x) y
   obtain ⟨x,-,v⟩:=(isCompact_closedBall (0:ℂ) (C*‖x‖*‖y‖)).ultrafilter_le_nhds' (u.map a) (by
      apply Eventually.of_forall (p:=fun t:ι=> a t∈ G) _ (f:=↑u) -- tune
      intro i; exact mem_closedBall_zero_iff.mpr ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))) (norm_nonneg _))))
   exact ⟨x,v⟩
 let v(i:ι) (x y:H):=inner ℂ (A i x) y
 choose B hB using e
 have he (x y) : Tendsto (fun i=> v i x y) u (𝓝 (B x y)):= hB x y
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

-- membership closure clock & self. Use direct double-pricing definition
variable {L:Filter ι}[NeBot L]{A:ι→H.Op}{B:H.Op}(p:Limited L A B)
include p
lemma staysClosed {M:Net H}(h:∀ i, A i∈ M): B∈ M:= by
 rw [← M.commutant_commutant]; apply VonNeumannAlgebra.mem_commutant_iff.mpr; intro x e;
 ext1 y; apply ext_inner_left ℂ; intro z
 have hp(t): A t * x=x*A t:= VonNeumannAlgebra.mem_commutant_iff.mp e (A t) (h t)
 exact tendsto_nhds_unique_of_eventuallyEq ((p.toLeft (Pearl.still L x)).confirms z y) ((p.toRight (Pearl.still L x)).confirms z y) (Eventually.of_forall fun i => congrArg (fun B:H.Op=> inner ℂ z (B y)) (hp i).symm)
lemma staysSelf (h:∀ i,IsSelfAdjoint (A i)) : IsSelfAdjoint B:=by
 ext1 x; apply ext_inner_left ℂ; intro y; exact tendsto_nhds_unique_of_eventuallyEq ((star_Limited p).confirms y x) (p.confirms y x) (Eventually.of_forall fun i=> congrArg (fun B:H.Op=>inner ℂ y (B x)) (h i).star_eq)
end YM.BridgeClub
