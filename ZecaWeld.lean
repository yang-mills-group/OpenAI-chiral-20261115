import YM.SU5.FiniteGaugeData.Seld.NewMoon
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


variable {H K:Hilbert}{a:Axis}(S:OS.Semigroup H a)(T:OS.Semigroup K a)
structure Weld (f:H.space→L[ℂ]K.space):Prop where
 real t (x:H): f (S.E t x)=T.E t (f x)
 spatial u (x:H): f (S.U u x)=T.U u (f x)
namespace Weld
variable {S:OS.Semigroup H a}{T:OS.Semigroup K a}{f:H.space→L[ℂ]K.space}
 (h:Weld S T f)
include h
lemma sauce (x:H): f (saucer S x)=saucer T (f x):=by
 rw [saucer_apply, ship, ← f.integral_comp_comm (cupsI ..), saucer_apply, ship]
 congr 1; funext t; unfold cups highlande; rw [f.map_smul_of_tower,h.real]
lemma cache (n:ℕ)(x:H): f (Cache S n x)=Cache T n (f x):=by
 induction n generalizing x with
 | zero=>simp [Cache]
 | succ n ih=>
   change f ((saucer S^(n+1)) x)= _
   rw [Cache,pow_succ,pow_succ]
   exact (ih _).trans (congrArg (Cache T n) (h.sauce x))

lemma hol {z:ℂ} (p:z∈inside) (x:H) : f (S.F z x)=T.F z (f x):=by
  have A : AnalyticOnNhd ℂ (fun z=> f (S.F z x)) inside:= fun z p=>
    f.analyticAt _|>.comp ((ContinuousLinearMap.apply ℂ H.space x).analyticAt _|>.comp (S.localHeat z p))
  refine A.eqOn_of_preconnected_of_frequently_eq
    (g:=fun z=> T.F z (f x)) (fun z p=> (ContinuousLinearMap.apply ℂ K.space (f x)).analyticAt _|>.comp (T.localHeat z p))
    (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0|>.isPreconnected) (dur.mpr zero_lt_one) ?_ p
  have hy : Tendsto duration (𝓝[>] 1) (𝓝[≠] (duration 1)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with i hi
      exact fun he => (mem_Ioi.mp hi).ne' (Subtype.ext (Complex.ofReal_injective he))
  intro b
  obtain ⟨i,t,v⟩:= ((hy.eventually b).and self_mem_nhdsWithin).exists
  have r: 0 < i :=lt_trans zero_lt_one (mem_Ioi.mp v)
  apply t; rw [S.roots_heat r,T.roots_heat r];exact h.real ..

lemma edge (t:ℝ) (x:H): f (S.edge t x)= T.edge t (f x):=by
  rw [← sub_eq_zero]
  apply T.heat_faithful 1
  rw [map_sub, ← h.real, ← S.roots_heat zero_lt_one, ← T.roots_heat zero_lt_one,
      ← ContinuousLinearMap.comp_apply (S.F _), ← ContinuousLinearMap.comp_apply (T.F _),
      S.either (dur.mpr zero_lt_one), T.either (dur.mpr zero_lt_one)]
  exact sub_eq_zero.mpr (h.hol (by simp [inside,duration,sideways]) x)
lemma trans (p:E4)(x:H) : f (M S p x)=M T p (f x):=by
  change f (S.edge _ (S.U _ _))= T.edge _ (T.U _ _)
  rw [h.edge,h.spatial]
lemma par {z:ℂ}(p:z∈inside)(n:ℕ)(x:H): f (parabola S n z x)=parabola T n z (f x):=by
 apply cache_I T n
 rw [←h.cache]
 exact (congrArg f (DFunLike.congr_fun (recover S n z p) x)).trans ((h.hol p x).trans (DFunLike.congr_fun (recover T n z p) (f x)).symm)
def site (h:Weld S T f) : Bench S →ₗ[ℂ] Bench T:=
  (f.toLinearMap.comp ((Bench S).subtype)).codRestrict _
    fun u=> (bench T _).2 fun n=> ⟨f (hall S n u), by rw [← h.cache,releases];rfl⟩
lemma desk (n:ℕ)(u:Bench S) : f (hall S n u)=hall T n (h.site u):=by
 apply cache_I T n
 rw [←h.cache,releases,releases]
 rfl

open Boundary
variable {A:H.Op} {B:K.Op}
 (k: ∀ y:H,f (A y)=B (f y))
include k
lemma lunch (g:Test4)(x:H): f (valise S A g x)=valise T B g (f x):=by
 rw [vmap, vmap, ← f.integral_comp_comm (emberI ..)]
 congr 1; funext p
 rw [map_smul]
 change g p • f (M S p (A (M S (-p) x)))= g p • M T p (B (M T (-p) (f x)))
 rw [h.trans,k,h.trans]
lemma showtime (g:Test4)(n:ℕ)(u:Bench S) : h.site (ℑ S A g n u)=ℑ T B g n (h.site u):=by
 apply Subtype.ext; apply cache_I T n
 rw [native]
 change Cache T n (f (ℑ S A g n u).val) = _
 rw [←h.cache,native,h.lunch k,h.desk]
#print axioms showtime
