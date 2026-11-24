import YM.SU5.FiniteGaugeData.Seld.Sequel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
open Spectral Boundary Probe
local notation "V"=> S.unit
local notation "U"=> M S
variable (A B: H.Op)(p:E4)(g h: Test4)(c:ℂ)
local notation "W" => Bench S
local notation "□" => W →ₗ[ℂ] W
variable (w:∀ p:E4,S.unit.translation p x=x)
include w
lemma TurnU : S.edge t x=x:= timeslot S t ▸ w _ -- cast notation
lemma rlock : saucer S x=x:=by
 have he: HasDerivAt (fun t:ℝ=> R x) (parade S 0 x) 0 := (fanfare S x 0).congr_of_eventuallyEq (Eventually.of_forall (fun i=>by change R x= _; nth_rw 1 [← show R (S.edge i x)=_ from congrArg (saucer S) (TurnU S x i w)]; exact DFunLike.congr_fun (cupL S i).eq x)) -- danger rewriting inside
 have hv:I • (x-R x)=0:= by have HH:= he.unique (hasDerivAt_const (0:ℝ) (R x)); simpa [parade,S.birth,show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl,smul_sub] using HH
 exact (sub_eq_zero.mp ((smul_eq_zero.mp hv).resolve_left I_ne_zero)).symm
omit w
lemma helpO (h: R x=x): ∀ z:ℂ,z∈inside → slug S z x=0 := by
 intro z hz; have he: (S.F z-slug S z) x=S.F z x:= by nth_rw 1 [← h]; exact DFunLike.congr_fun (jalousie S z hz) x
 rw [_root_.sub_apply] at he; exact sub_eq_self.mp he
lemma heatO (h: R x=x)(z:ℂ)(p:z∈inside): S.F z x=x:=by
 let f(z:ℂ):= S.F z x; have he(z:ℂ)(p:z∈inside): HasDerivAt f 0 z := helpO S x h z p ▸ ((ContinuousLinearMap.apply ℂ H.space x).hasFDerivAt.comp_hasDerivAt (z) ((S.localHeat z p).differentiableAt.hasDerivAt)) -- tweak
 have hv := IsOpen.eqOn_of_deriv_eq (s:=inside) (f:=f) (g:=fun _=>f z) open_inside (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0 |>.isPreconnected) (fun i h=> (he i h).differentiableAt.differentiableWithinAt) (differentiableOn_const _) (fun i h=>Eq.trans ((he i h).deriv) (deriv_const .. |>.symm)) p rfl
 have hy: ∀ i:ℝ≥0,0 < i → f z=S.E i x:= fun i h=> (hv (dur.mpr h)).symm.trans (DFunLike.congr_fun (S.roots_heat h) x)
 have hk : Tendsto (fun i:ℝ≥0=> S.E i x) (𝓝[>] 0) (𝓝 (f z)):= tendsto_const_nhds.congr' ((show ∀ᶠ i in 𝓝[>] (0:ℝ≥0),0 < i from self_mem_nhdsWithin).mono fun i p=> hy i p)
 simpa [S.eZero] using tendsto_nhds_unique hk ((S.continuousE x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
lemma earthO (h:R x=x): S.E u x=x:=by
 rcases eq_zero_or_pos u with rfl|t; · rw [S.eZero]; rfl
 rw [← S.roots_heat t]; exact heatO S x h _ (dur.mpr t)
#print axioms rlock
#print axioms earthO
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
