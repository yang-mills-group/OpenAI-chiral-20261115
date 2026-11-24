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
variable (X Y: Bench S) (g₁ : 0<u) (m n:ℕ)
abbrev Par (u:ℝ≥0):= parabola S m (OS.Semigroup.duration u)
local notation "P" => Par S
local notation "K"=> Cache S
local notation "F"=> parabola S
variable (z:ℂ)
lemma cacheA : Cache S (m+n)= K m * K n:=pow_add ..
lemma parEq (q:A=F m z) (h:z∈inside): A * K m=S.F z:= q ▸ change_m S m z h -- perhaps avoid
lemma FsAct (h:z∈inside): S.edge t*parabola S m z= F m (z+ OS.Semigroup.sideways t):=by
 ext1 x; apply cache_I S m; have hv: K m*S.edge t= S.edge t*K m:=(cupL S t).pow_left m; exact DFunLike.congr_fun (show K m*(S.edge t*parabola S m z)=K m* F m (z+ OS.Semigroup.sideways t) from (by rw [← mul_assoc,hv,mul_assoc,recover _ _ _ h,recover _ _ _ ((allow z t).mpr h)]; exact S.along h t)) x
lemma FRight (h:z∈inside): (F m z)*S.edge t= F m (z+ OS.Semigroup.sideways t):= Eq.trans (show (F m z)*S.edge t= _ from (by rw [← timeslot S t,(mslot ..).eq]; exact h)) (FsAct S t m z h) -- ms needs args
lemma P_Heq (h:0<u) : K m * P m u = S.E u:= K_E S m u h
lemma landDiv (v:ℝ≥0)(t:0<v)(h:v≤u) : Par S m u = Par S m v * S.E (u-v):=by
 ext1 x; apply cache_I S m; exact DFunLike.congr_fun (show K m*(P m u)= K m*(P m v*S.E (u-v)) from by rw [←mul_assoc,P_Heq _ u _ (t.trans_le h),P_Heq _ v _ t]; exact ((congrArg S.E (add_tsub_cancel_of_le h)).symm).trans (S.time v (u-v))) x
lemma parRev (h:0<u) : IsSelfAdjoint (P n u):=by
 have he:=congrArg (star:H.Op→H.Op) ( (change_m S n _ (dur.mpr h)).trans (S.roots_heat h)); rw [star_mul,(show IsSelfAdjoint (K n) from (saucer_sym S).pow n).star_eq, show star (S.E u)=S.E u from S.sym u] at he; ext1 i; apply cache_I S n; exact DFunLike.congr_fun (he.trans (K_E S n u h).symm) i
lemma resolve (h:0<u): P (m+n) u * K n = P m u:=by
 ext1 i; apply cache_I S m; have he:= (gear S (OS.Semigroup.duration u) (dur.mpr h) (m+n)).pow_left n; change K n * P (m+n) u=P (m+n) u * K n at he; exact DFunLike.congr_fun (Eq.trans (show K m*(P (m+n) u* K n)=S.E u from by rw [← he, ←mul_assoc, ← cacheA, K_E _ _ _ h]) (K_E S m u h).symm) i
lemma priceT (h:0<u): parabola S n (OS.Semigroup.duration u) X.val= hall S n (stove S u X):= by apply cache_I S n; rw [releases]; exact DFunLike.congr_fun (P_Heq S u n h) X.val
-- F shift regularity $t$ pos
abbrev flame (k:0<u): H →ₗ[ℂ] Bench S:= (S.E u).toLinearMap.codRestrict _ fun x=> ray S x u k
lemma rung (k:0<u): hall S n (flame S u k x) = P n u x:= by apply cache_I S n; rw [releases]; exact DFunLike.congr_fun (P_Heq S u n k).symm x
lemma warps {C:Type*}(ℱ:Filter C)(f:C→ℝ≥0)(p:Tendsto f ℱ (𝓝 u))(h:0<u)(k:∀ i,0<f i)(Y:C→H)(e:Tendsto Y ℱ (𝓝 x)): pays_to S ℱ (fun i=>flame S _ (k i) (Y i)) (flame S u h x):=by
 intro n; simp_rw [rung]; have hp:Tendsto (fun i=> P n (f i)) ℱ (𝓝 (P n u)):= (Bokeh S n (OS.Semigroup.duration u) (dur.mpr h)).continuousAt.tendsto.comp ((continuous_ofReal.continuousAt.tendsto.comp continuous_subtype_val.continuousAt.tendsto).comp p)
 exact (show Continuous (fun i:H.Op×H=>i.1 i.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hp.prodMk_nhds e)
#print axioms warps
#print axioms FsAct
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
