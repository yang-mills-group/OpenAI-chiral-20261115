import SatinFixedContrastNovember4
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six Set
open Spectral Caino Orbit.Prairie
open OS.Semigroup
/- Heat-hole results in the true same-election Hilbert spaces. No claim of a cone. -/
namespace Thin
private lemma heat_diag (G : Hilbert) (T : OS.Semigroup G (3:Axis)) (t : ℝ≥0)
    (u : G) : (inner ℂ u (T.E (t + t) u)).re = ‖T.E t u‖ ^ 2 := by
  have h := T.swing t u (T.E t u)
  rw [← ContinuousLinearMap.comp_apply, ← T.time] at h
  change RCLike.re (inner ℂ u (T.E (t+t) u)) = _
  rw [← h, inner_self_eq_norm_sq]

lemma heat_contract (G : Hilbert) (T : OS.Semigroup G (3:Axis)) (t : ℝ≥0)
    (u : G) : ‖T.E t u‖ ≤ ‖u‖ :=
  ((T.E t).le_opNorm u).trans (mul_le_of_le_one_left (norm_nonneg _) (T.shrinks t))
lemma heat_decrease (G : Hilbert) (T : OS.Semigroup G (3:Axis)) (t s : ℝ≥0)
    (h : s ≤ t) (u : G) : ‖T.E t u‖ ≤ ‖T.E s u‖ := by
  nth_rw 1 [← tsub_add_cancel_of_le h]; rw [T.time, ContinuousLinearMap.comp_apply]; apply heat_contract

private lemma lap_falls (Z : Lead.Clan) : Tendsto
    (fun n:ℕ => (Cheer.FLap (promenade Z) 0 (↑(↑n + ↑n : ℝ):ℂ))) atTop (𝓝 0) := by
  let ν := (promenade Z).val
  let f(n:ℕ) := Cheer.tendsK 0 (↑(↑n + ↑n:ℝ):ℂ)
  have hp(n:ℕ) : 0 ≤ (↑(↑n + ↑n:ℝ):ℂ).re := by exact_mod_cast (show (0:ℝ) ≤ ↑n+↑n by positivity)
  have h(n:ℕ) := Cheer.destined (promenade Z) 0 (↑(↑n + ↑n:ℝ):ℂ) (home_bright Z) (hp n)
  have he (n:ℕ) (v:E4) : f n v = ↑(Real.exp (-((↑n+↑n:ℝ)*YM.time v))) := by
    unfold f Cheer.tendsK
    push_cast
    simp
  have hbound(n:ℕ) : ∀ᵐ v ∂ν, ‖f n v‖ ≤ (fun _ : E4 => (1:ℝ)) v := by
    filter_upwards [promenade_strict Z] with v t
    have htime : 0 ≤ YM.time v := ((Mink.strict_self _).mp t).1.le
    rw [he, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (by positivity) htime))
  have hlim : ∀ᵐ v∂ν, Tendsto (fun n=> f n v) atTop (𝓝 ((fun _ : E4=> (0:ℂ)) v)) := by
    filter_upwards [promenade_strict Z] with v g
    have htime : 0 < YM.time v:= ((Mink.strict_self _).mp g).1
    have ht : Tendsto (fun n:ℕ=> (↑n+↑n:ℝ)*YM.time v) atTop atTop := by
      have hx : Tendsto (fun n:ℕ=> (n:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop
      exact ((tendsto_atTop_mono (f:=fun n:ℕ=> (n:ℝ)) (g:=fun n:ℕ=> (n:ℝ)+n) (fun n=>by exact le_add_of_nonneg_right (Nat.cast_nonneg _)) hx)).atTop_mul_const htime -- check
    have hw := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht))
    rw [Complex.ofReal_zero] at hw
    exact hw.congr fun n=> (he n v).symm
  letI : IsFiniteMeasure ν := (promenade Z).2
  have hv := tendsto_integral_of_dominated_convergence (μ:=ν) (fun _=>1) (fun n=> (h n).aestronglyMeasurable) (integrable_const (1:ℝ)) hbound hlim
  rw [integral_zero] at hv
  exact hv

variable {P:Spine}{K:P.Register}{x:P.Spectrum0 3}{J:P.Ellis 3 x}{c r:ℕ→ℕ}
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "H"=> P.ManyF 3 ξ
local notation "T"=> P.seasons 3 ξ
local notation "b" Z:max i:max=> P.birthCloud x Z (c i) (r i)
variable (B:Experiment P K c r x J)
include B
private lemma thin_norm (Z : Lead.Clan) (t:ℝ≥0) :
  let ρ(i:ℕ) : ℝ≥0:= ⟨P.dew (c i) (r i),(P.dew_pos _ (B.launch.unitSize i)).le⟩
  Tendsto (fun i:ℕ => ‖(T).E (ρ i*t) (b Z i)‖ ^ 2) atTop
    (𝓝 ((Cheer.FLap (promenade Z) 0 ↑((↑(t+t)):ℝ)).re)):= by
  intro ρ
  let v(i:ℕ):= ρ i*t
  have hh:cutPulse 0=0:=Subtype.ext (show YM.position (0:Space3) 0=0 from (by rw [←Mink.combine_at]; exact map_zero _))
  have hp:P.dimensionS c r (fun i:ℕ=> v i+v i) ((↑(t+t)):ℝ):= tendsto_const_nhds.congr fun i=>by
    change (↑(t+t):ℝ) = ↑(v i+v i) / P.dew (c i) (r i)
    simp only [NNReal.coe_add,v,NNReal.coe_mul]
    change (t:ℝ)+t = (P.dew (c i) (r i)*(t:ℝ)+P.dew (c i) (r i)*t)/_
    field_simp [(P.dew_pos _ (B.launch.unitSize i)).ne']
  have hw := zoom_diagonal Z B.launch B.ready Twah.keyV_go (B.ground.2.1.accepted 3) 0 (t+t) _ hp
    (fun _=>0) (by rw [hh]; simp only [smul_zero]; exact tendsto_const_nhds)
  let f(i:ℕ):= inner ℂ (b Z i) ((T).E (v i+v i) (b Z i))
  simp_rw [OS.Semigroup.uZero, ContinuousLinearMap.id_apply] at hw
  exact (Complex.continuous_re.continuousAt.tendsto.comp hw).congr fun i=> heat_diag H (T) _ _

omit B in
private lemma abstract_hole (G:Hilbert)(T₀:OS.Semigroup G (3:Axis))(f:ℕ→G)
    (ρ:ℕ→ℝ≥0)(Hρ:Tendsto ρ atTop (𝓝 0)) (l:ℝ≥0→ℝ)
    (hf:∀ t:ℝ≥0, Tendsto (fun i:ℕ=> ‖T₀.E (ρ i*t) (f i)‖ ^ 2) atTop (𝓝 (l t)))
    (hw:Tendsto (fun n:ℕ=> l n) atTop (𝓝 0))(a:ℝ≥0)(ha:0<a):
    Tendsto (fun i:ℕ=> T₀.E a (f i)) atTop (𝓝 0):= by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (Metric.tendsto_nhds.mpr fun ε hε=> ?_)
  have hε':(0:ℝ)<ε^2:=pow_pos hε _
  obtain ⟨n, hn⟩ := (hw.eventually (gt_mem_nhds hε')).exists
  let v(i:ℕ): ℝ≥0:= ρ i * ↑n
  have Hv : Tendsto v atTop (𝓝 0):= by simpa only [zero_mul] using Hρ.mul_const (↑n : ℝ≥0)
  filter_upwards [Hv.eventually (gt_mem_nhds ha), (hf (↑n:ℝ≥0)).eventually (gt_mem_nhds (show l n<ε^2 from hn))] with i e h
  have hu := heat_decrease G T₀ a (v i) (show v i < a from e).le (f i)
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  exact lt_of_le_of_lt hu (lt_of_pow_lt_pow_left₀ 2 hε.le (show ‖T₀.E (v i) (f i)‖^2 < ε^2 from h))

lemma hole (Z:Lead.Clan)(a:ℝ≥0)(ha:0<a) :
    Tendsto (fun i:ℕ=> (T).E a (b Z i)) atTop (𝓝 0):= by
  let ρ(i:ℕ) : ℝ≥0:= ⟨P.dew (c i) (r i),(P.dew_pos _ (B.launch.unitSize i)).le⟩
  have Hρ:Tendsto ρ atTop (𝓝 0):= NNReal.tendsto_coe.mp (P.proper_dew c r B.launch)
  let l(t:ℝ≥0):=(Cheer.FLap (promenade Z) 0 ↑((↑(t+t)):ℝ)).re
  have hl:Tendsto (fun n:ℕ=> l n) atTop (𝓝 0):= by
    have he := (Complex.continuous_re.continuousAt.tendsto.comp (lap_falls Z))
    exact he.congr fun n=> (by dsimp [l,Function.comp_apply]; simp)
  exact abstract_hole H T (fun i=>b Z i) ρ Hρ l (thin_norm B Z) hl a ha


omit B in
lemma heat_diff_bound (G:Hilbert)(S:OS.Semigroup G (3:Axis))(a:ℝ≥0)(h:0<a):
    ∃ C>(0:ℝ), ∀ᶠ d:ℝ≥0 in 𝓝 0, ‖S.E a-S.E (a+d)‖ ≤ C*(d:ℝ) := by
  let q:=duration a
  obtain ⟨C,u,hC⟩:= (S.localHeat (duration a) (OS.Semigroup.dur.mpr h)).differentiableAt.hasFDerivAt.isBigO_sub.exists_pos
  refine ⟨C,u,?_⟩
  have ht : Tendsto (fun d:ℝ≥0=> duration (a+d)) (𝓝 0) (𝓝 q):= by
    rw [show q=duration (a+(0:ℝ≥0)) by simp [q]]
    have hc:Continuous duration:=Complex.continuous_ofReal.comp continuous_subtype_val
    exact (hc.comp (continuous_const.add continuous_id)).continuousAt.tendsto
  filter_upwards [ht.eventually hC.bound] with d h'
  have e:0<a+d:=by positivity
  change ‖S.F (duration (a+d))-S.F (duration a)‖ ≤ C*‖duration (a+d)-duration a‖ at h'
  rw [norm_sub_rev]
  rw [S.roots_heat e,S.roots_heat h] at h'
  convert h' using 1
  simp [duration]

omit B in
private lemma diff_paid (G:Hilbert)(S:OS.Semigroup G (3:Axis))(a:ℝ≥0)(h:0<a)
    (d:ℕ→ℝ≥0)(hd:Tendsto d atTop (𝓝 0)) (u:ℕ→G)(hu:∀ t:ℝ≥0, 0<t→ Tendsto (fun i:ℕ=> S.E t (u i)) atTop (𝓝 0)) :
    Tendsto (fun i:ℕ=> ‖S.E a (u i-S.E (d i) (u i))‖ / (d i:ℝ)) atTop (𝓝 0):= by
  have ha:0<a/2:=by positivity
  let v (i:ℕ):G:=S.E (a/2) (u i)
  obtain ⟨C,hC',he⟩:= heat_diff_bound G S (a/2) ha
  let D(i):=S.E (a/2)-S.E ((a/2)+d i)
  have hc:= hd.eventually he
  have hf:(∀ᶠ i in atTop, ‖D i (v i)‖ / (d i:ℝ) ≤ C*‖v i‖):= by
    filter_upwards [hc] with i p
    rcases eq_or_ne (d i) 0 with hv|hv; · simp only [hv,NNReal.coe_zero, div_zero]; exact mul_nonneg hC'.le (norm_nonneg _)
    apply (div_le_iff₀ (show 0<(d i:ℝ) from (d i).2.lt_of_ne (fun hg=> hv (Subtype.ext hg.symm)))).2
    calc
      _≤ ‖D i‖*‖v i‖:= (D i).le_opNorm _
      _≤ C*(d i:ℝ)*‖v i‖:= mul_le_mul_of_nonneg_right p (norm_nonneg _)
      _=_:= by ring
  have ht:Tendsto (fun i:ℕ=> ‖D i (v i)‖ / (d i:ℝ)) atTop (𝓝 0):= squeeze_zero' (.of_forall fun i=> div_nonneg (norm_nonneg _) (d i).2) hf (by simpa only [norm_zero,mul_zero] using (hu _ ha).norm.const_mul C)
  exact ht.congr fun i=> congrArg (fun x:G=>‖x‖/(d i:ℝ)) (by
    unfold D v; rw [sub_apply, map_sub, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,← S.time, ← S.time, ← S.time, add_halves, add_right_comm, add_halves])

lemma increment_zero : Tendsto (fun i=>P.increment (c i) (r i)) atTop (𝓝 0):= by
  apply NNReal.tendsto_coe.mp
  have hk:= increment_ratio B.launch
  change Tendsto (fun i=>(P.increment (c i) (r i):ℝ)/P.dew (c i) (r i)) atTop (𝓝 (1/2)) at hk
  have hh:= hk.mul (P.proper_dew c r B.launch)
  rw [mul_zero] at hh
  exact hh.congr fun i=> div_mul_cancel₀ _ (P.dew_pos _ (B.launch.unitSize i)).ne'

local notation "δ" i:max=> P.increment (c i) (r i)
local notation "m" Z:max i:max=> P.sixWard_macroVector x (c i) (r i) Z
lemma macro_o (Z:Lead.Clan)(a:ℝ≥0)(ha:0<a):
    Tendsto (fun i:ℕ=> ‖(T).E a (m Z i)‖/(δ i :ℝ)) atTop (𝓝 0) :=
  (diff_paid H T a ha (fun i=>δ i) (increment_zero B) (fun i=>b Z i) (hole B Z)).congr fun i=>
    congrArg (fun x':H=> ‖(T).E a x'‖/(δ i :ℝ)) (P.filtered_explicit ..).symm

-- Which physical tests are being compared? Any real smooth (not varying with grid)
-- normalized test in each half, supporting an independent-position purchase.
omit B
section
variable {G:Hilbert}
lemma dose_bound (D:SampleDose)(h:D.Normalized)(f:Vantage→G)(C:ℝ)
    (p:∀ i∈tsupport D.val, ‖f i‖ ≤ C) :
    ‖∫ i:Vantage,(D.val i:ℂ) • f i‖ ≤ C:= by
  have hu: Integrable D.val:= D.smooth.continuous.integrable_of_hasCompactSupport D.budget
  have hv:(∀ᵐ i ∂(volume:Measure Vantage),‖(D.val i:ℂ) • f i‖ ≤ D.val i * C):=
    Eventually.of_forall (fun i=> by
      by_cases he:D.val i=0
      · rw [he,Complex.ofReal_zero,zero_smul,norm_zero,zero_mul]
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (h.1 i)]; exact mul_le_mul_of_nonneg_left (p i (subset_closure he)) (h.1 i))
  exact (norm_integral_le_of_norm_le (hu.mul_const C) hv).trans_eq ((integral_mul_const C D.val).trans (by rw [h.2,one_mul]))
end

local notation "δ'" s:max n:max => P.increment s n
local notation "m'" Z:max s:max n:max=> P.sixWard_macroVector x s n Z
lemma launch_small {s n:ℕ}(Z:Lead.Clan){a:ℝ≥0}(w:ℝ)(D:SampleDose)(h:D.Normalized)
    (e:∀ i∈tsupport D.val, (a:ℝ)≤ i 3-w) :
    ‖P.launchCost x s n Z D w‖ ≤ ‖(T).E a (m' Z s n)‖:= by
  refine dose_bound (G:=H) D h _ _ ?_ -- explicit f
  intro i hi
  have hw:= e i hi
  have hu:(a : ℝ) ≤ ↑(i 3 - w).toNNReal:= hw.trans_eq (Real.coe_toNNReal _ (a.2.trans hw)).symm
  exact (P.cart_norm 3 ξ i _).trans_le (heat_decrease H T _ _ (NNReal.coe_le_coe.mp hu) _)
lemma land_small {s n:ℕ}(Z:Lead.Clan){a:ℝ≥0}(w:ℝ)(D:SampleDose)(h:D.Normalized)
    (e:∀ i∈tsupport D.val, (a:ℝ)≤ w-i 3) :
    ‖P.landingCost x s n Z D w‖ ≤ ‖(T).E a (m' Z s n)‖:= by
  refine dose_bound (G:=H) D h _ _ ?_ -- explicit f
  intro i hi
  have hw:= e i hi
  have hu:(a : ℝ) ≤ ↑(w-i 3).toNNReal:= hw.trans_eq (Real.coe_toNNReal _ (a.2.trans hw)).symm
  exact (P.cart_norm 3 ξ i _).trans_le (heat_decrease H T _ _ (NNReal.coe_le_coe.mp hu) _)

include B
lemma post_o (Z:Lead.Clan)(w:ℝ)(a:ℝ≥0)(ha:0<a)(F:ℕ→SampleDose)(h:∀ i,(F i).Normalized)
    (p:∀ i,∀ v∈tsupport (Dose.val (F i)), (a:ℝ)≤ v 3-w) :
    Tendsto (fun i:ℕ=> ‖P.launchCost x (c i) (r i) Z (F i) w‖/(δ i:ℝ)) atTop (𝓝 0):=
  squeeze_zero (fun i=> div_nonneg (norm_nonneg _) (δ i).property) (fun i=> div_le_div_of_nonneg_right
    (launch_small (s:=c i) (n:=r i) Z w (F i) (h i) (p i)) (δ i).property) (macro_o B Z a ha)
lemma pre_o (Z:Lead.Clan)(w:ℝ)(a:ℝ≥0)(ha:0<a)(F:ℕ→SampleDose)(h:∀ i,(F i).Normalized)
    (p:∀ i,∀ v∈tsupport (Dose.val (F i)), (a:ℝ) ≤ w-v 3) :
    Tendsto (fun i:ℕ=> ‖P.landingCost x (c i) (r i) Z (F i) w‖/(δ i:ℝ)) atTop (𝓝 0):=
  squeeze_zero (fun i=> div_nonneg (norm_nonneg _) (δ i).property) (fun i=> div_le_div_of_nonneg_right
    (land_small (s:=c i) (n:=r i) Z w (F i) (h i) (p i)) (δ i).property) (macro_o B Z a ha)

omit B in
private lemma sq_product (G:Hilbert)(v w:ℕ→G)(d:ℕ→ℝ)
    (h:Tendsto (fun i=>‖v i‖/d i) atTop (𝓝 0))(p:Tendsto (fun i=>‖w i‖/d i) atTop (𝓝 0)):
    Tendsto (fun i=>‖inner ℂ (v i) (w i)‖/(d i)^2) atTop (𝓝 0):= by
  have hv := h.mul p
  rw [mul_zero] at hv
  refine squeeze_zero (fun i=> div_nonneg (norm_nonneg _) (sq_nonneg _)) ?_ hv
  intro i; rw [div_mul_div_comm,sq]
  exact div_le_div_of_nonneg_right (norm_inner_le_norm ..) (mul_self_nonneg _)

lemma joint_o (Z W:Lead.Clan)(w:ℝ)(a:ℝ≥0)(ha:0<a)(F G:ℕ→SampleDose)(h:∀ i,(F i).Normalized)(k:∀ i,(G i).Normalized)
    (p:∀ i,∀ v∈tsupport (Dose.val (F i)), (a:ℝ) ≤ w-v 3) (u:∀ i,∀ v∈tsupport (Dose.val (G i)), (a:ℝ)≤ v 3-w) :
    Tendsto (fun i:ℕ=> ‖P.arrayReading x (c i) (r i) w (F i) (G i) Z W‖ / (δ i : ℝ)^2) atTop (𝓝 0):= by
  exact sq_product H _ _ _ (pre_o B Z w a ha F h p) (post_o B W w a ha G k u)

omit B
-- family renormalization by a scalar. Heat difference is the counterterm
-- already present in the macro experiment (time translate of the same Q).
variable (P x)
def frontProbe (s n t:ℕ)(Z:Lead.Clan)(F:SampleDose)(b':ℝ): P.Test:=
 (b':ℂ) • P.prepared t (P.RTest Z s n) F
def backProbe (s n t:ℕ)(Z:Lead.Clan)(G:SampleDose)(b':ℝ): P.Test:=
 (b':ℂ) • P.prepared t (P.FTest Z s n) G
def jointPrice (s n t:ℕ)(Z W:Lead.Clan)(F G:SampleDose)(b':ℝ) (L:P.Test→ₗ[ℂ]ℂ):ℂ:=
 L (frontProbe P s n t Z F b' * backProbe P s n t W G b')
def continuumJoint (s n:ℕ)(Z W:Lead.Clan)(F G:SampleDose)(w b':ℝ):ℂ:=
 (b':ℂ)^2 * P.arrayReading x s n w F G Z W

local notation "μ" t:max=> P.singleState 3 t x
local notation "Ξ" Z:max s:max n:max=> P.experimentBody Z s n

-- translation/width support persists on every finer frame
lemma aperture_shrink {c r:ℕ→ℕ}(h:Launch P c r) {ε:ℝ}(q:0<ε):
    ∀ᶠ i:ℕ in atTop,∀ Z:Lead.Clan,∀ p:Vantage,
      P.Aperture (Ξ Z (c i) (r i)) p⊆ Metric.ball p ε∧
      P.Aperture (P.RTest Z (c i) (r i)) p⊆Metric.ball p ε := by
  filter_upwards [(Filter.eventually_all.mpr fun j:Axis=> (limit_width h j).eventually (gt_mem_nhds q))] with i v
  intro Z p
  have h':P.Aperture (Ξ Z (c i) (r i)) p⊆ Metric.ball p ε:=by
    intro a hc
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff q]; intro j
    rw [Real.norm_eq_abs]; exact (hc j).trans_lt (v j)
  exact ⟨h',h'⟩

lemma factor_out (s n t:ℕ)(Z W:Lead.Clan)(F G:SampleDose)(b':ℝ)(L:P.Test→ₗ[ℂ]ℂ):
    jointPrice P s n t Z W F G b' L=(b':ℂ)^2 * P.splitArray t L F G s n Z W:= by
  unfold jointPrice frontProbe backProbe
  rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul]
  change (b':ℂ)*((b':ℂ)*_)=_
  rw [← mul_assoc,sq]; rfl
variable {P}
lemma pair_priced {s n:ℕ}{Z W:Lead.Clan}{F G:SampleDose}(w b':ℝ)(p:P.WallBefore (P.RTest Z s n) F w)(q:P.WallAfter (P.FTest W s n) G w)
    (J:P.Ellis 3 x)(hn:P.calibration.ℓ<n):
    Tendsto (fun t:ℕ=> jointPrice P s n t Z W F G b' (μ t)) atTop (𝓝 (continuumJoint P x s n Z W F G w b'))∧
    (∀ t, s≤t → (μ t) (frontProbe P s n t Z F b')=0 ∧ (μ t) (backProbe P s n t W G b')=0 ∧
        ∀ L:P.Test→ₗ[ℂ]ℂ, Factors P.calibration L→
          MatterWard P.calibration L∨ GaugeWard P.calibration L → jointPrice P s n t Z W F G b' L=0) := by
  have h := (P.measured_both x s n Z W F G w J p q).const_mul ((b':ℂ)^2)
  refine ⟨h.congr (fun t=> (factor_out P s n t Z W F G b' (μ t)).symm),fun t e=>⟨?_,?_,?_⟩⟩
  · unfold frontProbe; rw [map_smul,P.Dose_zero t (P.RTest Z s n) F x (P.body_central x s n Z).2 e,smul_zero]
  · unfold backProbe; rw [map_smul,P.Dose_zero t (P.FTest W s n) G x (P.body_central x s n W).1 e,smul_zero]
  intro L u v
  exact (factor_out P s n t Z W F G b' L).trans ((congrArg ((b':ℂ)^2 * ·) (P.split_test t (P.RTest Z s n) F (P.FTest W s n) G (P.test_apart _ F w _ G p q) e e Z.2 (P.sensor_mirror Z.2 3 _ (P.body_senses Z s n hn)) L u v)).trans (mul_zero _))

variable {x}
include B
lemma scaled_price_silence (b':ℕ→ℝ)(b0:ℝ)(hb:∀ᶠ i in atTop, |b' i| *(δ i:ℝ) ≤ b0) (Z W:Lead.Clan)(w:ℝ)(a:ℝ≥0)(ha:0<a)(F G:SampleDose)(p:F.Normalized)(q:G.Normalized)
    (hf:∀ v∈tsupport F.val,(a:ℝ)≤w-v 3)(hg:∀ v∈tsupport G.val,(a:ℝ)≤v 3-w):
    Tendsto (fun i:ℕ=> continuumJoint P x (c i) (r i) Z W F G w (b' i)) atTop (𝓝 0):= by
  let f(i):ℂ:=P.arrayReading x (c i) (r i) w F G Z W
  let d(i:ℕ):ℝ := δ i
  have hd(i:ℕ):0<d i:= P.increment_pos _ _ (B.launch.unitSize i)
  have ht:Tendsto (fun i:ℕ=>(b0^2)*(‖f i‖/(d i)^2)) atTop (𝓝 0):= by
    simpa only [mul_zero] using (joint_o B Z W w a ha (fun _=>F) (fun _=>G) (fun _=>p) (fun _=>q) (fun _=>hf) (fun _=>hg)).const_mul (b0^2)
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (.of_forall (fun _=>norm_nonneg _)) ?_ ht)
  filter_upwards [hb] with i u
  have hv:(|b' i| * (d i))^2 ≤ b0^2:= pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (hd i).le) u _
  unfold continuumJoint; rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  change |b' i| ^2 * ‖f i‖ ≤ _
  calc
     |b' i| ^2 * ‖f i‖ = (|b' i| * (d i))^2 * (‖f i‖/(d i)^2) := by field_simp [hd i|>.ne']
     _≤ _:= mul_le_mul_of_nonneg_right hv (div_nonneg (norm_nonneg _) (sq_nonneg _))


-- Boxes and election. In `experiment`, width fixed at i₀; in `hole` and
-- `grids` width shrinks along the same trajectory. 0-plane WALL price
-- for all experiments; therefore no intervals moving in the estimation.
variable (P x c r K J)
structure CollapseApplication (F G:SampleDose)(i₀:ℕ):Prop where
  experiment : P.ReturnsSix x (c i₀) (r i₀) 0 F G ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F G
  boxes: tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport G.val ⊆ reviewLaterBox.invites
  weights: F.Normalized ∧ G.Normalized
  widths(j:Axis): Tendsto (fun i:ℕ=> P.probeWidth (c i) (r i) j) atTop (𝓝 0)
  poses(ε:ℝ)(q:0<ε):∀ᶠ i:ℕ in atTop, let s:=c i; let n:=r i
    ∀ Z:Lead.Clan,∀ p:Vantage, P.Aperture (P.FTest Z s n) p⊆ Metric.ball p ε ∧
      P.Aperture (P.RTest Z s n) p⊆ Metric.ball p ε
  intrinsic(t i:ℕ)(Z:Lead.Clan)(e:c i≤t) (p:Cover) : let s:=c i; let n:=r i
    P.asked_at t (P.issuing t (P.RTest Z s n) p) (P.Aperture (P.RTest Z s n) (P.meshPose t p))∧
    P.asked_at t (P.issuing t (P.FTest Z s n) p) (P.Aperture (P.FTest Z s n) (P.meshPose t p))
  gauge(t i:ℕ)(Z:Lead.Clan)(d:ℝ) : frontProbe P (c i) (r i) t Z F d ∈ enclave P.calibration ∧
    backProbe P (c i) (r i) t Z G d ∈ enclave P.calibration
  comparator(t:ℕ): ∃ L, Comparison P.calibration (μ t) L ∧ L 1=1 ∧ GaugeWard P.calibration L ∧ MatterWard P.calibration L
  grids: ∀ᶠ i:ℕ in atTop, let s:=c i; let n:=r i
   ∀ (Z W:Lead.Clan)(d:ℝ), Tendsto (fun t:ℕ=> jointPrice P s n t Z W F G d (μ t)) atTop (𝓝 (continuumJoint P x s n Z W F G 0 d)) ∧
    (∀ t, s≤t → (μ t) (frontProbe P s n t Z F d)=0 ∧ (μ t) (backProbe P s n t W G d)=0 ∧
        ∀ L:P.Test→ₗ[ℂ]ℂ, Factors P.calibration L→
          MatterWard P.calibration L∨ GaugeWard P.calibration L → jointPrice P s n t Z W F G d L=0)
  states(i:ℕ)(Z:Lead.Clan): Tendsto (fun t=>P.postVector x (c i) t (r i) Z G 0) atTop (𝓝 (P.enter 3 ξ (P.launchCost x (c i) (r i) Z G 0))) ∧
    Tendsto (fun t=>P.preVector x (c i) t (r i) Z F 0) atTop (𝓝 (P.enter 3 ξ (P.landingCost x (c i) (r i) Z F 0)))
  minimal : Tendsto (fun i:ℕ=> δ i) atTop (𝓝 0) ∧ ∀ i:ℕ, 0<δ i
  state_price(Z:Lead.Clan): Tendsto (fun i:ℕ=> ‖P.launchCost x (c i) (r i) Z G 0‖/(δ i:ℝ)) atTop (𝓝 0)∧
    Tendsto (fun i:ℕ=> ‖P.landingCost x (c i) (r i) Z F 0‖/(δ i:ℝ)) atTop (𝓝 0)
  telescope(Z W:Lead.Clan):Tendsto (fun i:ℕ=> ‖P.arrayReading x (c i) (r i) 0 F G Z W‖ / (δ i : ℝ)^2) atTop (𝓝 0)
  no(Z W:Lead.Clan)(D:ℕ→ℝ)(M:ℝ)(h:∀ᶠ i in atTop, |D i| * (δ i:ℝ)≤M):
    Tendsto (fun i:ℕ=> continuumJoint P x (c i) (r i) Z W F G 0 (D i)) atTop (𝓝 0)
  necessary(Z:Lead.Clan)(D:ℕ→ℝ)(ε:ℝ)(pε:0<ε)
    (h:∀ᶠ i in atTop, ε ≤ ‖continuumJoint P x (c i) (r i) Z Z F G 0 (D i)‖ ):
    ∀ M:ℝ, ∃ᶠ i in atTop, M< |D i| * (δ i:ℝ)
variable {P c r K x J}
local notation "X'"=>reviewEarlierBox
local notation "Y'"=>reviewLaterBox
omit B in
private lemma separated {s n:ℕ}{F G:SampleDose}(p:P.probeWidth s n 3<1)(q:tsupport F.val ⊆ (X').invites)(t:tsupport G.val ⊆ (Y').invites)(Z:Lead.Clan): P.WallBefore (P.RTest Z s n) F 0 ∧ P.WallAfter (P.FTest Z s n) G 0 := by
  refine ⟨fun i hi=> ?_,fun i hi=> ?_⟩
  · change i 3+P.probeWidth s n 3<0; have he:i 3 < -1:= ((q hi) (3:Axis) (Set.mem_univ _)).2; linarith only [p,he]
  change 0+P.probeWidth s n 3 < i 3; have he:1 < i 3:= ((t hi) (3:Axis) (Set.mem_univ _)).1; linarith only [p,he]

lemma collapse (F G:SampleDose)(f:F.Normalized)(g:G.Normalized)(q:tsupport F.val⊆(X').invites)(t:tsupport G.val⊆(Y').invites)(i₀:ℕ)(h:P.ReturnsSix x (c i₀) (r i₀) 0 F G) : CollapseApplication P K x c r F G i₀:= by -- order check!
  have hf(v:Vantage)(u:v∈tsupport F.val): ((1:ℝ≥0):ℝ)≤ (0:ℝ)-v 3:= by have he:v 3 < -1:= ((q u) (3:Axis) (Set.mem_univ _)).2; change 1≤_; linarith only [he]
  have hg(v:Vantage)(u:v∈tsupport G.val): ((1:ℝ≥0):ℝ)≤ v 3-(0:ℝ):= by have he:1<v 3:= ((t u) (3:Axis) (Set.mem_univ _)).1; change 1≤_; linarith only [he]
  have n(Z W:Lead.Clan)(D:ℕ→ℝ)(M₁:ℝ)(e:∀ᶠ i in atTop, |D i| * (δ i:ℝ)≤M₁) := scaled_price_silence B D M₁ e Z W 0 1 one_pos F G f g hf hg
  refine { experiment:=⟨h,P.reviewWardContrast K x _ _ 0 F G h⟩, boxes:=⟨q,t⟩, weights:=⟨f,g⟩,
           widths:=limit_width B.launch, poses:= fun _ e => aperture_shrink P B.launch e
           intrinsic t i Z e p:=⟨⟨_,P.issuing_support t p (P.RTest Z (c i) (r i)),P.inside_now t p (P.RTest Z (c i) (r i)) (show c i≤t from e)⟩,⟨_,P.issuing_support t p (P.FTest Z (c i) (r i)), P.inside_now t p (P.FTest Z (c i) (r i)) (show c i≤t from e)⟩⟩
           gauge t i Z d:=⟨Subalgebra.smul_mem (enclave P.calibration) (P.prepared_color t (P.RTest Z (c i) (r i)) F) (d:ℂ),Subalgebra.smul_mem (enclave P.calibration) (P.prepared_color t (P.FTest Z (c i) (r i)) G) (d:ℂ)⟩
           comparator t:= P.comparator t x
           grids:= ?_
           states i Z:=⟨P.toLaunch x _ _ _ G _ J, P.toLand x _ _ _ F _ J⟩
           minimal:=⟨increment_zero B,fun i=>P.increment_pos _ _ (B.launch.unitSize i)⟩
           state_price Z:=⟨post_o B Z 0 (1:ℝ≥0) one_pos (fun _=>G) (fun _=>g) (fun _=>hg),pre_o B Z 0 (1:ℝ≥0) one_pos (fun _=>F) (fun _=>f) (fun _=>hf)⟩
           telescope Z W:=joint_o B Z W 0 (1:ℝ≥0) one_pos (fun _=>F) (fun _=>G) (fun _=>f) (fun _=>g) (fun _=>hf) (fun _=>hg)
           no:= n
           necessary:= ?_ }
  · filter_upwards [(limit_width B.launch 3).eventually (gt_mem_nhds (show (0:ℝ)<1 from one_pos)), B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i u v
    exact fun Z W d=> pair_priced x _ d (separated u q t Z).1 (separated u q t W).2 J v
  intro Z D ε pε e M₁ v
  obtain ⟨i,p,k⟩:= (((n Z Z D M₁ (v.mono (fun i=> le_of_not_gt))).norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using pε))).and e).exists
  exact k.not_gt p
#check @CollapseApplication
-- Application with concrete supplier request. Chooses a single experiment
-- from the general theorem with 0 wall, no re-election in the hole.
omit B
theorem onVacuum : ∃ (P:Spine)(K:P.Register),
    uniform P K (fun _ _ _ _ _ _ _ _ _ _ _ _=> 0) 1 1 ∧
    ∃ (x:P.Spectrum0 3)(c r:ℕ→ℕ)(J:P.Ellis 3 x), P.Experiment K c r x J∧∃ (F G:SampleDose)(i:ℕ), CollapseApplication P K x c r F G i:= by
  obtain ⟨P,K,h,c,r,x,z,J,B,L⟩:=macroscopicSatin (fun _ _ _ _ _ _ _ _ _ _ _ _ => 0) 1 1 one_pos id
  refine ⟨P,K,h,x,c,r,J,B,?_⟩
  let order:Orders:=⟨fun _=>true,rfl⟩
  have sep:(X').Later (Y') order 0:=by intro j; norm_num [Doorway.Later,reviewEarlierBox,reviewLaterBox,order]
  let V(i:Fin 3):Bool:=false
  obtain ⟨p,a,t,w,u⟩:= authorize V
  obtain ⟨i,⟨A,wb,F,G,xF,xG,e,hF,hG,y⟩,hm,Q⟩:= ((packs_within_rectangles L _ _ u (X') (Y') order sep).and ((B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and ((limit_width B.launch 3).eventually (gt_mem_nhds (show (0:ℝ)<1 from one_pos))))).exists
  let l:=c i; let k:=r i
  have hg(Z:Lead.Clan):= separated (P:=P) (s:=l) (n:=k) (show P.probeWidth l k 3<1 from Q) hF hG Z
  have hr:P.arrayReading x l k wb F G=P.arrayReading x l k 0 F G:= tendsto_nhds_unique e.steady (P.answersTogether x l k _ J F G (fun Z=> (hg Z).1) (fun Z=>(hg Z).2)) -- check order
  exact ⟨F,G,i,collapse B F G xF xG hF hG i (P.paidReturn x l k 0 F G (fun Z=>(hg Z).1) (fun Z=> (hg Z).2) J (hr ▸ e.poles) hm)⟩
#print axioms onVacuum
#print axioms joint_o
#print axioms pair_priced
#check @onVacuum
#print CollapseApplication
end Thin
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
