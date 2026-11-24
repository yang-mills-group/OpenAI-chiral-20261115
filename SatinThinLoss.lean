import SatinFixedContrastNovember4

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators

namespace YM.ThinLoss
open OS.Semigroup
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)

/-- Cost of a single vanishing time tick at any fixed strictly positive setback. The
constant and the neighborhood of eligible ticks need not be scale-effective. -/
theorem heatIncrement (b : ℝ≥0) (hb : 0 < b) {dt : ℕ → ℝ≥0}
    (hd : Tendsto dt atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i : ℕ in atTop,
      ‖S.E (b + dt i) - S.E b‖ ≤ C * (dt i : ℝ) := by
  have ha := S.localHeat (duration b) (show 0 < (duration b).re from hb)
  obtain ⟨C,p,h⟩ := ha.differentiableAt.isBigO_sub.exists_pos
  have he : Tendsto (fun i => duration (b + dt i)) atTop (𝓝 (duration b)) := by
    unfold duration; push_cast
    simpa using ((tendsto_const_nhds (x:=((b:ℝ):ℂ))).add (Complex.continuous_ofReal.continuousAt.tendsto.comp (NNReal.tendsto_coe.mpr hd)))
  refine ⟨C,p,(he.eventually h.bound).mono ?_⟩
  intro i hi
  have hv : 0 < b + dt i := add_pos_of_pos_of_nonneg hb bot_le
  rw [S.roots_heat hv,S.roots_heat hb, show duration (b + dt i) - duration b = duration (dt i) by
    unfold duration; push_cast; abel] at hi
  simpa [duration] using hi

theorem cost_le (t : ℝ≥0) (u : H) : ‖S.E t u‖ ≤ ‖u‖ :=
  ((S.E t).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))

theorem cost_mono {b c : ℝ≥0} (hb : b ≤ c) (u : H) : ‖S.E c u‖ ≤ ‖S.E b u‖ := by
  rw [← tsub_add_cancel_of_le hb,S.time,ContinuousLinearMap.comp_apply]; exact cost_le S _ _

/-- After crossing any fixed distance 2b, even inverse-tick normalization doesn't save
sequences escaping to infinity in energy. In this inequality a norm at distance b is
charged only on the front vector, not assumed on the width-differenced vector. -/
theorem inverse_cost (b : ℝ≥0) (hb : 0 < b) {d : ℕ → ℝ≥0} (hd : Tendsto d atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i : ℕ in atTop, ∀ t : ℝ≥0, b + b ≤ t → ∀ u : H,
      ‖S.E t (u - S.E (d i) u)‖ ≤ (C * (d i:ℝ)) * ‖S.E b u‖ := by
  obtain ⟨C,q,h⟩ := heatIncrement S b hb hd
  refine ⟨C,q,h.mono fun i hi t p u => (cost_mono S p _).trans ?_⟩
  have e : S.E (b+b) (u-S.E (d i) u) = (S.E b-S.E (b+d i)) (S.E b u) := by
    rw [map_sub,sub_apply, ←ContinuousLinearMap.comp_apply (S.E b) (S.E b),←S.time,
        ←ContinuousLinearMap.comp_apply (S.E (b+b)) (S.E (d i)),←S.time,
        ←ContinuousLinearMap.comp_apply (S.E (b+d i)) (S.E b),←S.time,add_right_comm]
  rw [e]
  refine ((S.E b-S.E (b+d i)).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rwa [norm_sub_rev]

open Cheer
lemma shore_zero : Cheer.shore 0 = 0 := by
  apply Subtype.ext
  change position (0:Space3) 0 = 0
  exact (position_eta (0:E4))

/-- No rate on the zoom weak convergence is used. -/
theorem verticalL {μ : Cheer.Narrow} (hm : ∀ᵐ p∂(μ:Measure E4), 0 < time p) :
    Tendsto (fun n:ℕ => FLap μ 0 ((n:ℝ):ℂ)) atTop (𝓝 0) := by
  let F (n:ℕ) := tendsK 0 ((n:ℝ):ℂ)
  have hb : Brilliant μ := hm.mono fun _ h => h.le
  have f(n:ℕ) : Integrable (F n) (μ:Measure E4) := destined _ _ _ hb (show 0≤ (n:ℝ) by positivity)
  have e(n:ℕ)(p:E4) : F n p = ↑(Real.exp (-((n:ℝ)*time p))) := by
    unfold F tendsK; push_cast; simp only [inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub]
  have l : ∀ᵐ p∂(μ:Measure E4), Tendsto (fun n=>F n p) atTop (𝓝 ((0:E4→ℂ) p)) := by
    filter_upwards [hm] with p h
    have hv : Tendsto (fun n:ℕ=>(n:ℝ)*time p) atTop atTop := Tendsto.atTop_mul_const h tendsto_natCast_atTop_atTop
    have hp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hv)
    simp_rw [e]; simpa only [Function.comp_def,Complex.ofReal_zero,Pi.zero_apply] using Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  have hz := tendsto_integral_of_dominated_convergence (μ:=(μ:Measure E4)) (fun _=>1) (fun n=>(f n).1)
    (integrable_const (1:ℝ)) (fun n=> hb.mono fun p h => Cheer.withinK 0 ((n:ℝ):ℂ) p (show 0≤ (n:ℝ) by positivity) h) l
  simpa [F,FLap] using hz

/-- Escape on a shrinking zoom. -/
theorem setbackEscape (S : OS.Semigroup H timeAxis) (v : ℕ → H) (r : ℕ → ℝ≥0) (hr : Tendsto r atTop (𝓝 0))
 
    {μ : Cheer.Narrow} (pμ : ∀ᵐ p∂(μ:Measure E4), 0 < time p)
    (hμ : Lyrical μ (fun i=> Cheer.outlay S (v i) (r i))) -- S timeAxis
    (b : ℝ≥0) (p : 0 < b) : Tendsto (fun i=> S.E b (v i)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply Metric.tendsto_nhds.mpr; intro ε he
  obtain ⟨n,hn⟩ := (((Complex.continuous_re.tendsto _).comp (verticalL pμ)).eventually
    (gt_mem_nhds (a:=ε^2) (show (0:ℂ).re < ε^2 from sq_pos_of_pos he))).exists
  let t : ℝ≥0 := n/2
  let c(i:ℕ) := r i * t
  let W (i:ℕ) := S.E (c i) (v i)
  have hm := hμ.meets 0 (t+t)
  have hh : Tendsto (fun i=> ‖W i‖^2) atTop (𝓝 (FLap μ 0 (↑(n:ℝ))).re) := by
    have ht:= (Complex.continuous_re.tendsto _).comp hm
    rw [show (↑(↑(t+t):ℝ):ℂ)=(↑(n:ℝ):ℂ) by dsimp [t]; push_cast; ring] at ht
    refine ht.congr fun i=> ?_
    change (FLap (outlay S (v i) (r i)) _ _).re = _
    rw [show ((↑(n:ℝ)):ℂ)=(↑(↑(t+t):ℝ):ℂ) by dsimp [t]; push_cast; ring,
      back, shore_zero, smul_zero, S.uZero, ContinuousLinearMap.id_apply, mul_add,
      S.time, ContinuousLinearMap.comp_apply, ← S.swing, inner_self_eq_norm_sq_to_K]
    change ((((‖W i‖:ℝ):ℂ)^2).re)=_
    rw [←Complex.ofReal_pow,Complex.ofReal_re]
  have hk : Tendsto c atTop (𝓝 0) := by simpa using hr.mul_const t
  filter_upwards [hh.eventually (gt_mem_nhds hn), hk.eventually (gt_mem_nhds p)] with i h k
  have he' := cost_mono S k.le (v i)
  rw [dist_eq_norm,sub_zero, Real.norm_of_nonneg (norm_nonneg _)]
  change ‖S.E b (v i)‖ < ε
  change _ ≤ ‖W i‖ at he'
  nlinarith [norm_nonneg (W i)]


theorem inverse_costs {I: Type} (b:ℝ≥0)(p:0<b) (d:ℕ→ℝ≥0)(q:Tendsto d atTop (𝓝 0))
    (u w:ℕ→I→H)(eq:∀ i Z,w i Z=u i Z-S.E (d i) (u i Z)) :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ i in atTop, ∀ (Z:I)(t:ℝ≥0), b+b ≤ t →
      ‖S.E t (w i Z)‖ ≤ C * (d i : ℝ) * ‖S.E b (u i Z)‖ := by
  obtain ⟨C,hC,h⟩:= inverse_cost S b p q
  exact ⟨C,hC,h.mono fun i hi Z t ht=>(eq i Z).symm ▸ hi t ht (u i Z)⟩

end YM.ThinLoss
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance
open Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker ENNReal Classical
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
open Aria Casting Six
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "Hc" => P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "T" => P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "ν" i:max Z:max => P.birthCloud x Z (c i) (r i)
local notation "ψ" i:max Z:max => P.sixWard_macroVector x (c i) (r i) Z
local notation "d" i:max => P.increment (c i) (r i)


include B
/-- On one purchase. All the paid zoom clouds escape as seen with even arbitrarily short
fixed physical Euclidean time smear. -/
theorem cloud_escape (Z:Lead.Clan)(b:ℝ≥0)(p:0<b) :
    Tendsto (fun i=> (T).E b (ν i Z)) atTop (𝓝 0) := by
  let H(i:ℕ):ℝ≥0 := ⟨P.dew (c i) (r i),(P.dew_pos _ (B.launch.unitSize i)).le⟩
  apply ThinLoss.setbackEscape T _ H (NNReal.tendsto_coe.mp (P.proper_dew _ _ B.launch))
    ((promenade_strict Z).mono (fun i h => ((Mink.strict_self _).1 h).1)) _ b p
  exact lyricalCloud Z B.launch B.ready Twah.keyV_go (B.ground.2.1.accepted 3)

theorem increment_zero : Tendsto (fun i=> d i) atTop (𝓝 0) := by
  let D(i:ℕ):=P.dew (c i) (r i)
  have he : Tendsto (fun i=> (d i:ℝ) / D i) atTop (𝓝 (1/2)) := increment_ratio B.launch
  apply NNReal.tendsto_coe.mp
  have hv := he.mul (P.proper_dew _ _ B.launch)
  rw [mul_zero] at hv
  exact hv.congr fun i=>div_mul_cancel₀ _ (P.dew_pos _ (B.launch.unitSize i)).ne'


theorem inverse_tick (b:ℝ≥0) (p:0<b) :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ i in atTop, ∀ (Z:Lead.Clan) (t:ℝ≥0), b+b ≤ t →
      ‖(T).E t (ψ i Z)‖ ≤ C * (d i:ℝ) * ‖(T).E b (ν i Z)‖ :=
  ThinLoss.inverse_costs T b p _ (increment_zero B) _ _ (fun _ _=> P.filtered_explicit ..)

omit B
private lemma normalizedCost {H:Hilbert}(F:SampleDose)(p:F.Normalized)
    (g:Vantage→ H)(hg:Continuous g)(C:ℝ)(h:∀ x∈tsupport F.val, ‖g x‖ ≤ C) :
    ‖∫ x:Vantage,(F.val x:ℂ) • g x‖ ≤ C := by
  let f(x:Vantage): H := (F.val x:ℂ) • g x
  have he: Integrable f := weightedMoney F _ g hg
  have e:Integrable F.val := F.smooth.continuous.integrable_of_hasCompactSupport F.budget
  calc
    ‖∫ (x:Vantage), f x‖ ≤ ∫ (x:Vantage), ‖f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x:Vantage,F.val x * C:= by
      apply integral_mono he.norm (e.mul_const _)
      intro y; by_cases t:y∈ support F.val
      · dsimp only [f]; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (p.1 _)]
        exact mul_le_mul_of_nonneg_left (h y (subset_closure t)) (p.1 _)
      dsimp only [f]; rw [show F.val y=0 from notMem_support.mp t]; simp
    _ = C:= by rw [integral_mul_const,p.2,one_mul]


/-- Ray cost only needs to be bounded on supports. The exposures can move if desired,
including arbitrarily concentrated exposures, paying just the normalized mass. -/
private lemma wrists {H : Hilbert} {a : Axis} (S:OS.Semigroup H a) (b:ℝ≥0)(p:0<b)
    (tick:ℕ→ℝ≥0)(q:Tendsto tick atTop (𝓝 0))(pos:∀ i,0<tick i)
    (u w:ℕ→H)(e:Tendsto (fun i=>S.E b (u i)) atTop (𝓝 0))(eq:∀ i,w i=u i-S.E (tick i) (u i))
    (F:ℕ→SampleDose)(f:∀ᶠ i in atTop,(F i).Normalized)
    (g:ℕ→Vantage→H)(hg:∀ i,Continuous (g i))(t:ℕ→Vantage→ℝ≥0)
    (s:∀ᶠ i in atTop,∀ x∈tsupport (F i).val,b+b≤t i x)
    (ray:∀ i x,‖g i x‖=‖S.E (t i x) (w i)‖):
    Tendsto (fun i=> (((tick i:ℝ):ℂ)⁻¹) • ∫ x:Vantage,((F i).val x:ℂ) • g i x) atTop (𝓝 0):=by
  let v(i):=∫ x:Vantage,((F i).val x:ℂ) • g i x
  obtain ⟨C,_,h'⟩:= ThinLoss.inverse_cost S b p q
  have h:Tendsto (fun i=>C*‖S.E b (u i)‖) atTop (𝓝 0):=by simpa using e.norm.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ h
  filter_upwards [f,h',s] with i H' l k
  let r:ℝ:=tick i
  have hr:0<r:= NNReal.coe_pos.mpr (pos i)
  have hv:‖v i‖ ≤ C*r* ‖S.E b (u i)‖:= normalizedCost (F i) H' (g i) (hg i) _ fun x m=> (ray i x).trans_le ((eq i).symm ▸ l _ (k _ m) (u i))
  rw [norm_smul,norm_inv,Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  change r⁻¹ * ‖v i‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hv (inv_pos.mpr hr).le).trans_eq
  field_simp

include B
lemma filterTickPrice (Z:Lead.Clan)(b:ℝ≥0)(hb:0<b)(F:ℕ→SampleDose)(p:∀ᶠ i in atTop,(F i).Normalized)
    (a:ℕ→ℝ)(h:∀ᶠ i in atTop,∀ x'∈tsupport (F i).val,↑(b+b) ≤ x' 3 - a i) :
    Tendsto (fun i=> ((↑(d i):ℂ)⁻¹) • P.launchCost x (c i) (r i) Z (F i) (a i)) atTop (𝓝 0):=by
  let t(i:ℕ)(y:Vantage):=(y 3-a i).toNNReal
  let f(i:ℕ)(y:Vantage):=P.forwardRay x Z (c i) (r i) (a i) y
  have he(i y): ‖f i y‖= ‖(T).E (t i y) (ψ i Z)‖:= by
    exact (congrArg (fun U:(P.ManyF 3 ξ).Op => ‖U ((T).E (t i y) (ψ i Z))‖) (P.uses_cart 3 ξ y)).trans ((T).unitary ..)
  exact wrists T b hb _ (increment_zero B) (fun i=>P.increment_pos (c i) (r i) (B.launch.unitSize i)) _ _
    (cloud_escape B Z b hb) (fun _=> P.filtered_explicit ..) F p f (fun i=> P.hot_cont x _ _ _ _) t
    (h.mono fun i hi y hy=> (Real.le_toNNReal_iff_coe_le (by linarith [hi y hy, NNReal.coe_nonneg (b+b)])).mpr (hi y hy)) he
lemma filterTickPrice_back (Z:Lead.Clan)(b:ℝ≥0)(hb:0<b)(F:ℕ→SampleDose)(p:∀ᶠ i in atTop,(F i).Normalized)
    (a:ℕ→ℝ)(h:∀ᶠ i in atTop,∀ x'∈tsupport (F i).val,↑(b+b) ≤ a i - x' 3) :
    Tendsto (fun i=> ((↑(d i):ℂ)⁻¹) • P.landingCost x (c i) (r i) Z (F i) (a i)) atTop (𝓝 0):=by
  let t(i:ℕ)(y:Vantage):=(a i-y 3).toNNReal
  let f(i:ℕ)(y:Vantage):=P.backwardRay x Z (c i) (r i) (a i) y
  have he(i y): ‖f i y‖= ‖(T).E (t i y) (ψ i Z)‖:= by
    exact (congrArg (fun U:(P.ManyF 3 ξ).Op => ‖U ((T).E (t i y) (ψ i Z))‖) (P.uses_cart 3 ξ y)).trans ((T).unitary ..)
  exact wrists T b hb _ (increment_zero B) (fun i=>P.increment_pos (c i) (r i) (B.launch.unitSize i)) _ _
    (cloud_escape B Z b hb) (fun _=> P.filtered_explicit ..) F p f (fun i=> P.cold_cont x _ _ _ _) t
    (h.mono fun i hi y hy=> (Real.le_toNNReal_iff_coe_le (by linarith [hi y hy, NNReal.coe_nonneg (b+b)])).mpr (hi y hy)) he

-- Also complex normalization (family and height dependent, can depend on test choice),
-- for any rule satisfying this BOUND. No bound imposed on the selected limiting densities.
def UpToTick (P:Spine)(s n:ℕ→ℕ)(z:ℕ→ℂ) : Prop :=
  ∃ D:ℝ, ∀ᶠ i in atTop, ‖z i * (P.increment (s i) (n i):ℂ)‖ ≤ D

omit B
private lemma expand_tick {H : Hilbert}(x:ℕ→H)(tick:ℕ→ℝ≥0)(ht:∀ i,0<tick i)
    (p:Tendsto (fun i=> ((tick i:ℂ)⁻¹) • x i) atTop (𝓝 0)) (z:ℕ→ℂ)
    (h:∃ D:ℝ,∀ᶠ i in atTop, ‖z i*(tick i:ℂ)‖ ≤ D): Tendsto (fun i=> z i • x i) atTop (𝓝 0):=by
  let y(i):=((tick i:ℂ)⁻¹ • x i)
  have he(i): z i • x i=(z i*(tick i:ℂ)) • y i:=by
    unfold y; rw [smul_smul,mul_assoc,mul_inv_cancel₀,mul_one]
    exact Complex.ofReal_ne_zero.mpr (show (tick i:ℝ)≠0 from (NNReal.coe_pos.mpr (ht i)).ne')
  obtain ⟨D,hD⟩:=h
  have v:Tendsto (fun i=>D*‖y i‖) atTop (𝓝 0):= by simpa [y] using p.norm.const_mul D
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (hD.mono fun i u=>?_ ) v
  rw [he,norm_smul]; exact mul_le_mul_of_nonneg_right u (norm_nonneg _)

include B
variable (F G:ℕ→SampleDose)(a:ℕ→ℝ)(b:ℝ≥0)
structure StaysBack : Prop where
  room : 0<b
  normA : ∀ᶠ i in atTop,(F i).Normalized
  normB : ∀ᶠ i in atTop,(G i).Normalized
  first : ∀ᶠ i in atTop,∀ y∈tsupport (F i).val,↑(b+b) ≤ a i-y 3
  second : ∀ᶠ i in atTop,∀ y∈tsupport (G i).val,↑(b+b) ≤ y 3-a i
variable {F G a b}(R: StaysBack F G a b)(Z W:Lead.Clan)
include R
lemma filterPrice (z:ℕ→ℂ)(u:P.UpToTick c r z) :
    Tendsto (fun i=> z i • P.launchCost x (c i) (r i) Z (G i) (a i)) atTop (𝓝 0) :=
  expand_tick (H:=Hc) _ _ (fun i=>P.increment_pos (c i) (r i) (B.launch.unitSize i))
    (filterTickPrice B Z b R.room G R.normB a R.second) z u
lemma filterPrice_back (z:ℕ→ℂ)(u:P.UpToTick c r z) :
    Tendsto (fun i=> z i • P.landingCost x (c i) (r i) Z (F i) (a i)) atTop (𝓝 0) :=
  expand_tick (H:=Hc) _ _ (fun i=>P.increment_pos (c i) (r i) (B.launch.unitSize i))
    (filterTickPrice_back B Z b R.room F R.normA a R.first) z u

omit R B
private lemma multiplies {H:Hilbert} (y v:ℕ→H)(z₀ z₁:ℕ→ℂ)
    (p:Tendsto (fun i=> z₀ i • y i) atTop (𝓝 0))(q:Tendsto (fun i=> z₁ i • v i) atTop (𝓝 0)):
    Tendsto (fun i=> star (z₀ i)*z₁ i*inner ℂ (y i) (v i)) atTop (𝓝 0):= by
  have ht : Tendsto (fun i=> inner ℂ (z₀ i • y i) (z₁ i • v i)) atTop (𝓝 0) := by
    simpa using Tendsto.inner (𝕜:=ℂ) p q
  exact ht.congr fun i=> by rw [inner_smul_left,inner_smul_right,mul_assoc]; rfl

include R B
/-- Loss of interaction price, all six, even permitting inverse-increment order
per body. Need only hold back in axis 3. -/
theorem limitSixLoss (z y:ℕ→Lead.Clan→ℂ)(f:∀ i,P.UpToTick c r (fun k=>z k i))(g:∀ i,P.UpToTick c r (fun k=>y k i)):
    Tendsto (fun k=> Matrix.of fun i j:Lead.Clan=> star (z k i)*y k j*P.arrayReading x (c k) (r k) (a k) (F k) (G k) i j)
      atTop (𝓝 (0:CrossRead)) := tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>
        multiplies (H:=Hc) _ _ _ _ (filterPrice_back B R i _ (f i)) (filterPrice B R j _ (g j))

end Spine
#print axioms Spine.limitSixLoss
#print axioms Spine.cloud_escape
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
