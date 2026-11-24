/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.ActorDense

/-!
# The real time OS transfer by actual Eχ, still missing continuous spatial translations
Check only the hypotheses for **pure time**. Re-use OS.Duration with dummy space (no claim about
 its `U`); supply holomorphic half-plane and commutation with every `roll` actual.
Uses `timeMesh Λ` throughout (in physical level-zero fermion spacing).
Analytic identity on each heat half-plane, no use of a theorem whose hypotheses on actual E
presume relativity. Temporal spectral measures are those of these same heat reads. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set MeshClock
local notation "M"=>timeMesh Λ
namespace Acting
variable (X:Acting Y H V G j strict C)
local notation "ω₀"=>X.ground
local notation "A₀"=>X.space
local notation "S"=>stationC Y H V G j strict C
local notation "Φ"=>X.showL
local notation "Λ₀"=>heatOp Y H V G j strict C
local notation "Μ"=>marks (timeMesh Λ)
local notation "Q"=>clock Y H V G j strict C X
local notation "U"=>lattice Y H V G j strict C X
local notation "γ" s:max=>voice Y H V G j strict C X s

lemma runs_early (s:ℕ)(x : Fₛ s): ∃ i : ℝ≥0,0 < i ∧ ∃ (t:ℕ)(y:Fₛ t),(γ s) x=Q i ((γ t) y) := by
  obtain ⟨i,y,p⟩ := predecessor Y H s G.history.circuit j 0 strict x
  refine ⟨whenly M (s+i) 1,when_pos M _ 1 one_pos,s+i,y,?_⟩
  rw [clock_voice]
  exact (X.climbs Y H V G j strict C s x _ (by omega : s ≤ s+i)).symm.trans (congrArg (γ (s+i)) p.symm)
lemma price_near (x:ℝ≥0) (p:0 < x) : ContinuousAt (Q) x:=
  (show Continuous X.showL from map_continuous _).continuousAt.comp (show ContinuousAt (Λ₀) x from
    (tendsto_subtype_rng.mpr (norm_cont_heat Y H V G j strict C x p)))
lemma price_every (v:A₀): Continuous (fun t :ℝ≥0=> Q t v) := by
  let Pτ(t:ℝ≥0)(v:A₀):= Q t v
  -- only 0 missing, use for all.
  have he{w:A₀}(h:w∈ citizens Y H V G j strict C X): Continuous (fun t=> Pτ t w) := by
    obtain ⟨s,x⟩:= mem_iUnion.mp h; obtain ⟨y,rfl⟩:=x; obtain ⟨i,h,t,W,q⟩:= runs_early Y H V G j strict C X s y
    rw [q]; apply continuous_iff_continuousAt.mpr; intro v
    let y:=(γ t) W
    have h': ContinuousAt (fun w=>Q (w+i) y) v:= ContinuousAt.clm_apply ((X.price_near Y H V G j strict C _ (add_pos_of_nonneg_of_pos v.property h)).comp (f:=fun a:ℝ≥0=>a+i) (continuousAt_id.add continuousAt_const)) continuousAt_const
    have hh(z): Pτ z (Q i y)=Q (z+i) y:=by rw [clock_sum]; rfl
    change ContinuousAt (fun t=>Pτ t (Q i y)) v
    simp_rw [hh]; exact h'
  refine continuous_iff_continuousAt.mpr fun a=> Metric.tendsto_nhds.mpr fun ε hp=> ?_
  let q:= ε/4; have hq:0<q:=div_pos hp (by norm_num)
  obtain ⟨y,h,t⟩:= Metric.mem_closure_iff.mp (X.densely Y H V G j strict C v) q hq
  have hw(a:ℝ≥0):dist (Pτ a v) (Pτ a y)<q:=by
    unfold Pτ; rw [dist_eq_norm,←map_sub]; exact (le_trans ((Q a).le_opNorm _) (mul_le_of_le_one_left (norm_nonneg _) (clock_law ..))).trans_lt (by rwa [dist_eq_norm] at t)
  filter_upwards [Metric.tendsto_nhds.mp (show ContinuousAt (fun z=>Pτ z y) a from (he h).continuousAt) q hq] with z hz
  apply lt_of_le_of_lt (show dist (Pτ z v) (Pτ a v) ≤ dist (Pτ z v) (Pτ z y) + (dist (Pτ z y) (Pτ a y) + dist (Pτ a y) (Pτ a v)) from
    (dist_triangle ..).trans (by gcongr; apply dist_triangle))
  have ht:=hw z; have hf:=hw a; rw [dist_comm (Pτ a v)] at hf; unfold q at *; linarith

private noncomputable def temp : YM.OS.Semigroup X.space j where
  E := Q
  eZero:= clock_zero ..
  time t v:= clock_sum ..
  shrinks t:= clock_law ..
  sym t:= clock_symm ..
  «U» _:=ContinuousLinearMap.id ℂ _
  uZero:= rfl
  space _ _:=rfl
  unitary _ _:=rfl
  independent _ _:=rfl
  continuousE := price_every Y H V G j strict C X
  continuousU _:=continuous_const

open OS.Semigroup Spectral Boundary Probe Complex
local notation "I'"=> Complex.I
-- general analytic identity on right half plane
private theorem from_pos {B₀: Type} [NormedAddCommGroup B₀] [NormedSpace ℂ B₀]
    {f g:ℂ→ B₀}(p:AnalyticOnNhd ℂ f OS.Semigroup.inside)(q:AnalyticOnNhd ℂ g OS.Semigroup.inside)
    (h:∀ i:ℝ≥0,0 < i → f (duration i) = g (duration i)): EqOn f g OS.Semigroup.inside:= by
  refine p.eqOn_of_preconnected_of_frequently_eq q (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0 |>.isPreconnected) (z₀:=duration 1) (dur.mpr zero_lt_one) (fun hn=>?_)
  have ht:Tendsto duration (𝓝[>] (1:ℝ≥0)) (𝓝[≠] duration 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with i hi; change ¬duration i= _; intro h; exact (mem_Ioi.mp hi).ne' (Subtype.ext (Complex.ofReal_injective h))
  obtain ⟨i,u,v⟩ := ((ht.eventually hn).and self_mem_nhdsWithin).exists
  exact u (h i (zero_lt_one.trans (mem_Ioi.mp v)))

local notation "Z"=>temp Y H V G j strict C X
noncomputable def unitaryTime (i:ℝ):= (Z).edge i
local notation "J"=> unitaryTime Y H V G j strict C X
noncomputable def halfSpaceFunction(z:ℂ):=(Z).F (-Complex.I*z)
local notation "F₀"=>halfSpaceFunction Y H V G j strict C X
local notation "F"=>(Z).F
lemma unitary_time_zero : J 0=1 := (Z).birth
lemma norm_time (t:ℝ) (x:X.space) : ‖J t x‖=‖x‖:= (Z).life t x
lemma unitary_time_comm (t u:ℝ) : J (t+u) = J t * J u := (Z).send t u |>.symm
lemma unitary_time_cont (v:A₀) : Continuous (fun t:ℝ=> J t v) := (Z).cont v
lemma linker_analytic : AnalyticOnNhd ℂ (F₀) {x:ℂ|0<x.im}:=by
 intro t v; apply (((Z).localHeat _ (show -I'*t∈inside from by change 0 < (-Complex.I*t).re; simpa using (show 0<t.im from v))).comp (analyticAt_const.mul analyticAt_id))
lemma linker_at {t :ℝ≥0}(p:0<t): F₀ ((t:ℝ)*I' :ℂ)= Q t:=by
 unfold halfSpaceFunction
 rw [show -Complex.I* ((t:ℝ)*Complex.I :ℂ)= duration t from by simp [duration,mul_comm _ Complex.I,←mul_assoc]]
 exact (Z).roots_heat p
lemma linked {t:ℝ≥0} (p:0<t)(v:ℝ): F₀ ((v:ℂ)+ (t:ℝ)*I') = (J v)*(Q t):= by
 unfold halfSpaceFunction; rw [show -Complex.I*((v:ℂ)+(t:ℝ)*I')=duration t+sideways v from (by apply Complex.ext <;> simp [duration,sideways])]
 rw [←OS.Semigroup.along (Z) (OS.Semigroup.dur.mpr p) v, OS.Semigroup.roots_heat (Z) p]; rfl
lemma commute_heat (a:Trans j)(i:Μ) : ∀ z∈inside, Commute ((F z)) (U a i) := by
  refine from_pos (f:=fun z=> ((F z)).comp (U a i)) (g:=fun z=> (U a i).comp ((F z))) ?_ ?_ ?_
  · exact (Z).localHeat.mul analyticOnNhd_const -- multiplication defeq? mathlib .mul
  · exact analyticOnNhd_const.mul (Z).localHeat
  intro c h; rw [(Z).roots_heat h]; exact (X.roll_clock Y H V G j strict C a i c).symm
lemma warm_vac : ∀ z∈inside,(F z) ω₀=ω₀ := by
  refine from_pos (p:=fun z hz=> (ContinuousLinearMap.apply ℂ X.space.space ω₀).analyticAt _ |>.comp ((Z).localHeat z hz)) (g:=fun _=> ω₀) analyticOnNhd_const ?_ -- tune f
  intro t h; rw [(Z).roots_heat h]; exact vacuum_time ..
lemma mink_vac (a:ℝ): J a ω₀=ω₀:= by
  calc _= (Z).edge a ((Z).E 1 ω₀) := congrArg (J a) (X.vacuum_time Y H V G j strict C 1).symm
       _= ω₀ := ((Z).high a _).trans (warm_vac Y H V G j strict C X _ (length.mpr zero_lt_one)) -- length ambiguous
lemma spacetime_lattice (t:ℝ)(a:Trans j)(i:Μ): Commute (J t) (U a i) := by
  change (J t).comp (U a i)= (U a i).comp (J t)
  apply DFunLike.coe_injective; apply ((Z).whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext v
  change J t (U a i ( (Z).E 1 v))= U a i ((Z).edge t ((Z).E 1 v))
  rw [(Z).high t v, show U a i ((Z).E 1 v)=(Z).E 1 (U a i v) from congrArg (fun f:X.space.Op=> f v) (roll_clock Y H V G j strict C X a i 1).eq,
    show J t ((Z).E 1 (U a i v))= _ from (Z).high t _]
  exact congrArg (fun f:X.space.Op=>f v) (commute_heat Y H V G j strict C X a i _ (length.mpr zero_lt_one)).eq

noncomputable def pvM (v:A₀): Measure ℝ:= ((Z).ℚmeasure.diagonal v).map (fun y:E4 => y j)
local notation "µ" v:max=>pvM Y H V G j strict C X v
instance billE_finite (v:A₀):IsFiniteMeasure (µ v):=by unfold pvM; infer_instance
lemma billE_positive (v:A₀): ∀ᵐ t:ℝ ∂(µ v),0 ≤ t:=by
 have h:Measurable (fun i:E4=>i j):=by fun_prop
 exact (ae_map_iff h.aemeasurable (measurableSet_le measurable_const measurable_id)).2 ((Z).bright v)

lemma billE_char (t:ℝ)(v:A₀): inner ℂ v ((J t) v) = ∫ r:ℝ, Complex.exp ((r:ℂ)* (t:ℂ)*Complex.I) ∂(µ v):=by
 let m:=(Z).ℚmeasure.diagonal v; let e(x:E4):ℝ:=x j
 have he:Measurable e:= by unfold e; fun_prop
 rw [pvM,integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* (t:ℂ)*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*(t:ℂ)*Complex.I))).aestronglyMeasurable)]
 have ht:=(Z).assigned v t 0
 change (Z).J 0 v v (t:ℂ)=_ at ht
 simpa [OS.Semigroup.J,OS.Semigroup.ray,(Z).eZero,(Z).unit.origin,Probe.plane,unitaryTime,e] using ht
end Acting
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.temp -- private print?
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.billE_char
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.linker_analytic
