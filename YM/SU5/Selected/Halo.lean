import YM.SU5.Selected.Loewner
import YM.Heat.Duration
/-!
# Heat and halo in a phase C* algebra

Port one prepared (ambient) Semigroup through ANY unital C* representation
using strictly positive times and mesh-supported approximants. Exposes steps:
- Full interior analytically available in the *Cstar algebra*, same norm etc as ambient
- Agreement with reconstructed continuations in representation (survive compact expansions)
- Mink motion, its commuting endomorphisms from Euclidean, and invariant vectors
- Positive-energy measure with tested conventions. 

No use at all of the space-translations of the `OS.Semigroup` used to construct F and edge,
beyond that these protocols have reference to them. Claims here not asking for an `OS.Table` etc.
Credits: use Heat.Extend / Imaginary for (even proofs borrowed for) the invariant criterion.
One-dimensional spectral proofs transported from base `Tower.TimeKeeper`, proofs below local to this setting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Topology Metric Finset Complex MeasureTheory OS OS.Semigroup
open scoped Topology CStarAlgebra NNReal ENNReal Classical ComplexOrder InnerProductSpace

variable {A H : Hilbert} {j : Axis} (S : OS.Semigroup H j)
lemma norm_cont_area {t : ℝ≥0} (p : 0<t) : ContinuousAt S.E t := by
  have he : duration t∈inside := dur.mpr p
  refine ContinuousAt.congr ?_ (show (S.F ∘ duration) =ᶠ[𝓝 t] S.E from ?_) -- direction
  · exact (S.localHeat _ he).continuousAt.comp (continuous_ofReal.comp continuous_subtype_val).continuousAt
  exact ((lt_mem_nhds p).mono fun i v => (S.roots_heat v))

variable (B : StarSubalgebra ℂ H.Op) [IsClosed (B : Set H.Op)] (ρ : B →⋆ₐ[ℂ] A.Op)
lemma heat_complete {M : Set ℝ≥0} (p : Dense M) (v : ∀ z∈M,S.E z∈B) (t : ℝ≥0) : S.E t∈B := by
  by_cases hp : t=0; · rw [hp,S.eZero]; exact B.one_mem
  haveI : NeBot (𝓝[M] t) := mem_closure_iff_nhdsWithin_neBot.mp (p t)
  exact IsClosed.mem_of_tendsto (b:=𝓝[M] t) (by infer_instance)
    ((norm_cont_area S (pos_iff_ne_zero.mpr hp)).tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with i vi; exact v i vi) -- local nebot add
variable (hS : ∀ t,S.E t∈ B)

/-- Strict-positive heat can live in any algebra B with these payments; take full powers, not
statements only wrt a scalar measure. -/
def lamp (t : ℝ≥0) : B := ⟨S.E t,hS t⟩
local instance : ContinuousFunctionalCalculus ℂ (↥B) IsStarNormal := IsStarNormal.instContinuousFunctionalCalculus
def halo (z : ℂ) : B := cfc (fun x : ℂ => x^z) (lamp S B hS 1)
private lemma halo_power {z : ℂ} (h : z∈inside) : ContinuousOn (fun x : ℂ => x^z) (spectrum ℂ (S.E 1)) := by
  apply continuousOn_iff_continuous_restrict.mpr
  exact (S.adopt 1 z h).continuous
lemma halo_formed {z : ℂ} (h : z∈inside) : S.F z = cfc (fun x : ℂ => x^z) (S.E 1) := by
  rw [cfc_apply _ _ (S.stare 1).isStarNormal (halo_power S h)]; unfold F
  rw [roots,dif_pos h]; rfl
lemma lamp_herm (t) : IsSelfAdjoint (lamp S B hS t) := Subtype.ext (S.sym t)
lemma halo_val (z : ℂ) (p : z∈inside) : (halo S B hS z).val=S.F z := by
  rw [halo_formed S p]; unfold halo
  exact B.subtype.map_cfc (fun x : ℂ => x^z) (lamp S B hS 1) ((B.spectrum_eq (a:=lamp S B hS 1)).symm ▸ halo_power S p) (map_continuous _) (lamp_herm S B hS _).isStarNormal (S.stare 1).isStarNormal

private lemma μpower (f : ℝ≥0 → A.Op) (h : ∀ t,‖f t‖ ≤ 1) (p : Dense (⋃ t∈ Set.Ioi (0:ℝ≥0), Set.range (f t)))
    (e : ∀ t∈ Set.Ioi (0:ℝ≥0),ContinuousAt f t)
    (t : ∀ u v, f u * f v=f (u+v)) (x : A) : Continuous (fun z=> f z x) := by
  have hq (x y:A) (t : ℝ≥0) : dist (f t x) (f t y) ≤ dist x y := by
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((f t).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (h t))
  refine continuous_iff_continuousAt.mpr (fun i => Metric.tendsto_nhds.mpr (fun ε d => ?_)); classical
  obtain ⟨y,m,k⟩ := Metric.mem_closure_iff.mp (p x) (ε/3) (by positivity)
  obtain ⟨u,q⟩ := mem_iUnion.mp m; obtain ⟨b,z⟩ := Set.mem_iUnion.mp q; obtain ⟨v,rfl⟩ := z
  let F (i) := f i (f u v)
  have Hh : Continuous F := by
    simp_rw [F,←ContinuousLinearMap.mul_apply,t]
    refine (ContinuousLinearMap.apply ℂ A v).continuous.comp <|
      continuous_iff_continuousAt.mpr (fun x:ℝ≥0 => ?_)
    change ContinuousAt (fun x:ℝ≥0=> f (x+u)) x
    exact (e _ (lt_of_lt_of_le (show 0<u from b) (le_add_self ..))).comp (f:=fun z:ℝ≥0 => z+u) (continuous_id.add continuous_const).continuousAt
  filter_upwards [Metric.tendsto_nhds.mp (Hh.tendsto i) (ε/3) (by positivity)] with s q
  apply lt_of_le_of_lt (dist_triangle (f s x) (F s) (f i x))
  have he := dist_triangle (F s) (F i) (f i x); have h1 := hq x (f u v) s; have h2 := hq x (f u v) i; rw [dist_comm] at h2
  change dist (f s x) (F s) ≤ _ at h1; change dist (F i) (f i x) ≤ _ at h2; linarith

def Warm (H' : Hilbert) (f : ℝ≥0 → H'.Op) : Prop := Dense (⋃ t∈ Set.Ioi (0:ℝ≥0), range (f t))
local notation "E₁" => fun t : ℝ≥0 => ρ (lamp S B hS t) -- quotPrecheck?
set_option quotPrecheck false
lemma lamp_add (a b : ℝ≥0) : lamp S B hS a * lamp S B hS b = lamp S B hS (a+b) := Subtype.ext (S.time ..).symm
lemma lamp_birth : lamp S B hS 0=1 := Subtype.ext S.eZero
lemma lamp_small (t : ℝ≥0) : ‖(E₁) t‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le ρ _).trans (S.shrinks t)
lemma lamp_cont {t : ℝ≥0} (p : 0 < t) : ContinuousAt (lamp S B hS) t := tendsto_subtype_rng.mpr (norm_cont_area S p)
variable (h : Warm A (fun t => ρ (lamp S B hS t)))

/-- Buying Strong Continuity still requires `Warm` in each representation. No continuity from op
norm at t=0 available. Norm holomorphy refrained to S only. Pass otherwise atomistically.
NOTE spectator 'space' from base Semigroup REMOVED, U x here trivial. -/
def pecos : OS.Semigroup A j where
  E t := ρ (lamp S B hS t)
  U _ := ContinuousLinearMap.id ℂ _
  eZero := by rw [lamp_birth,map_one]; rfl
  time a b := by rw [←lamp_add,map_mul]; rfl
  shrinks := lamp_small S B ρ _
  sym t := by
    change star (ρ (lamp S B hS t))=_; rw [← map_star ρ] -- tune
    rw [lamp_herm S B hS t]
  uZero := rfl
  space _ _:=rfl
  independent _ _:=rfl
  unitary _ _:=rfl
  continuousE v := μpower _ (lamp_small S B ρ hS) h
    (fun t p => (map_continuous ρ).continuousAt.comp (lamp_cont S B hS p))
    (fun a b => by rw [← map_mul,lamp_add]) v
  continuousU _:=continuous_const
local notation "P" => pecos S B ρ hS h
lemma pecos_F {z : ℂ} (u : z∈inside) : (P).F z=ρ (halo S B hS z) := by
  rw [halo_formed _ u]; unfold halo; symm
  exact ρ.map_cfc (fun x : ℂ => x^z) (lamp S B hS 1) ((B.spectrum_eq (a:=lamp S B hS 1)).symm ▸ halo_power S u) (map_continuous _) (lamp_herm S B hS _).isStarNormal ((P).stare 1).isStarNormal

section lines
private lemma regular_zero {f : ℂ → H} (h : AnalyticOnNhd ℂ f inside)
    {a : ℝ → ℂ} (v : Continuous a) (hv : a 0∈inside) (hr : ∀ t> (0:ℝ), a t ≠ a 0) (k : ∀ t> (0:ℝ), f (a t)=0) : ∀ z∈ inside,f z=0 := by
  refine h.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0 |>.isPreconnected) hv ?_ -- check defeq EqOn
  intro hN
  have hz : Tendsto a (𝓝[>] (0:ℝ)) (𝓝[≠] (a 0)) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((v.tendsto 0).mono_left nhdsWithin_le_nhds) (by filter_upwards [self_mem_nhdsWithin] with i q; exact (hr i q))
  obtain ⟨i,b,h'⟩ := ((hz.eventually hN).and self_mem_nhdsWithin).exists
  exact b (k i h')
lemma lamp_fixed (x : H) : (∀ t : ℝ, S.edge t x=x) ↔ (∀ t : ℝ≥0,S.E t x=x) := by
  let F (x : H) z := S.F z x
  let w := duration 1
  have hw : 0 < (1:ℝ≥0) := by norm_num
  have h (u v : H) : AnalyticOnNhd ℂ (fun z => F u z-v) inside := fun a h => (((ContinuousLinearMap.apply ℂ H.space u).analyticAt _).comp (S.localHeat a h)).sub analyticAt_const
  constructor
  · intro p
    let a (t : ℝ) := w + sideways t
    have ha : Continuous a := continuous_const.add ((continuous_ofReal.neg).mul continuous_const)
    have hk (t : ℝ) (_ : t>0) : F x (a t)-F x w=0 := by
      unfold F a; rw [← S.either (dur.mpr hw) t, ContinuousLinearMap.comp_apply,p,sub_self]
    have h' (t : ℝ) (h : t>0) : a t≠a 0 := fun hz => by
      have e := congrArg Complex.im (add_left_cancel hz : sideways t=sideways 0); simp [sideways] at e; linarith
    have hz := regular_zero (h x (F x w)) ha (length.mpr hw) h' hk
    have hy (t : ℝ≥0) (ht : t>0) : S.E t x=F x w := by
      rw [←S.roots_heat ht]; exact sub_eq_zero.mp (hz _ (dur.mpr ht))
    have ht : x=F x w := tendsto_nhds_unique
      (f:=fun t : ℝ≥0 => S.E t x)
      (l:=𝓝[>] (0:ℝ≥0)) (by simpa [S.eZero] using (((S.continuousE x).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)) ))
        (tendsto_const_nhds.congr' (by filter_upwards [self_mem_nhdsWithin] with i e; exact (hy i e).symm)) -- argument name
    intro t; rcases eq_or_lt_of_le (show 0≤ t from by positivity) with h|p
    · rw [←h,S.eZero]; rfl
    exact (hy t p).trans ht.symm
  intro p t
  let a (t : ℝ) := (t:ℂ)+w
  have hu : Continuous a := continuous_ofReal.add continuous_const
  have hr : a 0∈inside := by simpa [a] using (show w∈inside from dur.mpr hw)
  have hy (z : ℝ) (v : z>0) : a z≠a 0 := fun q => ne_of_gt v (ofReal_injective (add_right_cancel q))
  have hz (z : ℝ) (v : z>0) : F x (a z)-x=0 := by
    let u : ℝ≥0 := ⟨z,v.le⟩; unfold F; rw [show a z=duration (u+1) from ?_,S.roots_heat (show 0<u+1 by positivity),p,sub_self]
    simp [a,u,duration,w]; rfl
  rw [show S.edge t x=S.F (w+sideways t) x from by
    conv_lhs => rhs; rw [←p 1]
    exact S.high ..]
  exact sub_eq_zero.mp (regular_zero (h x x) hu hr hy hz _ (length.mpr hw))
end lines

lemma commutes_lamp {T : H.Op} (q : Commute (S.E 1) T) (z : ℂ) : Commute (S.F z) T :=
  (S.stare 1).commute_cfcHom (S.stare 1).isStarNormal q (S.roots z)
lemma lamp_orbit {T : H.Op} (q : Commute (S.E 1) T) (t : ℝ) : Commute (S.edge t) T := by
  apply DFunLike.coe_injective (F:= (H).Op)
  apply (S.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext v
  change (S.edge t) (T (S.E 1 v))=T ((S.edge t) (S.E 1 v))
  rw [← ContinuousLinearMap.mul_apply T _ v,←q.eq, ContinuousLinearMap.mul_apply, S.high,S.high, ←ContinuousLinearMap.mul_apply,(commutes_lamp S q _).eq]
  rfl

section bill
open Spectral Boundary Probe
noncomputable def roadMeasure (v : H) : Measure ℝ := (S.ℚmeasure.diagonal v).map (fun x : E4 => x j)
local notation "L" v:max => roadMeasure S v
instance roadFinite (v : H) : IsFiniteMeasure (roadMeasure S v) := by unfold roadMeasure; infer_instance
lemma roadLight (v : H) : ∀ᵐ r : ℝ ∂(L v), 0 ≤ r :=
  (ae_map_iff (show Measurable (fun x : E4 => x j) from (by fun_prop)).aemeasurable (measurableSet_le measurable_const measurable_id)).2 (S.bright v)
lemma roadEngine (v : H) (t : ℝ) : inner ℂ v (S.edge t v) = ∫ r : ℝ, Complex.exp ((r:ℂ)*(t:ℂ)*Complex.I) ∂(L v) := by
  -- need S.U? S.uZero
  let e(x:E4) : ℝ:=x j
  have he:Measurable e:=by unfold e; fun_prop
  rw [roadMeasure,integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* (t:ℂ)*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*(t:ℂ)*Complex.I))).aestronglyMeasurable)]
  have ht := S.assigned v t 0
  change S.J 0 v v (t:ℂ)=_ at ht
  simpa [OS.Semigroup.J,OS.Semigroup.ray,S.eZero,S.unit.origin,Probe.plane,e] using ht
lemma roadBill (v : H) (t : ℂ) (h : 0<t.im) : inner ℂ v (S.F (-Complex.I*t) v) = ∫ r:ℝ, Complex.exp ((r:ℂ)*t*Complex.I) ∂(L v) := by
  let e(x:E4):ℝ:=x j
  have he:Measurable e:= by unfold e; fun_prop
  rw [roadMeasure,integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* t*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*t*Complex.I))).aestronglyMeasurable)]
  have ht:=S.heat 0 v (z:=t) (show t∈_ from h.le)
  rw [OS.Semigroup.J, S.lift_ray v h] at ht
  simpa [S.unit.origin,Probe.plane,e] using ht
end bill
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.pecos_F
#print axioms YM.SelectionAnalysis.lamp_orbit
#print axioms YM.SelectionAnalysis.lamp_fixed
#print axioms YM.SelectionAnalysis.roadEngine
