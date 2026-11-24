/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.LineUp.Slope
import YM.Work.C09
import YM.Work.C08
-- C09 adaptation. Ward purchases -> all boost, spatial.
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.WView
open Bid Boundary Mink Mink.Poincare Table Analysis Filter Function MeasureTheory Set Complex
open scoped Topology NNReal BigOperators ContDiff
open Work.C09 (time_compare motion_push push_one push_mul spatialMap move_position)
open HelioRoof
variable {V:Type*} [AddCommGroup V][Module ℂ V]{W:WView V}{Y:InkWaves V}{R:Courts V}{n:ℕ}
theorem restricted_spatial (hori : R.Carriage Y) (he : Y.Region) (v : Fin n → V)
    (x : Points n) (r : Ortho) (hr : Lorentz.spatialTurn r) {y : Heights n} (hy : y∈east n) :
    Y.restricted (R.eu r ∘ v) y ((motion (Lorentz.room r hr)).zusammen n x) =
      Y.restricted v y x := by
  let z := shift x y
  have hz : z ∈ strict n := by
    simpa [z] using on_profile x y 1 (by norm_num) hy
  let p := trace x
  let p' : SpacePoints n := spatialMap r ∘ p
  let t := (motion (Lorentz.room r hr)).zusammen n x
  have heq i : t i = r.move (x i) := by
    simp only [t,zusammen,points,WithLp.ofLp_toLp,as_active]; rfl
  have hpp (i) : t i = position (p' i) (YM.time (x i)) := by
    change t i = position (spatialMap r (p i)) _
    rw [heq, ← move_position r hr (p i)]; simp [p,trace]
  have hs : trace t = p' := by funext i; simp [trace,hpp]
  have ht : shift t y = z := by
    funext i; simp only [z,shift]; rw [show YM.time (t i)=YM.time (x i) by rw [hpp,time_position]]
  let v' := R.eu r ∘ v
  have hg (u : Heights n) : place p' u = Points.move r (place p u) := by
    ext1 i; exact (move_position r hr _ _).symm
  change Y.F n (shift t y) (trace t) v' = Y.F n z p v
  rw [ht,hs]
  have hj (u : Heights n) (hu : u∈east n) (b : ℝ) :
      Y.F n (fun i => (↑(u i+b*0):ℂ)*I) p' v' = Y.F n (fun i => (↑(u i):ℂ)*I) p v := by
    have hW : place p u∈ Wheeled n ∧ place p' u ∈ Wheeled n:=by simp [Wheeled,-line_at,hu]; -- tune
    simp only [mul_zero, add_zero]; have ht:= wheeled_eq hori he (place p u) hW.1 (r,1) (show fairFrame (r,(1:Equiv.Perm (Fin n))) from hr.1) (show reFrame (r,1) (place p u) ∈ Wheeled n from (show Points.move r (place p u)∈ Wheeled n from hg u ▸ hW.2)) v
    rw [show reFrame (r,1) (place p u)=place p' u from (hg u).symm,show reSup (r,1) R v=v' from rfl, InkWaves.entrance,InkWaves.entrance] at ht
    simpa only [line_place', trace_place'] using ht
  simpa using time_compare (fun u => Y.F n u p' v') (fun u => Y.F n u p v)
    (he.hol _ _ _) (he.hol _ _ _) 0 hj z hz

/-- Transfer point covariance with unchanged strict heights to W. Here used
for spatial rotations and all real translations; not assuming such a
strict-height covariance for boosts. -/
theorem corner_maps (hw : Y.NonTangentialFree W) (p : Poincare) (v u : Fin n → V)
    (h : ∀ x y, y∈east n → Y.restricted u y (p.zusammen n x) = Y.restricted v y x)
    (f : Joint n) : W.W n u (Joint.gpush n p f) = W.W n v f := by
  have he (p : Poincare) : LeftInverse (p⁻¹.zusammen n) (p.zusammen n) := by
    intro x; ext1 i; exact p.unmade (x i)
  let e : Points n ≃ᵐ Points n := {
    toFun := p.zusammen n
    invFun := p⁻¹.zusammen n
    left_inv := he p
    right_inv := by simpa only [Function.RightInverse,inv_inv] using he p⁻¹
    measurable_toFun := (p.together n).measurable
    measurable_invFun := (p⁻¹.together n).measurable }
  let f' := Joint.gpush n p f
  have hp (y : Heights n) (hy : y∈east n) : Y.psi u y f' = Y.psi v y f := by
    unfold InkWaves.psi
    rw [← (p.together n).integral_comp e.measurableEmbedding]
    simp_rw [h _ _ hy, f', Joint.gpush_at, he p _]
  haveI := awaits (light n)
  have hf : Tendsto (fun y => Y.psi u y f') (𝓝[east n] 0) (𝓝 (W.W n u f')) := hw.corner ..
  refine tendsto_nhds_unique hf ?_
  have hg : Tendsto (fun y => Y.psi v y f) (𝓝[east n] 0) (𝓝 (W.W n v f)) := hw.corner ..
  exact hg.congr' <| Eventually.mono self_mem_nhdsWithin fun x hx => (hp x hx).symm

/-- Boost identity passes to the boundary. We only need corner convergence
on fixed tests, including the extra tests appearing with a coefficient that
vanishes with the ordered height. -/
theorem boost_corner (hb : InkBoost Y R) (hw : Y.NonTangentialFree W)
    (v : Fin n → V) (a : SpaceAxis) (f : Joint n) :
    (∑ i, W.W n (Cosm R a v i) f) = W.W n v (inclined a 0 f) := by
  let F := 𝓝[east n] (0:Heights n)
  haveI : F.NeBot := awaits (light n)
  let u := v
  have he (w : Fin n → V) (g : Joint n) : Tendsto (fun y => Y.psi w y g) F (𝓝 (W.W n w g)) := hw.corner ..
  let l := fun (i : Fin n) => realTerm i a.castSucc f
  let c := fun (i : Fin n) (y : Heights n) => (y i : ℂ)*I
  have hc (y : Heights n) : inclined a y f = inclined a 0 f + ∑ i, c i y • l i := by
    simp [inclined,c,l,Finset.sum_add_distrib]
  let P (y : Heights n) (hy : y∈east n) : Joint n →ₗ[ℂ] ℂ := {
    toFun := Y.psi u y
    map_add' g j := by
      unfold InkWaves.psi
      rw [← integral_add (hw.int n u y hy g) (hw.int n u y hy j)]
      apply integral_congr_ae; filter_upwards with x; simp [mul_add]
    map_smul' z g := by
      change Y.psi u y (z • g) = z * Y.psi u y g
      unfold InkWaves.psi; rw [← integral_const_mul]; congr! 1; ext x; simp; ring }
  have hh (y) (hy : y∈east n) : Y.psi u y (inclined a y f) = Y.psi u y (inclined a 0 f) +
      ∑ i, c i y * Y.psi u y (l i) := by
    rw [hc y]
    change P y hy _ = P y hy _ + ∑ i, c i y • (P y hy) (l i)
    simp only [map_add,map_sum,map_smul]
  have hz (i : Fin n) : Tendsto (fun y => c i y * Y.psi u y (l i)) F (𝓝 0) := by
    have hp : Continuous (c i) := by unfold c; fun_prop
    have ht := ((hp.tendsto 0).mono_left (nhdsWithin_le_nhds (s:= east n))).mul (he u (l i))
    simpa only [c,Pi.zero_apply,ofReal_zero,zero_mul] using ht
  have hs : Tendsto (fun y => ∑ i, c i y * Y.psi u y (l i)) F (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hz i)
  let w := fun i => Cosm R a v i
  refine tendsto_nhds_unique (tendsto_finsetSum Finset.univ (fun i _ => he (w i) f)) ?_
  have ht := (he u (inclined a 0 f)).add hs
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s:=east n)] with y hy
  exact (hh y hy).symm.trans (hb n v a f y hy).symm


def ride (W:WView V)(R:Courts V)(a:SpaceAxis)(v:Fin n→V)(f:Joint n)(t:ℝ):= W.W n (fun i=> R.mi ((Ray.fromAxis a).boost t) (v i)) (Joint.gpush n (motion ((Ray.fromAxis a).boost t)) f)
def askM (W:WView V)(f:Joint n): MultilinearMap ℂ (fun _ :Fin n=>V) ℂ := -- linear dependence on f from dist
  let h : Distn (Points n)→ₗ[ℂ] ℂ := { toFun:=fun p=>p f, map_add':=fun _ _=>rfl, map_smul':=fun _ _=>rfl }; h.compMultilinearMap (W.W n)
theorem boost_origin (hpush : C08)
    (hb : InkBoost Y R) (hw : Y.NonTangentialFree W)
    (v : Fin n → V) (f : Joint n) (a : SpaceAxis) :
    HasDerivAt (ride W R a v f) 0 (0:ℝ) := by
  classical
  let M:= W.W n
  let b := Ray.fromAxis a
  let l (t : ℝ) := fun i => R.mi (b.boost t) (v i)
  let l' : Fin n → V := fun i => (-I) • R.planeDuty a (v i)
  let g (t) := Joint.gpush n (motion (b.boost t)) f
  have hg : g 0=f := by rw [show g 0 = Joint.gpush n 1 f by simp [g],push_one]
  let g' := -inclined a 0 f
  have hg' (w) : HasDerivAt (fun t => M w (g t)) (M w g') (0:ℝ) := by
    let D := (M w).restrictScalars ℝ
    change HasDerivAt (fun t => D (g t)) (D g') 0
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have ht : Tendsto (fun t : ℝ => t⁻¹ • (g t - f)) (𝓝[≠] 0) (𝓝 g') := hpush.2 n f a
    have hs := (D.continuous.tendsto _).comp ht
    simpa only [Function.comp_def,map_smul,map_sub,zero_add,hg] using hs
  let D(t:ℝ):MultilinearMap ℂ (fun _:Fin n=> V) ℂ:= askM W (g t); let D':= askM W g'; have hv: l 0=v:=by ext1 i; unfold l; rw [b.boost_start,R.mi1]
  have H:= GearDeriv.purchase D D' l l' (fun i=> hg' i) (fun i=> R.miD a (v i)); rw [hv] at H
  change HasDerivAt (ride W R a v f) ((∑ i,W.W n (Cosm R a v i) (g 0))+W.W n v (-inclined a 0 f)) (0:ℝ) at H
  rw [hg, boost_corner hb hw, map_neg,add_neg_cancel] at H; exact H
theorem boost_invariant (hpush : C08)
    (hb : InkBoost Y R) (hw : Y.NonTangentialFree W)
    (v : Fin n → V) (f : Joint n) (a : SpaceAxis) :
    ∀ r : ℝ, ride W R a v f r = W.W n v f := by
  let p := ride W R a v f
  have hp (t : ℝ) : HasDerivAt p 0 t := by
    let b := Ray.fromAxis a
    let v' : Fin n → V := fun i => R.mi (b.boost t) (v i)
    let g := Joint.gpush n (motion (b.boost t)) f
    let q := ride W R a v' g
    have he (s : ℝ) : p (t+s) = q s := by
      unfold p q ride
      rw [add_comm t s,b.boost_add,overL,push_mul]
      simp_rw [R.miMul]; rfl
    have ht : p t=q 0 := by simpa using he 0
    have hq : HasDerivAt q 0 0 := boost_origin hpush hb hw v' g a
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simp_rw [he, ht]
    simpa only [zero_add] using hq.tendsto_slope_zero
  have h0 : p 0 = W.W n v f := by simp [p,ride,R.mi1,push_one]
  suffices h : p = fun _ => W.W n v f from congr_fun h
  apply eq_of_fderiv_eq (𝕜:=ℝ) (fun t => (hp t).differentiableAt) (differentiable_const _) _ 0 h0
  intro x
  rw [fderiv_fun_const, (hp x).hasFDerivAt.fderiv]
  ext; simp

-- `SelfSpeaks`: use rotation-only support result.
structure SelfSpeaks (R:Courts V)(W:WView V) : Prop where
  rotation (n : ℕ) (v : Fin n → V) (x : Joint n) (r : Lorentz) : W.W n (fun i => R.mi r (v i)) (Probe.along (togetherL r _).symm x) = W.W n v x
lemma real_rot (hb:InkBoost Y R)(he:Y.Region)(hori:R.Carriage Y)(hw:Y.NonTangentialFree W) : SelfSpeaks R W:=by
  constructor
  let holds (p : Lorentz) := ∀ n (v : Fin n → V) (f : Joint n),
      W.W n (fun i => R.mi p (v i)) (Joint.gpush n (motion p) f) = W.W n v f
  let U : Subgroup Lorentz := {
    carrier := {p | holds p}
    one_mem' := by intro n v f; simp [push_one,R.mi1]
    mul_mem' := by
      intro a b ha hh
      change holds a at ha
      change holds b at hh
      intro n v f; rw [overL,push_mul]; simp_rw [R.miMul]; rw [ha,hh]
    inv_mem' := by
      intro a ha
      change holds a at ha
      intro n v f
      let v' : Fin n → V := fun i => R.mi a⁻¹ (v i)
      have heq (i : Fin n) : R.mi a (v' i)=v i := by unfold v'; rw [← R.miMul]; simp [R.mi1]
      have hh := ha _ v' (Joint.gpush n (motion a⁻¹) f)
      rw [← push_mul, ← overL,mul_inv_cancel,inactive,push_one] at hh
      simp_rw [heq] at hh; exact hh.symm }
  have hg : beamGens ≤ U := by
    apply (Subgroup.closure_le _).mpr
    rintro p (hp|hp)
    · rcases hp with ⟨r,hr,rfl⟩
      intro n v f
      simp_rw [R.both r hr]
      exact corner_maps hw _ _ _ (fun x _ hy => restricted_spatial hori he v x r hr hy) f
    rcases hp with ⟨i,t,rfl⟩
    intro n v f
    exact boost_invariant Work.C08.answer hb hw v f i t
  intro n v f r
  have hj : holds r := hg (show r ∈ beamGens by rw [show beamGens=⊤ from Work.A16.answer]; trivial)
  rw [← motion_push r f]; exact hj _ v f


open Probe Distribution
lemma tentsF (W : WView V) (R:Courts V)(h:SelfSpeaks R W) (hv : ∀ (v : Fin n → V), dsupport (Distn.fourier (W.W n v)) ⊆ half n) (p : Fin n → V) :
    dsupport (Distn.fourier (W.W n p)) ⊆ coneM n := by
  rw [coneM]; apply subset_iInter; intro i
  let A := togetherL (Lorentz.dual i) n
  apply (Distn.due (Distn.fourier (W.W n p)) (A⁻¹' half n) ((submissive n).preimage A.continuous)).2
  intro t ht
  let z := along A.symm t
  let q := fun j => R.mi i (p j)
  have hZ : tsupport z ⊆ (half n)ᶜ := by
    have he : tsupport z ⊆ A.symm ⁻¹' tsupport t := by
      refine closure_minimal ?_ ((isClosed_tsupport t).preimage A.symm.continuous)
      intro x hx; exact subset_tsupport _ hx
    intro x hx hI; apply ht (he hx)
    rw [Set.mem_preimage]; rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hp := (Distn.due (Distn.fourier (W.W n q)) (half n) (submissive n)).mp (hv q) z hZ
  change W.W n _ (hat _)=_; rw [← h.rotation n p _ i, ← turns]; exact hp
-- genuine joint momentum light cone spectrum test support
def conical (W:WView V):Prop:= ∀ n (v:Fin n→V), dsupport (Distn.fourier (W.W n v)) ⊆ coneM n
lemma on_shape (p:SelfSpeaks R W)(hb:W.cone_tests) : W.conical:= fun _ v=> W.tentsF R p (hb _) v
end YM.SatinWFixed.WView
open YM.SatinWFixed.WView
#print axioms real_rot
#print axioms on_shape
