import YM.SU5.FiniteGaugeData.Marked.Common

/-!
Joint link norms under the common price (C = Nimbus panel, for all periods
large enough to separate this stencil).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Common
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
open VolumeCape VolumeCape.Atlas VolumeCape.Mesh VolumeCape.Cane VolumeCape.Read

variable (C:Side)(D:ℕ→ℝ)(S:Finset Cover)
variable (n : Side)
lemma crop_m (p:Set.InjOn (wrap (More n)) (↑(porch C S):Set Cover)) {μ: Measure (Wor (More n) C)}
    [IsProbabilityMeasure μ]:
    let ξ:= (Borel.Aerial.valsf n).prod μ
    let η:= (prior group (More n)).prod ξ
    MeasurePreserving (fun x:Pane n × ((Borel.Aerial.Frame n) × Wor (More n) C)=> crop C S n x.1 x.2.1) η (law C S) := by
  intro V W
  let a (v:↥(porch C S)):= wrap (More n) (v:Cover)
  let b:=Prod.map a (id:Axis→Axis)
  have h:Injective a:= fun x y u=> Subtype.ext (p x.property y.property u)
  have hz:Injective b:= h.prodMap injective_id
  exact (Girt.normP group.probHaar b hz).prod ((Girt.normP group.probHaar a h).comp measurePreserving_fst)

variable {wide:Bool} {f : PairsC→ℂ} (h:Coeff wide S f)
abbrev amount (f: PairsC→ℂ)(u:Courses C S)(x:Hall C S):= f (pairs C D S u x)
def touch (f: PairsC→ℂ):= ∑ u:Courses C S, ∫ x, ‖amount C D S f u x‖ ∂law C S
lemma touch_pos (f: PairsC→ℂ):0≤touch C D S f:=sum_nonneg fun _ _=>integral_nonneg fun _=>norm_nonneg _
include h
lemma amount_env (u:Courses C S): Envelope (amount C D S f u) := Env.along h.env (pairs_m C D S u)
private lemma tally (l:Loom n)(V:Dream.Haven C D n l)(p:Set.InjOn (wrap (More n)) (↑(porch C S): Set Cover))(e:Measurable l):
    let A(x:Fields n):= f (onC n x.1,onC n x.2)
    (∫ x, ‖A (drawn l x)‖ ∂city n) ≤ touch C D S f := by
  obtain ⟨μ,hp,_,ht⟩:=V; intro A
  let X:=Borel.Aerial.Frame n × Wor (More n) C
  let R:= Pane n × X
  let ν:Measure X:= (Borel.Aerial.valsf n).prod μ; let κ:Measure R:= (prior group (More n)).prod ν
  haveI : IsProbabilityMeasure ν:=by unfold ν; infer_instance
  haveI : IsProbabilityMeasure κ:=by unfold κ; infer_instance
  let B(x:R):Fields n:= (x.1,Dream.sceneQ C D n x.1 x.2)
  have hB: Measurable B:=measurable_fst.prodMk (Dream.sceneM C D n)
  have hA: Envelope A:= Env.along h.env ((on_cont n).prodMap (on_cont n)).measurable
  have hL: (Measure.map (drawn l) (city n))= κ.map B:= by
    apply Borel.Aerial.mixedMap (prior group (More n)) (depot n) ν (drawn_m l e) hB
    intro x
    have hu:= congrArg (Measure.map (fun y:Pane n=>(x,y))) (ht x)
    have hs:Measurable (fun y:Pane n=>(x,y)):= measurable_const.prodMk measurable_id
    have hg:Measurable (fun z=>l (x,z)) := e.comp (measurable_const.prodMk measurable_id)
    have hy:Measurable (Dream.sceneQ C D n x):=(Dream.sceneM C D n).of_uncurry_left
    rw [Measure.map_map hs hg, Measure.map_map hs hy] at hu
    exact hu
  rw [←integral_map (drawn_m l e).aemeasurable hA.meas.norm.aestronglyMeasurable, hL,integral_map hB.aemeasurable hA.meas.norm.aestronglyMeasurable]
  let L(u:Courses C S)(x:Hall C S):= ‖amount C D S f u x‖
  let θ(x:R):=crop C S n x.1 x.2.1
  have ω:MeasurePreserving θ κ (law C S):= crop_m C S n p (μ:=μ)
  have he (u:Courses C S):Integrable (L u) (law C S):= (Env.integrableX (amount_env C D S h u) _).norm
  let Y(x:R):=∑ u:Courses C S, L u (θ x)
  have hb(u:Courses C S): Integrable (fun x => L u (θ x)) κ := ω.integrable_comp_of_integrable (he u)
  have hY:Integrable Y κ:= integrable_finsetSum _ (fun u _=>hb u)
  calc
    (∫ x, ‖A (B x)‖ ∂κ) ≤ ∫ x,Y x ∂κ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _=>norm_nonneg _) hY (Eventually.of_forall fun x=>?_)
      let u:=chooseCourse C S n x.2.2
      have hv := scene_pair C D S n x.1 x.2.1 x.2.2
      have hz: amount C D S f u (θ x)=A (B x):= h.locus _ _ hv.1 hv.2
      change ‖A _‖≤_; rw [←hz]; exact single_le_sum (f:=fun u=>L u (θ x)) (fun _ _=>norm_nonneg _) (mem_univ u)
    _ = touch C D S f := by
      unfold touch Y
      rw [integral_finsetSum _ (fun u _=>hb u)]
      exact Finset.sum_congr rfl fun u _=> (Girt.hinge θ (L u) ω (he u)).symm

/- One local joint-link price for all the periods with this stencilled law. -/
variable (K:Calibration)(a:ℕ)
abbrev Touch (f:PairsC→ℂ):= touch (Dream.plot a).C (Dream.plot a).K S f
omit h
lemma awning : ∀ᶠ m:Side in atTop, ∀ (l:Loom (K.c m)), Dream.Nimbus a _ l → Measurable l →
    ∀ f:PairsC→ℂ, Coeff true S f →
    (∫ x, ‖f (Prod.map (onC (K.c m)) (onC (K.c m)) (drawn l x))‖ ∂city (K.c m)) ≤ Touch S a f := by
  filter_upwards [separates K (porch (Dream.plot a).C S)] with m h l v w f p
  exact tally (Dream.plot a).C (Dream.plot a).K S (K.c m) p l v h w
end YM.CF.Buffered.Afterglow.Common
