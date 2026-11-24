import YM.SU5.FiniteGaugeData.Marked.Abstract
import YM.SU5.FiniteGaugeData.Marked.Lentil
import YM.SU5.FiniteGaugeData.Marked.Grammar

/-!
# Simultaneous extraction using period-uniform estimates

Supply a candidate pair of sequences of scales, e.g. the ones of an
existing gauge extraction/period election. Ask for exact local Loom
spec at the periods used (scale zero only), carries the shared
fixed stencil for every covered Borel mark. We will further thin these
same two sequences, so any row-wise eventual cutoff gates, the realized
trajectories, Looms, reflection data etc do not have to be elected again.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

/- input (selectable periods at the existing fixed resolution, each with a
shared Loom; no convergence assumptions). -/
structure Circuit (K:Calibration) (H:Histories K)(l:ℕ) where
  volume : ℕ→Side
  admitted (i:ℕ) : K.takes (volume i)
  ir : StrictMono (fun x=> (volume x).val)
  cut : ℕ→ℕ
  uv : StrictMono cut
  vis (i:ℕ) : VolumeCape.Dream.Nimbus l _ (H.loom (volume i) 0)

variable {K:Calibration}(H:Histories K){l:ℕ}(c:Circuit K H l) (S:Finset Cover)(u:Sound.Chorus)
namespace Circuit
variable {H}
lemma v_grows : Tendsto c.volume atTop atTop := tendsto_atTop.2 (fun i:Side=> c.ir.tendsto_atTop.eventually_ge_atTop i.val)
def inCone (i k:ℕ):= (c.volume i).val^5 ≤ c.cut k
lemma visits (i:ℕ): ∀ᶠ k in atTop,c.inCone i k:= c.uv.tendsto_atTop.eventually_ge_atTop _
lemma misses (k:ℕ): ∀ᶠ i:ℕ in atTop, ¬ c.inCone i k:= ((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp c.ir.tendsto_atTop|>.eventually_gt_atTop (c.cut k)).mono fun _ h=> not_le.mpr h
lemma issued (i:ℕ):∀ᶠ k in atTop,Wick H (c.volume i) (c.cut k):= c.uv.tendsto_atTop.eventually ((eventuallyWick H).mp ((K.eventually_allowed (c.admitted i)).mono fun _ h v=>v _ h))
end Circuit

local notation "rule" => VolumeCape.Dream.plot l
noncomputable def price := (bank H S).choose
lemma price_pos :0<price H S:= (bank H S).choose_spec.1
structure Serves (m:Side)(i:ℕ):Prop where
  wick : Wick H m i
  statute (f:Mark (K.c m)) : AtSupport false (S.image (wrap (More (K.c m)))) f → ‖hearth H m i f‖ ≤ price H S*cash (H.loom m 0) f
  career (f:PairsC→ℂ)(h:Coeff true S f): let n:=K.c m
    (∫ x, ‖f (Prod.map (onC n) (onC n) (drawn (H.loom m 0) x))‖ ∂city n) ≤ Touch S l f
variable (l) in
lemma room : ∀ᶠ m:Side in atTop,
    VolumeCape.Dream.Nimbus l _ (H.loom m 0)→ ∀ i:ℕ,Wick H m i→Serves H S (l:=l) m i := by
  filter_upwards [(bank H S).choose_spec.2,awning S K l] with m h e g i v
  exact ⟨v,h i v,e _ g v.loom_m⟩
variable (l)
structure Bracket : Prop where
  tines : staves u S
  harmony : treble u=false

def host (f:PairsC→ℂ)(m:Side)(i:ℕ):ℂ:=hearth H m i (note K f u m)
def trimmed (x:Purse S)(m i:ℕ):ℂ := if _h : Bracket S u ∧ Serves H (l:=l) S (c.volume m) (c.cut i) then
    host H u x.val (c.volume m) (c.cut i) else 0

variable {H S u l c}
lemma Serves.foremost {m:Side}{i:ℕ}(w:Serves H (l:=l) S m i)(t:Bracket S u)
    (x:Purse S): ‖host H u x.val m i‖ ≤ price H S * Touch S l x.val := by
  unfold host
  have hp: AtSupport false (S.image (wrap (More (K.c m)))) (note K x.val u m) := t.harmony ▸ (note_t K u x.property t.tines).support m
  refine (w.statute _ hp).trans (mul_le_mul_of_nonneg_left ?_ (price_pos H S).le)
  refine (w.career _ x.property).trans' ?_
  have ht : Envelope (fun X:Fields (K.c m)=> x.val (Prod.map (onC (K.c m)) (onC (K.c m)) X)):= Env.along x.property.env ((on_cont _).prodMap (on_cont _)).measurable
  unfold cash; exact integral_mono_of_nonneg (Eventually.of_forall fun _=>norm_nonneg _) (cashable' w.wick.loom_m ht) (Eventually.of_forall fun x'=> pitched K u x.val m (drawn _ x'))
where
 cashable' {n:Side}{g:Fields n→ℂ}{R:Loom n}(p:Measurable R)(v:Envelope g): Integrable (fun x=> ‖g (drawn R x)‖) (city n):= (Env.integrableX (Env.along v (drawn_m R p)) _).norm

variable (c S u)
lemma mainstage (x:Purse S) (m i:ℕ): ‖trimmed H l c S u x m i‖ ≤ price H S * Touch S l x.val:= by
  unfold trimmed; split_ifs with h; exact h.2.foremost h.1 _
  rw [norm_zero]; exact mul_nonneg (price_pos H S).le (touch_pos ..)
lemma nearby (x y:Purse S) (m i:ℕ): dist (trimmed H l c S u x m i) (trimmed H l c S u y m i) ≤ price H S * Touch S l (x.val-y.val):= by
  unfold trimmed; split_ifs with h; swap; · rw [dist_self]; exact mul_nonneg (price_pos H S).le (touch_pos ..)
  let z:Purse S:=⟨x.val-y.val,pastel x.property y.property⟩
  refine (h.2.foremost h.1 z).trans' ?_
  unfold host z; rw [dist_eq_norm,note_minus]; dsimp only [Pi.add_apply,Pi.smul_apply]
  rw [h.2.wick.warm_add ((note_t K u x.property h.1.tines).support (c.volume m)).env
    ((((note_t K u y.property h.1.tines).support (c.volume m)).smulM _).env),Wick.warm_scale]
  rw [neg_one_mul,sub_eq_add_neg]


abbrev songbook (S:Finset Cover)(l:ℕ):ℕ→Purse S := (Common.sample (VolumeCape.Dream.plot l).C (VolumeCape.Dream.plot l).K S).choose
abbrev Playbill:= Finset Cover × Sound.Chorus × ℕ
lemma recital (pay:ℕ→ℕ→Prop)(pX:∀ m,∀ᶠ n:ℕ in atTop,pay m n):
    ∃ i k:ℕ→ℕ, StrictMono i ∧ StrictMono k ∧
      (∀ a b, c.inCone (i a) (k b) → pay (i a) (k b) ∧ Wick H (c.volume (i a)) (c.cut (k b))) ∧
      ∀ (S:Finset Cover)(u:Chorus)(x:Purse S), ∃ F z, Couplet i k (trimmed H l c S u x) F z (fun f=> ∀ᶠ n in atTop,c.inCone (i n) (k (f n))) := by
  let f(j:Playbill):=songbook j.1 l j.2.2
  let X(j:Playbill):= trimmed H l c j.1 j.2.1 (f j)
  obtain ⟨i,k,g,v,s,h⟩:= recites X (fun j=> ⟨_,fun m k=> mainstage c _ _ _ _ _⟩) (fun m=> (pX m).and (c.issued m)) c.visits c.misses
  refine ⟨i,k,g,v,s,fun S u x=> rising_cloud _ ?_⟩
  intro r e
  let Q:=price H S; have hq:0<Q:=price_pos H S
  obtain ⟨p,t⟩:= (Common.sample (VolumeCape.Dream.plot l).C (VolumeCape.Dream.plot l).K S).choose_spec x (r/Q) (div_pos e hq)
  let j:Playbill:= (S,u,p); obtain ⟨F,z,u'⟩:= h j
  refine ⟨X j,F,z,(fun n b=> (nearby c S u x (songbook S l p) n b).trans ?_),u'⟩
  rw [mul_comm]; exact ((lt_div_iff₀ hq).1 t).le
end YM.CF.Buffered.Afterglow
