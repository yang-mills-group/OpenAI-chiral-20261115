import YM.CF.Mint.Stop
import YM.CF.Nova.Era
import YM.CF.Vale.Land
import YM.CF.Vp929.Analysis.Integrate
import Mathlib.Analysis.Analytic.Order
import GaugeFieldConstruction.AcrossStartup

/-!
# A common bare divide (no cone restriction, but no cross-period estimate yet)

One obligation in the cutoff problem is to actually divide. Here is an unconditional
piece of the normalization estimate. Works for the launched input with the true
mask at each cutoff, for all sufficiently large m (qualification `m=c*N` as
for Looms, not at course rungs only). Does not assert comparing values on this scheme.
Used by Plateau for a genuine common-β on arbitrarily large independently tendered periods.
The analytic top lemmas (windX etc) below use proofs from the supplied LocalFieldBounds reference
project, file `YM/SU5/Weave/Nu/Literal.lean`. They are combined with new pressure
proofs; not inferring their partition nonzero hypothesis outside its permitted rungs
from the LocalFieldBounds theorem.
-/
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2800
set_option maxHeartbeats 500000
namespace YM.CF
open Function Filter Metric NormedSpace Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember MeasureTheory Vale Hom Grace Push.SectorMeasure Next.SectorChange Precision Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff BigOperators InnerProductSpace ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Mint Dial
namespace AcrossLands
open VolumeRate
variable {K:Teller group}{P:Patch}{R:ChartRatio group} {W:Grace K P R}{M m B:Side}{e b b':ℝ}{U:Grasp W.U B e}{G:GivenX W U}
section lower
-- read on single configuration across volume; Limb.Use volume. extend entire via fixed cut.
variable (U m) (p:BudgetPoint)(a:ℝ)
local notation "Πk"=> mid m B -- shadows notation? 
abbrev sharpHat(β:ℝ) (y:Skye.Orbit (mid m B)):= Vale.capP (m:=m) (K:=K) U β p y.1
abbrev sharpWeight(β:ℝ):ℂ := ∫ y:Skye.Orbit (mid m B), Scree.beamZ _ (sharpHat m U p β y) ∂city _
def windX (z:ℂ)(y:Pane (mid m B)) := Complex.exp (((a:ℂ)-z)*(basicP K.top.clip y:ℂ))
-- windX needs K m args
private lemma windX_cont : Continuous (fun x:ℂ×Pane (mid m B)=>windX (K:=K) m a x.1 x.2):=by
 unfold windX; exact ( (continuous_const.sub continuous_fst).mul (Complex.continuous_ofReal.comp ((Nova.ren_c _).comp continuous_snd))).cexp
lemma windX_eq (β:ℝ) (y:Skye.Orbit (mid m B)) : sharpHat m U p β y= windX (K:=K) m a (β:ℂ) y.1 • sharpHat m U p a y:=by
 unfold sharpHat Vale.capP; by_cases h:y.1∈{u:Pane _ | flags p.threshold u=∅}
 · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, smul_smul]; unfold windX; rw [← Complex.exp_add]; congr 2; push_cast; ring
 rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero]
variable (H:Envelope (sharpHat m U p a))
include H
lemma pivot_env (β:ℝ): Envelope (sharpHat m U p β):=by
 have hv:Continuous (windX (B:=B) (K:=K) m a (β:ℂ)):= (windX_cont (B:=B) m a).comp (continuous_const.prodMk continuous_id)
 have he:= Girt.refill _ hv Prod.fst (measurable_fst (β:=Ids (mid m B)))
 rw [funext (windX_eq m U p a β)]
 exact Girt.kitE _ _ (fun (x:ℂ) y=>x • y) (continuous_fst.smul continuous_snd) he H
lemma sharpZeros (v:sharpWeight m U p a≠0): Set.Countable {b|sharpWeight m U p b=0}:=by
 let W0(y:Skye.Orbit (mid m B)) := Scree.beamZ _ (sharpHat m U p a y)
 let Q:=fun (z:ℂ)(y:Skye.Orbit (mid m B))=> windX (K:=K) m a z y.1*W0 y
 let F(z:ℂ):= ∫ y:Skye.Orbit (mid m B), Q z y∂city _
 have he(x:ℝ): sharpWeight m U p x=F (x:ℂ):=by unfold F sharpWeight Q W0; simp_rw [windX_eq m U p a x,Scree.beamZ,inner_smul_right]
 have hW:Envelope W0:= Girt.pole_w (sharpHat m U p a) _ (continuous_const.inner continuous_id) H
 have h:AnalyticOnNhd ℂ F Set.univ:=by
    intro x _; obtain ⟨y,u⟩:= ((isCompact_closedBall x (1:ℝ)).prod isCompact_univ).bddAbove_image (windX_cont (B:=B) (K:=K) m a).norm.continuousOn
    obtain ⟨c,v⟩:= hW.cost
    have hg:DifferentiableOn ℂ F (ball x 1):= by
      refine integrate_holo (F:=Q) isOpen_ball ?_ (fun z _=>?_) (integrable_const (max 0 y *c))
      · refine Eventually.of_forall fun d=> ⟨?_,fun z t=>?_⟩
        · dsimp [Q,windX]; fun_prop
        unfold Q; rw [norm_mul]; exact mul_le_mul ((u ⟨(z,d.1), ⟨ball_subset_closedBall t, trivial⟩, rfl⟩).trans (le_max_right ..)) (v d) (norm_nonneg _) (le_max_left ..)
      exact (Measurable.mul ((show Continuous (windX (B:=B) (K:=K) m a z) from (windX_cont (B:=B) m a).comp (continuous_const.prodMk continuous_id)).measurable.comp measurable_fst) hW.meas).aestronglyMeasurable
    exact hg.analyticOnNhd isOpen_ball x (mem_ball_self zero_lt_one)
 let S:Set ℂ:= F ⁻¹' {0}; have hv: Sᶜ∈Filter.codiscrete ℂ:= h.preimage_zero_mem_codiscrete (he a ▸ v)
 obtain ⟨hc,hv⟩:= compl_mem_codiscrete_iff.mp hv; refine ( (hc.isLindelof.countable_of_isDiscrete hv).preimage Complex.ofReal_injective).mono ?_; intro i t; exact (he i).symm.trans t
end lower
variable (L:Robes M W G)
variable {c:Side}(g:L.h≤c.val){p:BudgetPoint}
variable (u:p.threshold ≤ L.k) (d:K.top.clip.direct≤1)

include g d u
lemma soars (β:ℝ) : Envelope (sharpHat (c*M) U p β):=by
 obtain ⟨h,f,-⟩:= L.soaring p u c g β d; rw [funext f] at h; exact h
lemma true_top (β:ℝ) : partitionZ (launch W.L β p (mid (c*M) B)) U (L.rack c g)=sharpWeight (c*M) U p β:=by
  obtain ⟨-,h,-⟩:= L.soaring p u c g β d; unfold partitionZ; rw [funext h]

local notation "Λ"=> mid (c*M) B
lemma wider (q:BudgetPoint)(t:q.threshold≤p.threshold)(β:ℝ)(h:0≤β)(x: Orbit (mid (c*M) B)) :
 ‖beamZ _ (sharpHat (c*M) U p β x) - beamZ _ (sharpHat (c*M) U q β x)‖ ≤ Real.exp (-(β*(K.top.clip.linear*q.threshold^2))) := by
 by_cases hq: flags q.threshold x.1=∅
 · have hp: flags p.threshold x.1=∅:=by
     apply Finset.eq_empty_iff_forall_notMem.mpr; intro i w; obtain ⟨j,g,s⟩:= (flags_spec ..).mp w; exact Finset.notMem_empty _ (hq ▸ (flags_spec ..).mpr ⟨j,g,t.trans_lt s⟩)
   unfold sharpHat capP; rw [Set.indicator_of_mem (show x.1∈_ from hp),Set.indicator_of_mem (show x.1∈_ from hq),sub_self,norm_zero]; positivity
 unfold sharpHat capP; rw [Set.indicator_of_notMem (show x.1∉ {U : Pane (CSide (c*M) B) | flags q.threshold U=∅} from hq)]; unfold beamZ; rw [inner_zero_right,sub_zero]; by_cases ht: flags p.threshold x.1=∅
 · rw [Set.indicator_of_mem (show x.1∈ _ from ht),inner_smul_right,norm_mul,Complex.norm_exp,Complex.neg_re,Complex.ofReal_re]; let C:=changeM U x.1 babyM; have hz: ‖changeM U x.1 babyM‖=1:=((L.soaring p u c g β d).2.2 _ ht).2.2
   have hx:= norm_inner_le_norm (𝕜:=ℂ) (mateK Λ) C; change _ ≤ _*‖changeM U x.1 babyM‖ at hx; rw [(tickB Λ).2,hz,mul_one] at hx
   refine le_trans (mul_le_of_le_one_right (Real.exp_pos _).le hx) (Real.exp_monotone (neg_le_neg (mul_le_mul_of_nonneg_left (SatinBatches.flag_energy K.top.clip d _ _ hq) h)))
 rw [Set.indicator_of_notMem (show x.1 ∉_ from ht),inner_zero_right,norm_zero]; positivity

lemma wider_mass (q:BudgetPoint)(t:q.threshold≤p.threshold)(β:ℝ)(h:0≤β) :
 ‖sharpWeight (c*M) U p β - sharpWeight (c*M) U q β‖ ≤ Real.exp (-(β*(K.top.clip.linear*q.threshold^2))) := by
 have H(p:BudgetPoint)(l:p.threshold≤ L.k):Integrable (fun x:Orbit (mid (c*M) B)=> beamZ _ (sharpHat _ U p β x)) (city _) := by
   have h:= soars L g l d β; have hv:= pole_w _ (beamZ Λ) (continuous_const.inner continuous_id) h
   exact Integrable.of_bound hv.meas.aestronglyMeasurable _ (Eventually.of_forall hv.cost.choose_spec)
 unfold sharpWeight; rw [←integral_sub (H p u) (H q (t.trans u))]
 exact (norm_integral_le_of_norm_le_const (Eventually.of_forall (wider L g u d q t β h))).trans_eq (by simp)

variable {N:ℕ→Side} (q q':ℕ→BudgetPoint)
variable {v w a r l₁ D E C y r₀ :ℝ} {k n₀:ℕ} (S:Pic.Span G.pearl b v w a r l₁ k)(X:Roe.Port S D E C y r₀ n₀)
  {h:ℝ} (hX:C≤h)(H:1≤h) (φ:∀ i, L.h≤ (N i).val) (hp:∀ i,(q' i).threshold ≤ L.k)
local notation "BASIC"=> (fun i=> mid (N i*M) B) -- silent N*
omit g u
include S X H hX hp φ
lemma big_bare (x:ℕ→ℝ) (t:Tendsto x atTop atTop) (f:Tendsto (eur N) atTop atTop)
    (p:Gray (lum x) (eur N)) (gq:∀ᶠ i in atTop, (q i).threshold = tame x i ∧ (q i).threshold ≤ (q' i).threshold) :
    ∀ᶠ i in atTop, sharpWeight (N i*M) U (q' i) (x i) ≠ 0 := by
  let I:=fun i=> launch W.L (x i) (q i) ((BASIC) i)
  let Lc:=fun i=> L.rack (N i) (φ i)
  have ht:RangeH x x 1 1:= ⟨zero_lt_one,zero_lt_one,t,by filter_upwards with i; simp⟩
  let R:= Mint.Stop.seedB (M:=M) q x x S H f p ht (gq.mono fun i h=> h.1)
  have hS:= Mint.Stop.loom_p L q x x φ t (gq.mono fun i h=>h.1)
  let ξ:=fun i=> drip (I i) U -- cash
  let ℓ:= v/(2*Nova.poseX)/2; have hc:0<ℓ:=by unfold ℓ; have hv:= S.pos; have hz:=Nova.pose_p; positivity
  have hv:= (Roe.ride S R).shrinks.eventually (gt_mem_nhds hc)
  filter_upwards [t.eventually_gt_atTop 0,(Roe.costR S R Lc hS X hX).1,Roe.touch S R,gq,hv] with i e v w h vV
  have hℓ: ξ i *ℓ ≤ ‖sharpWeight (N i*M) U (q i) (x i)‖:= (show ξ i*ℓ ≤ ‖Complex.exp (-(I i).v) * partitionZ (I i) U (Lc i)‖ from v.2.2.2.2.2.2.1).trans_eq (by dsimp only [I,Lc]; rw [true_top L (φ i) (h.2.trans (hp i)) d (x i)]; change ‖Complex.exp (-(0:ℂ)) * _‖=_; simp)
  let Q:= fun i=> Graph.kinetic (More ((BASIC) i)) (q i) K.top.paths W.W.bar (x i) K.top.clip.linear
  have ht: Q i ≤ x i *(K.top.clip.linear*(q i).threshold^2):= by
      apply sub_le_self
      unfold taxY; have hf:=R.row; have hg:= zero_le_one.trans W.W.rental; have hv:= (q i).threshold_pos; positivity
  have he: Real.exp (-Q i) / ξ i < ℓ:=by
      change Real.exp (flagT ((BASIC) i) 0 0 0 - Q i) / ξ i < ℓ at vV
      simpa only [flagT,pittance,doorF,add_zero,zero_mul,mul_zero,zero_add,zero_sub] using vV
  -- Note threshold may itself have come from the bad-sequence query.
  intro z; have hd:=wider_mass L (φ i) (hp i) d (q i) h.2 (x i) e.le
  rw [z,zero_sub,norm_neg] at hd
  have hx:= (hℓ.trans hd).trans_lt ((Real.exp_monotone (neg_le_neg ht)).trans_lt ((div_lt_iff₀ (show 0<ξ i from w.2)).1 he))
  rw [mul_comm] at hx; exact (lt_irrefl _ hx)

omit φ hp
omit S X H hX d in
private lemma prices (p:BudgetPoint)(c:ℝ) (i:ℕ) : ∃ a:ℝ, (i:ℝ)≤a ∧ 0<a ∧ c≤Real.log a ∧ temp a ≤ p.threshold:= by
  obtain ⟨x,⟨e,v,g⟩,q⟩:= ((((eventually_ge_atTop (i:ℝ)).and ((eventually_gt_atTop (0:ℝ)).and (Real.tendsto_log_atTop.eventually_ge_atTop c))).and ((show Tendsto temp atTop (𝓝 0) from by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds p.threshold_pos))).exists)
  exact ⟨x,e,v,g,q⟩

/-- All masks, including arbitrarily small ones (but not threshold zero).
Non-vanishing somewhere, not at the prescription yet. -/
theorem mass_exists : ∃ n:ℕ, L.h≤n ∧ ∀ (c:Side), n≤c.val → ∀ (p:BudgetPoint), p.threshold≤L.k → ∃ b>0, sharpWeight (c*M) U p b ≠ 0:= by
 by_contra! w
 have hw:= fun i=> w (i+L.h) (Nat.le_add_left _ _)
 choose N f q hp e using hw
 have hN:∀ i, L.h≤ (N i).val:= fun i=>(Nat.le_add_left _ _).trans (f i)
 choose x ω₁ ω₂ η θ using fun i=> prices (q i) (eur N i) i
 let q'(i):BudgetPoint:={ q i with threshold:= temp (x i), threshold_pos := Work.E09.temp_pos (ω₂ i), threshold_le := (θ i).trans (q i).threshold_le}
 have hg: Gray (lum x) (eur N):= ⟨1,zero_lt_one,1,Eventually.of_forall fun i=>by rw [Real.norm_of_nonneg (by unfold eur; positivity),pow_one,one_mul]; exact η i⟩
 obtain ⟨i,t⟩ := (big_bare L d q' q S X hX H hN hp x (tendsto_atTop_mono ω₁ tendsto_natCast_atTop_atTop) (tendsto_atTop_mono (fun i=> show (i:ℝ)≤ eur N i from Nat.cast_le.mpr (by have he:=f i; omega)) tendsto_natCast_atTop_atTop) hg (Eventually.of_forall (fun i=>⟨rfl,θ i⟩))).exists
 exact t (e i _ (ω₂ i))

/-- Can purchase this before the Appointment sequence. -/
structure Territory (K:Teller group) {W: Grace K P R} {U:Grasp W.U B e} {G:GivenX W U}
    (L:Robes M W G) (n:ℕ) : Prop where
  min_size : L.h≤n
  fails (c:Side) (h:n≤c.val) (p:BudgetPoint) (hp:p.threshold≤L.k):
    Set.Countable {x:ℝ | sharpWeight (c*M) U p x=0}

theorem pre_quit : ∃ n, Territory K L n:=by
  obtain ⟨n,h,hp⟩:= mass_exists L d S X hX H
  exact ⟨n,h,fun c g p u=>by
    obtain ⟨b,e,v⟩:= hp c g p u; exact sharpZeros _ U p b (soars L (h.trans g) u d b) v⟩

#print axioms mass_exists
#print axioms pre_quit
end AcrossLands
end YM.CF
