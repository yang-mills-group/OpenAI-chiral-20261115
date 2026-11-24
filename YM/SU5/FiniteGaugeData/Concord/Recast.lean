import YM.SU5.FiniteGaugeData.Concord.Thinning
/-!
# Extraction of box-office limits preserving any elected marked reading

On the specified terminal pivot history. Also can simultaneously preserve/choose limits of
effective prices shown (each fixed observing step, **not** at moving bare scales or requiring
that the different periods work on identical beta or wave etc.). Keep p→x planner fixed. What
lets us estimate the effect of the actual period-dependent prescriptions (including nuisance
operators, branching & auxiliary choices and RG data) on the WHOLE determining local multiscale
reading will be the approximation of the actual transmitted operators here, NOT a bound derived
from presumed stabilization of input data. No stability under a change of prescription claimed.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
variable (S:Finset Cover)(s:ℕ) {i k p u v:ℕ→ℕ} (V: Universal Y H i k F E)
local notation "Wf" s:max i:max k:max => (((Y.voyage i).X (Y.uv k)).wave s).val
local notation "Ω" => ConeFilter Y i k

-- step prices we also retain in thinning, gifted at Course. PairIdx only required for bounds
def actualQuote (j n:ℕ):ℝ × Op SU.Slot := (Y.beta j n s,Wf s j n)
def quoted (j n:ℕ) : ℝ × Op SU.Slot := if PairIdx Y s j n then actualQuote Y s j n else 0

theorem review_size : ∃ T : Set (ℝ × Op SU.Slot), IsCompact T ∧ ∀ i k, quoted Y s i k ∈ T :=by
  let a:= |Course.ceiling Λ s|; let b:= |Λ.R0 (hat Λ.R.L Λ.x s)|
  refine ⟨(Set.Icc (-a) a) ×ˢ closedBall 0 b,isCompact_Icc.prod (ProperSpace.isCompact_closedBall _ _),fun i k=>?_⟩
  unfold quoted; split_ifs with t
  · have he : ‖Wf s i k‖ ≤ b:= (((Y.voyage i).X (Y.uv k)).pull.tip s t.2).trans (le_abs_self _)
    exact ⟨abs_le.mp ((abs_le.mpr (Y.seated s i k t.2)).trans (le_abs_self _)),mem_closedBall_zero_iff.mpr he⟩
  exact ⟨⟨neg_nonpos.mpr (abs_nonneg _),abs_nonneg _⟩,mem_closedBall_self (abs_nonneg _)⟩

abbrev Method (Λ:Preparation)(l:ℕ)(S:Finset Cover):= Palette S→L[ℂ] Palette (swept Λ l S)

/-- One limit operator for EVERY observing step and support on a fixed tower. -/
abbrev Playhouse (Λ:Preparation)(l:ℕ) :=
    (∀ (_s:ℕ)(S:Finset Cover), Method Λ l S) ×
    (∀ (_s:ℕ)(S:Finset Cover)(_n:ℕ), Method Λ l S) ×
    (ℕ → ℝ × Op SU.Slot) × (ℕ→ℕ→ ℝ × Op SU.Slot)

namespace Playhouse
variable (P:Playhouse Λ l)
abbrev issue := P.1
abbrev matinee := P.2.1
abbrev retail := P.2.2.1
abbrev tariff := P.2.2.2
end Playhouse

/-- The extra estimates, not touching the physical limits already bought. -/
def Meter (r:ℕ):ℝ:= (1/2:ℝ)^r
lemma meter_p (r:ℕ):0<Meter r := by unfold Meter; positivity
lemma meter_time:Tendsto Meter atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma meter_law : Antitone Meter:= by intro i j p; exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num) p

structure Traces (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
    (i k:ℕ→ℕ)(P:Playhouse Λ l) :Prop where
  clocks (s:ℕ)(S:Finset Cover): Couplet i k (screen Y H S s) (P.matinee s S) (P.issue s S) (Paths Y i k)
  quoteSteps (s:ℕ) : Couplet i k (quoted Y s) (P.tariff s) (P.retail s) (Paths Y i k)
  errorC (s:ℕ)(S:Finset Cover) : ∀ᶠ n in atTop,∀ k', legacy Y (i n) (k k') →
    SeasonPass Y H S s (i n) (k k') ∧ dist (screen Y H S s (i n) (k k')) (P.issue s S) ≤ Meter n ∧
    dist (actualQuote Y s (i n) (k k')) (P.retail s) ≤ Meter n

variable (P:Playhouse Λ l)

private abbrev Nights := ℕ × Finset Cover
private abbrev Viewer (Λ:Preparation)(l:ℕ)(w:Nights) := Method Λ l w.2 × (ℝ × Op SU.Slot)
private def nights (q:Nights)(n j:ℕ) : Viewer Λ l q := (screen Y H q.2 q.1 n j, quoted Y q.1 n j)
private theorem price (w:Nights) : ∃ T:Set (Viewer Λ l w),IsCompact T ∧ ∀ i k,nights Y H w i k∈ T:=by
  obtain ⟨A,h₀,q⟩:= review_size Y w.1; exact ⟨_ ×ˢ _, (boxOffice Y H w.2 w.1).prod h₀, fun i k=> ⟨subset_closure (Set.mem_range_self (i,k)), q i k⟩⟩
private lemma trial :∃ U:ℕ→Finset Nights, ∀ x,∀ᶠ n in atTop,x∈U n:=by
  obtain ⟨t,v⟩:= exists_surjective_nat Nights
  refine ⟨fun n=>(range (n+1)).image t,fun x=>?_⟩
  obtain ⟨q,rfl⟩:= v x
  exact (eventually_ge_atTop q).mono (fun i p=> mem_image_of_mem t (mem_range.mpr (by omega)))

include V
lemma elect : ∃ (u v:ℕ→ℕ), StrictMono u ∧ StrictMono v ∧
    ∃ Q:Playhouse Λ l, Traces Y H (i∘u) (k∘v) Q:=by
  let A:= nights Y H; let a:= V.pick.grow_i; let b:= V.pick.grow_k
  obtain ⟨τ,w⟩:= trial
  obtain ⟨f,g,I,T,e,h,U⟩:= YM.SU5.FiniteGaugeData.LocalLimit.Rings.two_steps A (fun i x=> Stadium Y H x.2 x.1 i) (fun i k x=> SeasonPass Y H x.2 x.1 i k)
    (legacy Y) τ Meter (price Y H) (fun x=> crowd ..) (fun i x p=> ((eventually_ge_atTop (Y.voyage _).kick).and (Y.uv_grows.tendsto_atTop.eventually_gt_atTop x.1)).mono (fun _ h=> show SeasonPass Y H x.2 x.1 _ _ from ⟨p,h⟩)) (cadence Y id strictMono_id) (absent Y id strictMono_id) meter_p i k a b
  let Q:Playhouse Λ l := ⟨fun s S=> (T (s,S)).1,fun s S i=> (I (s,S) i).1,fun s=> (T (s,∅)).2, fun s i=> (I (s,∅) i).2⟩
  let a:=i∘f; let b:=k∘g
  have he(x:Nights)(q:ℕ→ℕ)(v:Paths Y a b q): Tendsto (fun n=> A x (a n) (b (q n))) atTop (𝓝 (T x)):= by
    refine  (Metric.tendsto_nhds (α:=Viewer Λ l x) (a:=T x)).mpr fun ε e=> ?_; filter_upwards [v,w x,meter_time.eventually (gt_mem_nhds e)] with n t p u
    exact ((U.line n (q n) ((U.card n (q n)).1 t) x p).2).trans_lt u
  refine ⟨f,g,e,h,Q,fun s S=> ⟨fun x=> (U.cut (s,S) x).fst_nhds,(U.ir (s,S)).fst_nhds, fun p u=>(he (s,S) p u).fst_nhds⟩,
    fun s=> ⟨fun x=> (U.cut (s,∅) x).snd_nhds,(U.ir (s,∅)).snd_nhds,fun p u=> (he (s,∅) p u).snd_nhds⟩,fun s S=> ?_⟩
  filter_upwards [w (s,S), w (s,∅)] with n u v j l
  obtain ⟨k,t⟩:=U.line n j ((U.card n j).1 l) (s,S) u; rw [Prod.dist_eq,max_le_iff] at t
  have ht₀:=(U.line n j ((U.card n j).1 l) (s,∅) v).2; rw [Prod.dist_eq,max_le_iff] at ht₀
  refine ⟨k,t.1,?_⟩; rw [show actualQuote Y s _ _= _ from (show quoted Y s (a n) (b j)=actualQuote Y s (a n) (b j) from if_pos k.timely).symm]; exact ht₀.2
variable (U:Traces Y H i k P)
include U
lemma recast (a:StrictMono u)(b:StrictMono v): Traces Y H (i∘u) (k∘v) P:=by
  refine ⟨fun s S=> Smaller.couplet (U.clocks s S) V.pick.grow_k a b,fun s=> Smaller.couplet (U.quoteSteps s) V.pick.grow_k a b,fun s S=>?_⟩
  filter_upwards [a.tendsto_atTop.eventually (U.errorC s S)] with n e k v₀
  obtain ⟨p,h,t⟩:=e (v k) v₀; exact ⟨p,h.trans (meter_law (a.id_le n)),t.trans (meter_law (a.id_le n))⟩

lemma cone_trace : Tendsto (fun n:ℕ×ℕ=>screen Y H S s (i n.1) (k n.2)) (ConeFilter Y i k) (𝓝 (P.issue s S)):= (ConeFilter.tendsto_iff_paths V.pick.grow_k).mpr ((U.clocks s S).paths)
lemma cone_quotes : Tendsto (fun n:ℕ×ℕ=> actualQuote Y s (i n.1) (k n.2)) (ConeFilter Y i k) (𝓝 (P.retail s)) :=
  Tendsto.congr' ((timely_visit V.pick s).mono (fun _ p=>if_pos p)) ((ConeFilter.tendsto_iff_paths (Y:=Y) (i:=i) V.pick.grow_k (f:=fun n=> quoted Y s (i n.1) (k n.2))).mpr (U.quoteSteps s).paths)
omit V U

/-- Keep the crimson estimate all along these same periods even as we obtained transmission
and quote estimates. On these very sequences: one chosen calibration *before* any limit. -/
structure Traced (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)(i k:ℕ→ℕ)
    (F:ℕ→Family (tent Y H)→ℕ→ℂ)(E:ℕ→Family (tent Y H)→ℂ)(P:Playhouse Λ l) : Prop where
  own : Universal Y H i k F E
  receipts : Traces Y H i k P
  crimson (S:Finset Cover)(s:ℕ) : ∀ᶠ r in atTop,
    let m:=momentm Y (i r) s
    Hosp S ((tent Y H).c m) ∧ ∀ (f:Family (tent Y H)), InTest (tent Y H) true S false f →∀ A:ℝ,(∀ x,‖f m x‖ ≤ A) →
      ‖F s f (i r) - E s f‖ ≤ Meter r * A ∧ ∀ j, legacy Y (i r) (k j)→‖sharp Y H s (i r) (k j) f-E s f‖ ≤ Meter r * A

include V

theorem draw : ∃ (u v:ℕ→ℕ) (Q:Playhouse Λ l), StrictMono u ∧ StrictMono v ∧ Traced Y H (i∘u) (k∘v) F E Q:=by
  obtain ⟨x,y,t,q,B,h⟩:= elect Y H V
  let R:= Smaller.universal V t q
  obtain ⟨f,e,v⟩:= Satin.crimson Y H R
  exact ⟨x∘f,y,B,t.comp e,q,Smaller.universal (i:=i∘x) (k:=k∘y) (u:=f) (v:=id) R e strictMono_id,recast (i:=i∘x) (k:=k∘y) (u:=f) (v:=id) Y H R B h e strictMono_id,v⟩
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.draw
#print axioms YM.CF.Buffered.Concord.cone_quotes
