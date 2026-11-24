import SatinThinNuclear
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid


private lemma spender {W:Type*} [MeasurableSpace W] (m:Measure W) (T:ℕ → W → ℝ) (hm:∀ n, Integrable (T n) m) (hp:∀ n w, 0≤ T n w) (he:Summable fun n=>∫ x,T n x∂m): (∀ᵐ x ∂m, Summable fun n=>T n x):= by -- adapt Silk/Span/Salt
 have hl(i:ℕ) : ∫⁻ a, ‖T i a‖ₑ ∂m= ‖∫ a, ‖T i a‖ ∂m‖ₑ:= by
    dsimp [enorm]; rw [lintegral_coe_eq_integral _ (hm i).norm,ENNReal.coe_nnreal_eq, coe_nnnorm]; rw [Real.norm_of_nonneg (integral_nonneg (fun a:W=>abs_nonneg (T i a)))]; rfl
 have ht': Summable (fun i=> ∫ a, ‖T i a‖ ∂m):=by simpa only [Real.norm_of_nonneg (hp ..)] using he -- simp using he? lem on goal
 have hf': (∑' i, (∫⁻ a, ‖T i a‖ₑ ∂m)) ≠ ∞:= by simp_rw [hl]; exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 ht'.abs)
 have hf (i:ℕ): AEMeasurable (fun a=>‖T i a‖ₑ) m:= (hm i).1.enorm
 have hhh: ∀ᵐ a ∂m, Summable fun n=> (‖T n a‖₊:ℝ) :=by
    rw [← lintegral_tsum hf] at hf'
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hf) hf'] with x hx
    rw [←ENNReal.tsum_coe_ne_top_iff_summable_coe]; exact hx.ne
 have hx(a:W) (i:ℕ): (‖T i a‖₊:ℝ)= T i a:=Real.norm_of_nonneg (hp i a)
 simpa only [hx] using hhh
private lemma sparse {I W:Type} [Countable I][MeasurableSpace W](m: Measure W)
    (a:ℕ→ℕ)(u:StrictMono a)
    (T:I→ℕ→W→ℝ)(h:∀ i n x,0≤ T i n x)(g:∀ i n,Integrable (T i n) m)
    (w:∀ i,Tendsto (fun n=> ∫ x,T i n x∂m) atTop (𝓝 0)) :
    ∃ e:ℕ→ℕ,StrictMono e ∧
       ∀ᵐ x∂m,∀ i,Tendsto (fun n=>T i (a (e n)) x) atTop (𝓝 0):= by
 cases isEmpty_or_nonempty I; · refine ⟨id,strictMono_id,Eventually.of_forall fun _ i=>isEmptyElim i⟩
 obtain ⟨l,j⟩:=exists_surjective_nat I
 let c:ℝ:=1/2; have hc:0<c:=by norm_num [c]
 have t(n k:ℕ): ∃ r,k<r ∧ ∀ i∈Finset.range n,(∫ x,T (l i) (a r) x∂m) ≤ c^n:=by
    have e: ∀ᶠ r in atTop,∀ i∈Finset.range n,(∫ x,T (l i) (a r) x∂m) ≤ c^n:=(eventually_all_finset _).mpr fun i _=> ((w _).comp u.tendsto_atTop).eventually (ge_mem_nhds (pow_pos hc n))
    exact ((eventually_gt_atTop k).and e).exists
 choose z p q using t

 let e:ℕ→ℕ:=Nat.rec 0 (fun i k=> z (i+1) k)
 refine ⟨e,strictMono_nat_of_lt_succ (fun n=>p _ _),(ae_all_iff.mpr fun i=> ?_)⟩
 obtain ⟨b,rfl⟩:= j i
 have hx:Summable (fun n=>∫ x,T (l b) (a (e n)) x∂m):= by
    apply (summable_geometric_of_norm_lt_one (show ‖c‖<1 from by norm_num [c])).of_norm_bounded_eventually_nat
    filter_upwards [eventually_gt_atTop b] with n t'; cases n; · omega
    rw [Real.norm_of_nonneg (integral_nonneg fun _=>h ..)]; exact q _ _ b (mem_range.mpr t')
 exact (spender m (fun n=> T (l b) (a (e n))) (fun _=>g ..) (fun _ _=>h ..) hx).mono fun x t=> Summable.tendsto_atTop_zero t

open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable (P:Spine)
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "F" s:max=>hat P.par.R.L P.par.x s
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Regis.Circuit
local notation "z'"=> Yoke.witnessZ
local notation "m" r:max => ((P.plannedK r:ℕ):ℝ)
abbrev photo (r:ℕ)(X:Cover): Vantage:= fun k=>(X k:ℝ)/ (m r)
abbrev lengthP (r:ℕ):ℝ:=P.flightCap (P.pointEra r)
lemma plan_p(r:ℕ):0 < m r:= Nat.cast_pos.mpr (P.pointK_pos ..)
lemma local_hero {X:ℕ→ Cover}{d:Vantage}(h:Tendsto (fun s=>P.photo s (X s)) atTop (𝓝 d)) {w:ℝ}(u:P.depthCap<w): ∀ᶠ s:ℕ in atTop,∀ k:Axis,(X s k).natAbs ≤ scout Λ w s:=by
 apply eventually_all.mpr
 intro k
 obtain ⟨n,c⟩:=exists_nat_gt |d k|
 -- axis focus divided tends n
 have hx: Tendsto (fun s=>(P.focusF (P.plannedK s) n 0 3:ℝ) / (m s)) atTop (𝓝 (n:ℝ)):= by
    let a(s):ℝ:= P.persistN (P.plannedK s)
    have hv:Tendsto (fun s=>a s/(m s)) atTop (𝓝 0):=squeeze_zero (fun s=>div_nonneg (P.tiny_one_ledger s _|>.1) (P.plan_p s).le) (fun s=> div_le_div_of_nonneg_right (P.tiny_one_ledger s _|>.2) (P.plan_p s).le) (tendsto_const_nhds.div_atTop (a:=(P.echoFoot:ℝ)) P.planned_grows)
    have he:= (tendsto_const_nhds (x:=(n:ℝ))|>.add (hv.const_mul (1-(n:ℝ)))); rw [mul_zero,add_zero] at he; apply he.congr; intro s; rw [P.focus_axis]; rw [Int.cast_add,Int.cast_mul,Int.cast_mul,Int.cast_sub,Int.cast_one, Int.cast_natCast, Int.cast_natCast]; unfold a; rw [add_div,mul_div_assoc,div_self (P.plan_p s).ne',mul_one,mul_div_assoc]

 filter_upwards [((tendsto_pi_nhds.mp h k).abs.eventually_lt hx c),P.military_size u n 0] with s q p
 let A:= P.focusF (P.plannedK s) n 0 (3:Axis)
 change |(X s k:ℝ)/(m s)| < (A:ℝ)/(m s) at q; rw [abs_div,abs_of_pos (P.plan_p s),← Int.cast_abs,div_lt_div_iff_of_pos_right (P.plan_p s),Int.cast_lt] at q
 have he:(X s k).natAbs ≤ A.natAbs:= by rw [←Int.ofNat_le,Int.natCast_natAbs,Int.natCast_natAbs]; exact le_trans q.le (le_abs_self _);
 exact he.trans (p 3).1

abbrev strike (X R:ℕ→ Cover)(d a:Vantage) (s:ℕ): P.Spectrum0 3→ℝ:= P.mistake 3 z' s (m s) (X s) (R s) (moor (d-a))
variable {Cε:ℝ}
abbrev Care(P:Spine)(Cε:ℝ): Prop:= ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost Cε P.run s i k
lemma photo_go (Z:P.Care Cε){X R:ℕ→ Cover}{d a:Vantage}(h:d ≠ a)
    (v:Tendsto (fun s=>P.photo s (X s)) atTop (𝓝 d))
    (u:Tendsto (fun s=>P.photo s (R s)) atTop (𝓝 a)): Tendsto (fun s=>∫ x,P.strike X R d a s x∂(P.pillars 3)) atTop (𝓝 0):= by
 let p:=8*P.depthCap+1; have hp:=P.depthCap_pos; let A:=14+2*p; let c:= P.depthCap+6*A+2*p+1; have hx:P.depthCap < c:=by unfold c A p;linarith
 have hw:∀ᶠ j:ℕ in atTop,CoversT (twinTrip (X j) (R j)) (scout P.par c j):=by
    filter_upwards [P.local_hero v hx,P.local_hero u hx] with s t v b
    cases b <;> assumption
 have hpu:0<p:=by unfold p; linarith only [hp]


 refine P.mistake_go 3 z' A p c Z P.plan_p P.planned_grows ?_ ?_ hw ?_ (by unfold A; linarith) hpu (by unfold c; linarith only [hp])
 · let e:=WithLp.toLp 2 (V:=Axis→ℝ)
   exact (((PiLp.continuous_toLp 2 _).tendsto (d-a)).comp (v.sub u)).congr (fun s=>by ext k; change (X s k:ℝ)/_ - (R s k:ℝ)/(m s)=((X s-R s) k:ℝ)/_; rw [← sub_div,Pi.sub_apply,Int.cast_sub])
 · intro e; have ht:d-a=0:= congrArg WithLp.ofLp e; exact h (sub_eq_zero.mp ht)
 have he:= P.planning_size_go 1 0 (by norm_num) p (by unfold p;linarith)
 unfold travelF at he
 rw [Nat.add_zero,Nat.cast_one] at he; simpa only [one_mul] using he
lemma era_le (r:ℕ):P.pointEra r ≤ r:= Nat.sub_le ..
abbrev paceN (r:ℕ):ℝ:=P.sidesPerTick/(m r)
lemma paceN_pos (r:ℕ): 0<P.paceN r:=div_pos (Nat.cast_pos.mpr P.sides_pos) (P.plan_p r)
lemma paceN_t : Tendsto P.paceN atTop (𝓝 0) := tendsto_const_nhds.div_atTop P.planned_grows
lemma paceN_width (r:ℕ): P.paceN r * P.lengthP r=P.macroStep r:= by
 have hm := (P.plan_p r).ne'; have hc: (P.sidesPerTick:ℝ)≠0:= (Nat.cast_pos.mpr P.sides_pos).ne'
 unfold lengthP paceN; rw [←P.offeringF (P.era_le r)]
 change _/(m r) * ((m r)*_/_)=_
 field_simp
abbrev tap (y:Vantage) (r:ℕ): Cover:=fun k=> ⌊y k/P.paceN r⌋
abbrev roundPose (y:Vantage)(r:ℕ): Vantage:= fun k=>(P.tap y r k:ℝ)*P.paceN r
lemma tap_scale (y:Vantage)(r:ℕ):P.meshPose r (P.tap y r) = P.lengthP r • P.roundPose y r:= by ext; unfold roundPose; rw [Pi.smul_apply,smul_eq_mul,P.pose_w,← P.paceN_width]; ring
lemma tap_t (y:Vantage): Tendsto (P.roundPose y) atTop (𝓝 y):= by
 refine tendsto_pi_nhds.mpr fun k=>tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun r=>y k-P.paceN r) (f:=fun r=>P.roundPose y r k) (by simpa only [sub_zero] using ((tendsto_const_nhds (x:=y k)).sub P.paceN_t)) 

   (tendsto_const_nhds (x:=y k))
   (fun r=> show y k-P.paceN r ≤ _ from (by
      have h : y k/P.paceN r < (P.tap y r k:ℝ)+1:= Int.lt_floor_add_one _
      rw [div_lt_iff₀ (P.paceN_pos _)] at h; change _ ≤ (P.tap y r k:ℝ)*_;linarith only [h]))
   (fun r=> (le_div_iff₀ (P.paceN_pos r)).mp (Int.floor_le _))

abbrev pix (l:List Axis)(y:Vantage)(r:ℕ): Cover:= pivotQ (P.granule (P.plannedK r)) l + P.sidesPerTick • P.tap y r
lemma glimmer (l:List Axis)(y:Vantage): Tendsto (fun r=> P.photo r (P.pix l y r)) atTop (𝓝 y):= by
 apply tendsto_pi_nhds.mpr; intro k
 let Z(r:ℕ):ℤ:=pivotQ (P.granule (P.plannedK r)) l k
 have h: Tendsto (fun r=>(Z r:ℝ)/(m r)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]; simp_rw [Real.norm_eq_abs]
    apply squeeze_zero (fun _=>abs_nonneg _) _ (tendsto_const_nhds.div_atTop (a:=(P.echoFoot:ℝ)) P.planned_grows)
    intro r; rw [abs_div,abs_of_pos (P.plan_p r)]; apply div_le_div_of_nonneg_right _ (P.plan_p r).le
    obtain ⟨g,h⟩:=P.tiny_one_ledger r (P.plannedK r)
    rcases show Z r=P.persistN (P.plannedK r) ∨ Z r= -P.persistN (P.plannedK r) from pivot_alone _ _ k with e|e <;>
      (rw [e]; simpa only [Int.cast_neg,abs_neg,abs_of_nonneg g] using h)
 have z:= h.add (tendsto_pi_nhds.mp (P.tap_t y) k)
 rw [zero_add] at z
 apply z.congr; intro r

 unfold photo pix; rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
 simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast, roundPose, paceN, add_div]
 congr 1; rw [← mul_div_assoc,mul_comm (_:ℝ) (P.sidesPerTick:ℝ)]
abbrev Samples:= ℕ × List Axis × Option Axis
abbrev spl := TopologicalSpace.denseSeq Vantage
lemma spl_dense: DenseRange spl:= TopologicalSpace.denseRange_denseSeq _
def look (i:Samples) : Vantage:= match i.2.2 with
| some k=> opposeR k (spl i.1)
| none=>spl i.1
def lick (i:Samples)(r:ℕ) : Cover:= match i.2.2 with
| some k=> opposeQ k (P.pix i.2.1 (spl i.1) r)
| none=> P.pix i.2.1 (spl i.1) r
lemma look_for (i:Samples): Tendsto (fun r=> P.photo r (P.lick i r)) atTop (𝓝 (look i)):= by
 rcases i with ⟨n,l,_|j⟩; · exact P.glimmer ..
 apply tendsto_pi_nhds.mpr; intro k
 have h:= tendsto_pi_nhds.mp (P.glimmer l (spl n)) k
 change Tendsto (fun r=> ((opposeQ j (P.pix l (spl n) r) k:ℤ):ℝ)/ (m r)) atTop (𝓝 ((opposeR j (spl n)) k))
 by_cases e:k=j
 · unfold opposeQ opposeR mirrorΩ; simp only [if_pos e,Int.cast_neg, neg_div]; rw [e] at h; exact h.neg
 unfold opposeQ opposeR mirrorΩ; simp only [if_neg e]; exact h
abbrev Sight:= {p: Samples × Samples // look p.1 ≠ look p.2}

def Spots (u:ℕ→ℕ) (x:P.Spectrum0 3): Prop:=∀ p: Sight,Tendsto (fun i=>P.strike (P.lick p.val.1) (P.lick p.val.2) (look p.val.1) (look p.val.2) (u i) x) atTop (𝓝 0)
lemma spots_fee (Z:P.Care Cε) (a:ℕ→ℕ)(t:StrictMono a): ∃ b:ℕ→ℕ, StrictMono b ∧ ∀ᵐ x∂ P.pillars 3,P.Spots (a ∘ b) x:= by
 let T (p:Sight):= P.strike (P.lick p.val.1) (P.lick p.val.2) (look p.val.1) (look p.val.2)
 refine sparse (P.pillars 3) a t T (fun _ _ _=>norm_nonneg _) ?_ (fun i=> P.photo_go Z i.property (P.look_for _) (P.look_for _))
 intro p n; exact (P.mistake_live ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
open Next.Free

open Regis.Head.Brecht
abbrev gloss (d:Vantage):ℂ:=spectrumℓ z' SU.group (moor d)/canonWeight
abbrev factor (s:ℕ):ℂ:=(P.rewardK (P.pointEra s) s:ℂ)/(Real.sqrt (P.dBase s):ℝ)
lemma min_budget:0< min7:=div_pos focus_positive (by norm_num)
lemma gloss_funds (s:ℕ)(d:Vantage):P.wagerQ z' s (moor d)=P.dBase s*gloss d:= by
 have hp : (canonWeight:ℂ)≠0:= Complex.ofReal_ne_zero.mpr focus_positive.ne'
 unfold wagerQ dBase gloss
 rw [Complex.ofReal_mul,Complex.ofReal_pow]
 field_simp
lemma lofty (s:ℕ):0<P.dBase s:= min_budget.trans_le (P.dBase_interval s).1
variable {x:P.Spectrum0 3}{r:ℕ→ℕ}
lemma grade (s:ℕ)(e:0<P.tallWorth s) (X R: Cover): (P.dBase s:ℂ) * (((starRingEnd ℂ) (P.factor s))*(P.factor s)*P.singleState 3 s x (P.centeredQ x s R*P.centeredQ x s X))
     = ((m s):ℂ)^8 *P.pulseQ 3 z' s X R x:=by
 rw [P.lens_price]
 unfold factor; rw [map_div₀,Complex.conj_ofReal,Complex.conj_ofReal]
 let z:ℝ:=m s; let b:ℝ:= P.tallWorth s; let w:ℝ:=Real.sqrt (P.dBase s); have hz:w^2=P.dBase s:= Real.sq_sqrt (P.lofty s).le
 let t:= P.pulseQ 3 z' s X R x
 change (P.dBase s:ℂ)*((↑(z^4/b):ℂ)/↑w*((↑(z^4/b):ℂ)/↑w)*((b:ℂ)^2*t))= (z:ℂ)^8*t
 have hb:(b:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.ne'
 have hw:(w:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (P.lofty s)).ne'
 rw [←hz,Complex.ofReal_pow, Complex.ofReal_div,Complex.ofReal_pow]; field_simp

def paidPix (x:P.Spectrum0 3) (s:ℕ)(X R: Cover):ℂ:= (starRingEnd ℂ) (P.factor s)*(P.factor s)*P.singleState 3 s x (P.centeredQ x s R*P.centeredQ x s X)
lemma paid_sight (H:P.Spots r x)(t:Tendsto r atTop atTop)(i j:Samples)(h: look i ≠ look j): Tendsto (fun k=> P.paidPix x (r k) (P.lick i (r k)) (P.lick j (r k))) atTop (𝓝 (gloss (look i-look j))):= by
 apply Metric.tendsto_nhds.mpr; intro ε e
 let g:=look i - look j
 have hw:=H ⟨(i,j),h⟩
 filter_upwards [t.eventually P.reward_positive, hw.eventually (gt_mem_nhds (mul_pos min_budget e))] with k a b
 let s:=r k; let X:= P.lick i s; let Y':= P.lick j s
 change ‖ (↑(m s):ℂ)^8*P.pulseQ 3 z' s X Y' x - P.wagerQ z' s (moor g)‖ < min7*ε at b
 rw [← P.grade s a.1, P.gloss_funds,←mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (P.lofty s).le] at b
 rw [dist_eq_norm]
 exact lt_of_mul_lt_mul_left (b.trans_le (mul_le_mul_of_nonneg_right (P.dBase_interval _).1 e.le)) (P.lofty _).le

