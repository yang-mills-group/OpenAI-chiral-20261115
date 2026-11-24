import SatinPP.Recoup
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

open QuadClock Preparation.Yoke Yoke.Travel Regis.Head Regis.Head.Brecht
variable (P:Spine) {A C b:ℝ} (x:P.Spectrum0 3) {f r:ℕ}
local notation "Λ"=>P.par
local notation "F%" k:max=>P.pointEra k
local notation "h%" k:max=>P.rewardK (F% k) k
local notation "χ"=> P.pillars 3

def turncost(n:ℕ):ℝ:= (1/2:ℝ)^n
lemma turn_pos(n):0<turncost n:=pow_pos (by norm_num) _
lemma turn_soon:Tendsto turncost atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
/-- One calendar charge; retain synchrony to the master. -/
structure Sprint(A:ℝ)(f r k n:ℕ):Prop where
 depth:F% k < k
 tint:P.Synchrony f (F% k)
 paid:P.reached (F% k) k
 grows:f ≤ F% k
 far:r ≤ k
 bill:P.repeatBill (twiceT (P.baseRoot (F% k)) 3) (F% k)
 book:0<slotFee Λ (F% k)
 quote:0<h% k
 goal:2*(navy (2*n)*lensValue A)*(P.repeatLoss k)≤turncost n/16
private lemma terseP(f:ℕ): twiceT (P.baseRoot f) 3= twiceT (P.plateau f) 3:=by unfold twiceT; simp only [nodeC, Pi.add_apply,Pi.smul_apply]

lemma sprintable(n:ℕ):∀ᶠ k:ℕ in atTop,P.Synchrony f (F% k)→ P.Sprint A f r k n:= by
 let t:=P.future_payment
 let d:=2*(navy (2*n)*lensValue A)
 have h:Tendsto (fun k=>d*P.repeatLoss k) atTop (𝓝 0):=by simpa only [mul_zero] using P.era_complete.const_mul d
 filter_upwards [P.payment_late,P.ready_granule (P.roomy),t.eventually_ge_atTop f,eventually_ge_atTop r,t.eventually (P.offers_plans 3 1 zero_lt_one),t.eventually (P.seat_many 3 1 zero_lt_one),t.eventually P.size_honors,P.reward_positive,h.eventually (ge_mem_nhds (div_pos (turn_pos n) (by norm_num: (0:ℝ)<16)))] with s k v u w p q y z h u₀
 exact ⟨k.2.1,u₀,v,u,w,p.1 _ ((terseP ..).le.trans q),y.1,z.2 _,h⟩

-- spend sparser (spots chosen first)
lemma sprint_route (A:ℝ) (z:P.Care C)
   (t:∃ᶠ s:ℕ in atTop,P.Synchrony f (F% s)):
 ∃ l:ℕ→ℕ,StrictMono l ∧ (∀ᵐ x∂χ,P.Spots l x) ∧ ∀ i,P.Sprint A f r (l i) i:=by
 obtain ⟨u,w,h⟩:=extraction_of_frequently_atTop t
 obtain ⟨k,k',p⟩:=P.spots_fee z u w
 let v:=u ∘ k
 have he(i m:ℕ):∃ j>m,P.Sprint A f r (v j) i:= by

    refine ((eventually_gt_atTop m).and ?_).exists
    filter_upwards [(w.comp k').tendsto_atTop.eventually (P.sprintable (A:=A) (f:=f) (r:=r) i)] with j v' using v' (h _)
 choose a b y using he
 let m:ℕ→ℕ:= Nat.rec (a 0 0) fun i=>a (i+1)
 have h':StrictMono m:=strictMono_nat_of_lt_succ fun i=> b (_+1) (m i)
 exact ⟨v ∘ m, (w.comp k').comp h', p.mono (fun x z i=>(z i).comp h'.tendsto_atTop), fun i=>by cases i<;>exact y _ _⟩
abbrev Sprint.pedal {P:Spine}{k n:ℕ}(m:P.Sprint A f r k n): Pedal P f:= ⟨3, (P.pointEra k,k), P.baseRoot (P.pointEra k), m.bill,m.grows,P.lent_anchor _,m.depth,m.book⟩

abbrev ticket_loss(k v:ℕ)(a:ℕ×ℕ→ℝ) := dist (P.invoiceV x (F% k) k v (a (F% k,k):ℂ)) (P.invoiceV x (F% k) k k 1)
lemma sprint_charge {k n v:ℕ}(m:P.Sprint A f r k n)(y:k ≤ v)
  (a:ℕ×ℕ→ℝ)(h:P.reachP x m.pedal v a A ≤ navy (2*n)):
  P.ticket_loss x k v a ≤ turncost n/16:=by
 let d:=navy (2*n)*lensValue A
 have he:=P.charge_p x m.pedal v a A y (2*n) h
 have hc:=m.depth.le
 change ‖P.stateVox 3 (P.advocate 3 x 3) v (P.cameo 3 (P.baseRoot (F% k)) (a (F% k,k)) hc y (P.lent_anchor _))‖^2≤ (navy (2*n)*(lensValue A*slotFee Λ (F% k)))^2 at he
 rw [P.price_caps,←mul_assoc] at he
 exact (P.compare_distance x y hc _ d (mul_pos (pow_pos (by norm_num) _) (lensBasis A)) m.quote m.paid he m.book).trans m.goal


variable {k n:ℕ} {v:ℕ→ℕ} {a:ℕ→(ℕ×ℕ)→ℝ}
def theaterLimit (_f:ℕ)(r k:ℕ):ℝ:=4*zoomC P.par.R.L^(k-r)
lemma theaterTicket (m:P.Sprint A f r k n) {R:ℕ→Pedal P f}
  (T:AtMile P A C f r x b v a R)
  (y:f<r):
 ∃ u:ℕ→ℝ,(∀ i,|u i| ≤ P.theaterLimit f r k) ∧ ∀ᶠ i:ℕ in atTop,a i (f,r)=u i*a i (P.pointEra k,k):= by
 have h(i)(w:k ≤ v i):|a i (f,r)| ≤ P.theaterLimit f r k * |a i (F% k,k)|:=by
    obtain ⟨s,t,e⟩:=T.cruise i
    exact e.career (f,r) (F% k,k) ⟨le_rfl,y,T.up i⟩ ⟨m.grows,m.depth,w⟩ m.far
 let d:=P.theaterLimit f r k
 have d0:0≤d:=mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans (zoomC_p _)) _)
 let g i:=a i (f,r)
 let t i:=a i (P.pointEra k,k)
 let H i:=if k≤v i then g i/t i else 0
 have e(i)(w:k≤v i):g i=H i*t i:= by
    rw [show H i = g i/t i from if_pos w]
    by_cases p:t i=0

    · have r':|g i|≤d * |t i|:=h i w
      rw [p,abs_zero,mul_zero] at r'
      rw [p,mul_zero]
      exact abs_nonpos_iff.mp r'
    exact (div_mul_cancel₀ _ p).symm
 refine ⟨H,fun i=>?_,(T.fast.tendsto_atTop.eventually_ge_atTop k).mono e⟩
 unfold H; split_ifs with p;swap;· rw [abs_zero];exact d0
 rw [abs_div]
 by_cases r':t i=0
 · rw [r',abs_zero,div_zero];exact d0
 exact (div_le_iff₀ (abs_pos.mpr r')).mpr (h i p)

lemma ScoutAnthem.pull {x:P.Spectrum0 3}(T:ScoutAnthem P x A C f r b v a) {w:ℕ→ℕ}
 (p:StrictMono w): ScoutAnthem P x A C f r b (v ∘ w) (a ∘ w):=by
 obtain ⟨R,h⟩:=T.station
 refine ⟨⟨R,h.fast.comp p,fun i=>h.up _,fun i=>h.cruise _,h.price,fun i=>h.main _,fun n=>p.tendsto_atTop.eventually (h.extra n)⟩,?_⟩
 exact fun j l d e=> (T.earns j l d e).elim (fun B z=>⟨B,p.tendsto_atTop.eventually z⟩)


lemma fineLine {l:ℕ→ℕ}
 (y:f<r)(t:∀ n,P.Sprint A f r (l n) n) 
 (T:ScoutAnthem P x A C f r b v a)
 (H:∀ n,∀ᶠ i:ℕ in atTop,P.reachP x (t n).pedal (v i) (a i) A ≤ navy (2*n)):
 ∃ v' a',ScoutAnthem P x A C f r b v' a' ∧ ∀ n,P.Offering x (P.pointEra (l n)) (l n) v' a' f r (turncost n) := by
 obtain ⟨s,h⟩:=T.station
 choose u z w using fun n=> P.theaterTicket x (t n) h y
 let d n:=P.theaterLimit f r (l n)
 let X(i n):=u n i
 obtain ⟨Y,_,m,e,p⟩:= (isCompact_pi_infinite (ι:=ℕ) (X:=fun _=>ℝ) (fun n=> isCompact_Icc (a:=-d n) (b:=d n))).isSeqCompact (x:=X) (fun i n=>abs_le.mp (z n i))
 refine ⟨v∘m,a∘m,T.pull P e,fun n=>⟨(t n).depth.le,(t n).paid,?_,(t n).tint,?_⟩⟩
 · have H': ∀ᶠ i in atTop,P.ticket_loss x (l n) (v i) (a i)≤turncost n/16:=by
      filter_upwards [H n,h.fast.tendsto_atTop.eventually_ge_atTop (l n)] with i q r' using P.sprint_charge x (t n) r' (a i) q
   exact e.tendsto_atTop.eventually H'
 let c:=P.rewardK f r / h% (l n)

 refine ⟨_,_, (tendsto_pi_nhds.mp p n).const_mul c,?_⟩
 filter_upwards [e.tendsto_atTop.eventually (w n)] with j a₁
 let i:=m j
 change P.rewardK f r * a i (f,r)=(c*u n i)*((h% (l n))*a i (F% (l n),l n))
 have r:= (t n).quote
 unfold c;rw [a₁]
 field_simp

 rfl
