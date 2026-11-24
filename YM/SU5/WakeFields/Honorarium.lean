import YM.SU5.WakeFields.Ensembles


set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Filter
open Function
open Metric
open MeasureTheory
open Lattice Cube Lat Skye Lifted EmberWind
open Py Py.Rate LocalLimit FullBill Preparation Yoke Journey
open Satin Fock
open Ballad
open scoped Topology BigOperators Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Onyx (riseX)
open YM.Stationary (Gaia)

namespace Resolving
open Jewel Jewel.Program
open Regis Regis.Head.Brecht Regis.Circuit
open Hiro.Crossing
open Hiro (shotL)
open EmberWind.MixedCards MixedCards.Receipt
open Scree

variable (P:Spine) {J:Type*} [Fintype J] (X: ℕ → J→ Staff) (L : List J) (D:J→MixedCards.Ticket)
variable {β: ℕ→ℝ} (f:ℕ→ℕ) (p : Tuned P f β) {I A b:ℝ} (hp:0 < I) (ha:0<A) (r:ℕ→ℕ)
variable {Q:Spine.Register P}{E:ℝ}{Mc:ℕ} (W:Spine.PreparedInvestment P Q E Mc)
local notation "Y" => P.run
local notation "Z" => P.calibration
local notation "ι" => physicalPeriod P f
local notation "ν" => physicalCut P f
local notation "κ" t:max => Jewel.κFix β t
local notation "δ" s:max A:max => sPow P.par s A
local notation "q"=> P.par.K.j
local notation "Γ" x:max => (side Y (ι x.2) x.1)
local notation "ℳ" x:max => (RootBook Y (ι x.2) (ν x.2) x.1).J.M
local notation "ph" s:max => Pressure.temp (Vale.hat P.par.R.L P.par.x s)
-- reader stamp and list product, stamps also counted singly. Order.
abbrev scoreActor (s r:ℕ) (A ρ : ℝ) (i:Staff) (w:Ticket) : Papal.Weaver:= (sPow P.par s A:ℂ)^(volumeFee w) • MixedCards.actor i w ρ r (ph s)
def stampL (s r:ℕ) (A ρ:ℝ) (X:J→Staff) (D:J→Ticket) (L:List J) : Family Z :=
    (L.map (fun i=> Papal.household Z (scoreActor P s r A ρ (X i) (D i)))).prod

lemma stamp_register (s r w:ℕ)(A ρ:ℝ)(X:J→Staff) (h:∀ i∈L,(X i).Pays r w) : TestFamily Z true (stampL P s r A ρ X D L) ∧ CovCover Z (stampL P s r A ρ X D L):=by
  induction L with
  | nil=> exact ⟨ TestFamily.oneT, covariant_one _⟩
  | cons i L ih=>
    let S := (X i); let b'D(t:Ticket):= scoreActor P s r A ρ (X i) t
    have t (u) : TestFamily Z true (Papal.household Z (b'D u))∧ CovCover Z (Papal.household Z (b'D u)):= by
      cases u with
      | none=> have f:=h i List.mem_cons_self
               refine ⟨?_,?_⟩
               · exact (aux_test (Staff.letterBudget S ρ Z (ph s) f)).scale _ -- tune
               exact covariant_scale _ (Staff.registration S ρ (ph s) Z f) _
      | some u=> let q':= (matter_voice S u).hushed ((sPow P.par s A:ℂ)^3)
                 exact ⟨aux_test ((q'.1.narrow _).widen), fun _=> q'.2 _⟩
    have H:= ih fun i w=> h i (List.mem_cons_of_mem _ w)
    exact ⟨ (t (D i)).1.mul H.1, (covariant_parts _ (t _).2 H.2).2⟩
lemma stampMany (s r:ℕ) (A ρ:ℝ)(X:J→ Staff) : stampL P s r A ρ X D L=(sPow P.par s A:ℂ)^(scaleFee D L) • Papal.household Z (concert X D L ρ r (ph s)):=by
  induction L with
  | nil=> rw [show scaleFee D []=0 from rfl,pow_zero,one_smul]; rfl
  | cons i L ih=>
    let a:ℂ:= sPow P.par s A; let q':=ph s; let p:= Papal.household Z (MixedCards.actor (X i) (D i) ρ r q'); let h:= Papal.household Z (concert X D L ρ r q'); change (a^(volumeFee (D i)) • p) * stampL P s r A ρ X D L=a^(volumeFee (D i)+scaleFee D L) • (p*h)
    rw [ih,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,pow_add]; -- check
lemma readBill (s r m n:ℕ)(A ρ:ℝ)(X:J→ Staff) :
    sharp Y P.large s m n (stampL P s r A ρ X D L) = (sPow P.par s A:ℂ)^ (scaleFee D L) * compass Y m n s (concert X D L ρ r (ph s) (side Y m s)) := by
  rw [stampMany,sharp_scale]; change _*compass Y m n s (expSrc Y s m P.large _) = _; rw [lift_book]

def seatsPaid (P:Spine)(X:J→ Staff)(I:ℝ)(r s:ℕ)(V:Side): Prop:=
    ∃ (w e:ℕ) (o: Seat V),(∀ i,(X i).Pays r w)∧(∀ i,(X i).tenancy V r Staff.clearance e o) ∧ (e:ℝ) ≤ sPow P.par s I ∧ (w:ℝ) ≤ sPow P.par s I
include p W hp
-- stays against compass which IS the mean price. Uniform in MixedCards.actor, r, and amplitude. scale AFTER using sails.
lemma ensemble_bound (A:ℝ) : ∀ᶠ i in towerLimit, ∀ (X:J→ Staff) (D:J→MixedCards.Ticket) {r:ℕ} {ρ:ℝ}, |ρ| ≤2*bornQ P.par i.1 → seatsPaid P X I r i.1 (Γ i) →
    ‖sharp Y P.large i.1 (ι i.2) (ν i.2) (stampL P i.1 r A ρ X D L) -
         (sPow P.par i.1 A:ℂ)^ (scaleFee D L) * costMany Y i.1 (ι i.2) (ν i.2) X D L ρ‖ ≤ scaledBill P A (scaleFee D L) i.1 := by
  have H:= course Y P.law P.history W.investment.choose_spec W.dispatch W.rocky.merit hp L
  rw [towerLate]; filter_upwards [H] with s v
  filter_upwards [(show StrictMono f from Pooling.up p).tendsto_atTop.eventually v] with n w X D r ρ h H
  let i:= ι n; let k:= ν n; let a:ℝ:= δ s A
  obtain ⟨w',e,o,x,u,t,g⟩:= H
  have hv : ‖(a:ℂ)^ (scaleFee D L)‖ = a^(scaleFee D L) :=by
    rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (BProof.coin_pos ..).le]
  rw [readBill,←mul_sub,norm_mul,hv]; exact mul_le_mul_of_nonneg_left (w X D x u t g h) (pow_nonneg (BProof.coin_pos ..).le _)

variable (F:J→PlaqAxes) (K:J→Twah.DirSpin) (U:J→Gaia)(z:J→Gaia)
variable (t:∀ i, ∀ᶠ s in atTop, (X s i).face.2 = F i) (w:∀ i,Tendsto (fun s=> riseX (sPow P.par s A) (X s i).face.1) atTop (𝓝 (U i)))
variable (u:∀ i,∀ᶠ s in atTop,(X s i).spin = K i) (g:∀ i,Appoint P.par A (fun s=> (X s i).u) (z i))
variable (h: ∀ i j,z i=z j→ ∀ᶠ s in atTop,(X s i).u=(X s j).u)
include ha t w u g h
theorem pricedMany (W':∀ᶠ i in towerLimit,seatsPaid P (X i.1) I (r i.1) i.1 (Γ i))(m:L.Pairwise (fun i j=> U i ≠ U j)) :
    MeanShot P f (fun s=> stampL P s (r s) A (κ s) (X s) D L) (tariff L D F K U z):=by
  let Z'(x:ℕ×ℕ):=costMany Y x.1 (ι x.2) (ν x.2) (X x.1) D L (κ x.1); let T (x:ℕ×ℕ):ℂ:= (δ x.1 A:ℂ)^ (scaleFee D L); let B (x:ℕ×ℕ):=sharp Y P.large x.1 (ι x.2) (ν x.2) (stampL P x.1 (r x.1) A (κ x.1) (X x.1) D L)
  have hv: Tendsto (fun x=> B x-T x * Z' x) towerLimit (𝓝 0):= by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (.of_forall fun i=>norm_nonneg _) _ (billTends P A (scaleFee D L)); filter_upwards [ensemble_bound P L f p hp W A, W'] with i ht f
    exact ht (X i.1) D (paidFix Y p P.large i.1) f
  apply mean_grant P f (Pooling.up p)
  · rw [towerLate] at W'; filter_upwards [W'] with s v
    obtain ⟨n,w,e,o,x,_⟩:= v.exists; exact stamp_register P L D s _ w _ (κ s) (X s) (fun i _=> x i)
  have p':=hv.add (tariff_limit P X L D f p ha F K U z t w u g h m); rw [zero_add] at p'; exact p'.congr fun x=> sub_add_cancel ..

omit hp W p ha t w u g h
-- occupancy certificate
lemma fuel_open (r w:ℕ)(b:ℝ)(hl:0≤b)(g:A<I) (p:0<I): ∀ᶠ s in atTop,∀ X:J→ Staff, (∀ i,(X i).Pays r w) → (∀ i, ‖riseX (δ s A) (X i).hub‖ ≤ b) → ∀ n, seatsPaid P X I r s n := by
  filter_upwards [payBump P b (r+Staff.clearance+8) hl g p,grow_e I w p P.par,bumped (A:=A) P b] with s v h H X hX y n
  exact ⟨w,_,wrap (More n) 0,hX,fun i=>nearTenancy _ (H _ (y i)) _ r,v,h⟩
variable (x : ℕ→ J→ Cover)
variable (G:∀ i,Appoint P.par A (fun s=> x s i) (U i))
include ha G
lemma fuelAll (s₀:ℕ) (h:4≤ s₀) (v:A<I) : ∀ᶠ s:ℕ in atTop, ∀ n,
    seatsPaid P (fun i=> adjacent (x s i) (F i) (K i)) I s₀ s n := by
  obtain ⟨k,V,g⟩:= ((eventually_all.mpr (show ∀ i, ∀ᶠ v:ℝ in atTop, ‖U i‖<v from fun i=> eventually_gt_atTop ‖U i‖)).and (eventually_ge_atTop (0:ℝ))).exists
  have hK : ∀ᶠ s in atTop,∀ i, ‖riseX (δ s A) (nodeC (x s i))‖ ≤ k:= eventually_all.mpr (fun i=> (G i).norm.eventually (ge_mem_nhds (V i)))
  filter_upwards [fuel_open (J:=J) P s₀ 0 k g v (ha.trans v),hK] with s v hV
  exact v (fun i=> adjacent (x s i) (F i) (K i)) (fun i=>compRoom _ _ _ h) hV

include p W
theorem paidAdjacents (h: ∀ i j,U i=U j→ ∀ᶠ s in atTop, x s i=x s j) (s₀:ℕ)(hn:4≤ s₀) (m:L.Pairwise (fun i j=> U i ≠ U j)) :
    MeanShot P f (fun s=> stampL P s s₀ A (κ s) (fun i=> adjacent (x s i) (F i) (K i)) D L) (tariff L D F K U U):=
  pricedMany P _ L D f p (show 0<A+1 by linarith) ha (fun _=> s₀) W F K U U (fun _=>.of_forall fun _=>rfl) G (fun _=>.of_forall fun _=>rfl) G h ((towerLate _).2 ((fuelAll P ha F K U x G s₀ hn (lt_add_one A)).mono fun s v=>.of_forall fun _=>v _)) m
#print axioms paidAdjacents
end Resolving
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
