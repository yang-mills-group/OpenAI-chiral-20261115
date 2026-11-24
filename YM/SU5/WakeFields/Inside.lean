import YM.SU5.WakeFields.StarsAhead
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 2500
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
open Function Filter Metric Cube Lat Lattice Satin Fock Finset MeasureTheory
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Classical
open Py Py.Rate LocalLimit FullBill Preparation Yoke Yoke.Shuttle
open Lifted EmberWind EmberWind.Staff EmberWind.MixedCards MixedCards.Receipt
open Papal (household)
open Ballad
open Tapestry Journey Heat
open Jewel
open YM.Stationary (Gaia)
open YM.WakeFields
attribute [local instance] opCStarAlgebra
local notation "z" => (3:Axis)
variable (P:Spine) {K:P.Register}{M:ℕ}{E:ℝ}(X:Spine.PreparedInvestment P K E M) {β:ℕ→ℝ}(f:ℕ→ℕ)(V:Tuned P f β){A:ℝ}(p:0<A)
open CrossMoment
local notation "α" => Lead.Clan
local notation "Ω" => P.Test
variable (u:ℕ→ Fin 4→ Cover) (U:∀ i, Appoint P.par A (fun s=> u s i) (spot4 i))
variable (s:ℕ) (a b:Lead.Clan)

abbrev localTest (L:List (Fin 4))(D:Fin 4→MixedCards.Ticket)(s:ℕ) := letterTest L D P s 4 (κFix β s) A le_rfl (u s)
abbrev localPrice (L:List (Fin 4))(D:Fin 4→MixedCards.Ticket) := plaque L D spot4
local notation "Υ" L:max D:max => localTest (β:=β) (A:=A) P u L D
local notation "T" => trajectory
local notation "Q" => polarization
local notation "𝕍" => spot4
abbrev claimL (β:ℕ→ℝ)(A:ℝ) (s:ℕ) : P.Test:= localTest (β:=β) (A:=A) P u [0,1] (fun _=>none) s
abbrev claimR_ind (β:ℕ→ℝ)(A:ℝ)(s:ℕ)(a b:Lead.Clan): P.Test:=localTest (β:=β) (A:=A) P u [2,3] (playT a b) s
abbrev claimR (β:ℕ→ℝ)(A:ℝ) (s:ℕ) : P.Test:= ∑ a:α,∑ b:α,claimR_ind P u β A s a b

lemma claim_eq (β)(A) : localTest (β:=β) (A:=A) P u [0,1] (playT a b) s=claimL P u β A s:= Subtype.ext rfl
lemma veg (β:ℕ→ℝ)(A:ℝ) :
      (claimL P u β A s).val= firstPair P u β A s ∧ ∀ a b,
            (claimR_ind P u β A s a b).val= second_for P u A a b s:= by
  let a:α:= ⟨0,true⟩; let v:= standby P u s β A a a; exact ⟨v.1.symm,fun _ _=>(standby P u s β A _ _).2.1.symm⟩
lemma bill_join (β:ℕ→ℝ)(A:ℝ): claimL P u β A s * claimR_ind P u β A s a b=localTest (β:=β) (A:=A) P u [0,1,2,3] (playT a b) s:= by
  apply Subtype.ext; exact (congrArg₂ (·*·) (veg P u s β A).1 ((veg P u s β A).2 a b)).trans (standby P u s β A a b).2.2
lemma vegetate (β:ℕ→ℝ)(A:ℝ)(s:ℕ): (claimR P u β A s).val=secondPair P u A s:= by
  rw [second_all]; change (screenHall P.calibration).val (∑ i,∑ j,claimR_ind P u β A s i j)= _
  simp_rw [map_sum, Finset.sum_apply]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>(veg ..).2 i j

lemma second_phys (β:ℕ→ℝ)(A:ℝ)(s:ℕ) : Six.PureMatter P.calibration (claimR P u β A s):=by
  unfold Six.PureMatter; rw [vegetate]; exact fun _ _ _=> second_pure ..

-- poll even on other family combinations (use same countable menu). Then get confrontation estimates FOR A SELECTED x on that subgroup.
include X V p U
lemma tenureP (L:List (Fin 4))(t:L.Nodup)(D:Fin 4→MixedCards.Ticket) : Spine.WakePoll P (Υ L D) (localPrice L D):= paysPoll L u D P 4 le_rfl f V p X 𝕍 U (fun i j e=> allSpots e ▸ (.of_forall (fun _=>rfl))) (t.imp fun {i j} => spot_non i j)
universe μ
omit X V p U
variable {M' : ℕ→ℕ}{x:P.Spectrum0 3}
def agency (A:ℝ)(β:ℕ→ℝ)(M':ℕ→ℕ)(x:P.Spectrum0 3) :=
    ∀ (L:List (Fin 4))(t:L.Nodup)(D:Fin 4→MixedCards.Ticket), Tendsto (fun n=> P.singleState 3 (M' n) x (localTest (β:=β) (A:=A) P u L D (M' n))) atTop (𝓝 (localPrice L D))
-- choose hold for p0 & p2 (left- to right- rectangle, not same internal pair). leave additional polls affordable; U always may refine later.
include X V p U
lemma accounting (U': Spine.QualifiedWakeReadout.{μ} P K)
    (M:ℕ→ℕ)(w:StrictMono M) {J:Type}[Countable J] (R:J→ℕ→P.Test) (Z:J→ℂ)(pR:∀ i,Spine.WakePoll P (R i) (Z i)) :
  ∃ c : ℕ→ℕ, StrictMono c ∧ ∀ H:P.Spectrum0 3→Prop,(∀ᵐ x∂P.pillars 3,H x) →
    ∃ x, H x ∧ Spine.JointTuple.{μ} P K x ∧ Spine.HoldRead P A (M ∘ c) x (spot4 0) (spot4 2) (fun s=>u s 0) (fun s=> u s 2)∧
       (agency P u A β (M ∘ c) x) ∧ ∀ i,Tendsto (fun r=>P.singleState 3 (M (c r)) x (R i (M (c r)))) atTop (𝓝 (Z i)):= by
  let I:= {L:List (Fin 4) // L.Nodup} × (Fin 4 → MixedCards.Ticket)
  let W(I':I):= Υ I'.1.val I'.2
  let t(I':I):=localPrice I'.1.val I'.2
  have hz(i:J⊕I) : Spine.WakePoll P (Sum.elim R W i) (Sum.elim Z t i) := by cases i; exact pR _; next u=> exact tenureP P X f V p _ U u.1.val u.1.property u.2
  obtain ⟨c,v,H⟩:= U' A p (𝕍 0) (𝕍 2) (fun s=>u s 0) (fun s=>u s 2) (J⊕I) M w ⟨U _,U _,fun i=> (spot_non 0 2 (by decide) i).elim⟩ _ _ hz
  refine ⟨c,v,fun Qh V'=>?_⟩; obtain ⟨x,e,s,f,d⟩:=H Qh V'; exact ⟨x,e,s,f,(fun i v D=> d (.inr (⟨i,v⟩,D))),fun i=>d (.inl i)⟩

omit X V p U
abbrev contrastC (u : ℕ→ Fin 4→ Cover)(β:ℕ→ℝ)(A:ℝ)(x:P.Spectrum0 3)(n:ℕ):ℂ:= P.selectedPanel (claimL P u β A n) (claimR P u β A n) n x
lemma veget_in (v:agency P u A β M' x) : Tendsto (fun n=> contrastC P u β A x (M' n)) atTop (𝓝 wakeForceBill):=by
  let q(n:ℕ):= P.singleState 3 (M' n) x; let L(n):= claimL P u β A (M' n); let R (n):=claimR P u β A (M' n); let V (n a b):=claimR_ind P u β A (M' n) a b
  let a:α:= ⟨0,true⟩; let F:=finalV T Q 𝕍 𝕍 0 1 2 3; let Y:=payStaff T Q 𝕍 𝕍 0 1; let D:=allMatter Q 𝕍 2 3; let S:=playT a a
  have he: Tendsto (fun n=> q n (L n)) atTop (𝓝 Y):= by
     have hv:= v [0,1] (by decide) S; unfold S at hv; simp_rw [claim_eq] at hv; rw [show localPrice [0,1] (playT a a)=Y from mixPrice T Q 𝕍 𝕍 (playT a a) 0 1 rfl rfl] at hv; exact hv
  have hw: Tendsto (fun n=> q n (R n)) atTop (𝓝 D):=by
     unfold R claimR D; rw [←pure_combine]; simp_rw [map_sum]; apply tendsto_finsetSum; intro a _; apply tendsto_finsetSum; intro b _
     rw [← qprice T Q 𝕍 𝕍 (playT a b) 2 3 a b rfl rfl]; exact v [2,3] (by decide) (playT a b)
  have hj:Tendsto (fun n=> q n (L n*R n)) atTop (𝓝 F):=by
     unfold L R claimR F; rw [←fleet_price]; simp_rw [mul_sum,map_sum,bill_join]; apply tendsto_finsetSum; intro a _; apply tendsto_finsetSum; intro b _
     rw [← bothPrice T Q 𝕍 𝕍 (playT a b) 0 1 2 3 a b rfl rfl rfl rfl]; exact v [0,1,2,3] (by decide) (playT a b)
  unfold wakeForceBill; rw [←interference_bill]; exact hj.sub (he.mul hw)

-- durable under width progression. extraction pin -> any sufficiently high rung in that sequence. test first still mixed.
open PhaseChoice Reconstruction Selected
lemma still_holding (β)(A:ℝ)(s:ℕ)(t:PairedReport P A u s β f)(x:P.Spectrum0 3) (n:ℕ) :
    P.selectedPanel (P.conveying s n (claimL P u β A s)) (P.conveying s n (claimR P u β A s)) (s+n) x=contrastC P u β A x s:=by
  let L:=claimL P u β A s; let R:=claimR P u β A s; let e:=P.conveying s n
  have he : e (L*R) = e L*e R:= by
      apply Subtype.ext; change later P s n (L.val*R.val)= later P s n L.val * later P s n R.val
      rw [(veg ..).1,vegetate]; apply woven_product _ _ P.history.circuit s n t.left.1 t.rightS.1
      have V:= apert_pos P s A; refine separatedPhys (supported_iff.mpr t.left.2.2) (supported_iff.mpr t.rightS.2.2) (Disjoint.preimage (fun x:RSpace => fun j:Axis => x j / 2) ?_); apply Set.disjoint_left.mpr; intro y h k; have hk:= (t.gap y h y k).1 2; linarith only [V,hk]
  have ht(f:P.Test): P.singleState 3 (s+n) x (e f)=P.singleState 3 s x f:= congrArg (P.chi 3 x) (P.carryReads 3 s n f)
  unfold Spine.selectedPanel; change P.singleState z (s+n) x (e L * e R)-_ = _; rw [←he]; unfold contrastC Spine.selectedPanel; simp_rw [← ht]; rfl -- likely expanding all problematic

include X V p U
theorem holdsAt (h : agency P u A β M' x) (hq: StrictMono M') : ∀ᶠ i:ℕ in atTop, let s:= M' i
              PairedReport P A u s β f ∧ ∀ n:ℕ,
     ‖wakeForceBill‖/2< ‖P.selectedPanel (P.conveying s n (claimL P u β A s)) (P.conveying s n (claimR P u β A s)) (s+n) x‖:= by
  filter_upwards [hq.tendsto_atTop.eventually (billAtSpots P f V p X u U), (veget_in P _ h).norm.eventually (lt_mem_nhds (half_lt_self opening))] with i p h s
  exact ⟨p,fun n=> (still_holding P f u _ A (M' i) p x n).symm ▸ h⟩

#print axioms agency
#print axioms accounting
#print axioms holdsAt
omit X V p U
lemma region02 : (spot4 0) 3 < spot4 2 3 ∧ spot4 0 2 <spot4 2 2:=by
 change (-5/2:ℝ)*1 < 3/2*1 ∧ (-5/2:ℝ)*6 < 3/2*6; norm_num
-- no comparator equiv. keep proofs same.
theorem certifiedEvent (J:TintDemand)(Mc:ℕ) : ∃ (P:Spine)(K:P.Register)(E:ℝ),
   Spine.PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
   Spine.QualifiedWakeReadout.{μ} P K ∧ P.PhysicalWakeGram ∧
   ∀ (h:ℕ→ℕ), StrictMono h → ∀ (v: ℕ)(d:0<v)(x: Cover)(A:ℝ)(b:0<A),
   ∃ c β u t, StrictMono c ∧ Tuned P (h ∘ c) β ∧
     (∀ i, Appoint P.par A (fun s=>u s i) (spot4 i))∧ (∀ s i (j:Axis), (v:ℤ)∣ u s i j-x j) ∧ StrictMono t ∧
     ∀ H:P.Spectrum0 3→Prop,(∀ᵐ x∂P.pillars 3,H x) →∃ x,H x∧ Spine.JointTuple.{μ} P K x ∧
       P.HoldRead A (h ∘ t) x (spot4 0) (spot4 2) (fun s=> u s 0) (fun s=>u s 2)∧ agency P u A β (h∘t) x ∧
       ∀ᶠ i:ℕ in atTop, let s:= h (t i)
              PairedReport P A u s β (h ∘ c) ∧ ∀ n:ℕ,
     ‖wakeForceBill‖/2< ‖P.selectedPanel (P.conveying s n (claimL P u β A s)) (P.conveying s n (claimR P u β A s)) (s+n) x‖ := by
  obtain ⟨P,K,E,p,X,b,V,F⟩:= wakeElectionWithStory.{μ} J Mc; refine ⟨P,K,E,p,X,b,V,fun h g v d x A t=>?_⟩
  obtain ⟨c,L,T₀,e,f⟩:= F h g; obtain ⟨W,s,H,B⟩:= f A t v d x
  let u : Unit→ ℕ→ P.Test:= fun _ => localTest (β:=T₀) (A:=A) P W [] (fun _=>none)
  let z' : Unit→ℂ:= fun _=> localPrice [] (fun _=>none)
  obtain ⟨f,Qf,Z⟩:= accounting P p _ e t _ H b h g u z' (fun i=> tenureP P p _ e t _ H [] (by simp) _)
  refine ⟨c,T₀,W,f,L,e,H,s,Qf,fun R W=>?_⟩; obtain ⟨x,v,s,E,y,_⟩:= Z R W; exact ⟨x,v,s,E,y,holdsAt P p _ e t _ H y (g.comp Qf)⟩
#print axioms certifiedEvent
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
