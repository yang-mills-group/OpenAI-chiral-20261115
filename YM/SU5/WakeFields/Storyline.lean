import YM.SU5.WakeFields.Jacobian


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
open CrossMoment
local notation "J₀" => Fin 4
local notation "Ho" => Lead.Clan
open Finset PhaseChoice Reconstruction
open Tapestry
open Papal (household)
include p

lemma axSharp : ∀ᶠ x in towerLimit, Ferry Y x.1 (ι x.2) (ν x.2):= (towerLate _).2 (.of_forall fun s => pathPaidFixed P f s (Pooling.up p))
lemma plusMean {x y:ℕ→ Family P.calibration} {a b:ℂ} (t:MeanShot P f x a)(u:MeanShot P f y b): MeanShot P f (x+y) (a+b):= by
  have hf : ∀ᶠ i in towerLimit, sharp Y P.large i.1 (ι i.2) (ν i.2) ((x+y) i.1)=
        sharp Y P.large i.1 (ι i.2) (ν i.2) (x i.1)+sharp Y P.large i.1 (ι i.2) (ν i.2) (y i.1) := by
     filter_upwards [firstTends.eventually t.registered,firstTends.eventually u.registered,axSharp P f p] with i h t b; exact sharp_plus Y P.large _ h.1 t.1 b
  exact mean_grant P f (Pooling.up p) ((t.registered.and u.registered).mono (fun i h=> ⟨h.1.1.add h.2.1,(covariant_parts _ h.1.2 h.2.2).1⟩)) ((t.approved.add u.approved).congr' (hf.mono (fun i f=> f.symm)))
lemma noMean : MeanShot P f 0 0:=by
  apply mean_grant P f (Pooling.up p) (.of_forall fun i=> ⟨TestFamily.zeroT,covariant_zero _⟩)
  apply tendsto_const_nhds.congr; intro i
  have h :∀ s m n, sharp Y P.large s m n 0=0:=fun s m n=>by simpa using sharp_scale Y P.large s (0:Family Z) 0 m n
  exact (h ..).symm

lemma addAllMean {J : Type*} (S:Finset J) (F:J→ ℕ→Family Z) (x:J→ℂ) (h:∀ i∈ S, MeanShot P f (F i) (x i)): MeanShot P f (∑ i∈ S,F i) (∑ i∈ S,x i):= by
  induction S using Finset.induction_on with| empty=> rw [sum_empty,sum_empty]; exact noMean P f p| @insert i S hv ih=> rw [sum_insert hv,sum_insert hv]; exact plusMean P f p (h i (mem_insert_self ..)) (ih fun i v=> h i (mem_insert_of_mem v))
omit p
variable (u:ℕ→ Fin 4→ Cover) (g:∀ i, Appoint P.par A (fun s=> u s i) (spot4 i))
local notation "mask" => polarization
local notation "face4" => trajectory
abbrev speakU (u:ℕ→ Fin 4→ Cover) (s:ℕ) (i:Fin 4) : Staff := adjacent (u s i) (trajectory i) (polarization i)
abbrev playT (a b:Ho): Fin 4→ MixedCards.Ticket := ![none,none,some a,some b]
abbrev firstV (β:ℕ→ℝ)(A:ℝ) (i:Fin 4) (s:ℕ) : Family Z:= household Z (scoreActor P s 4 A (Jewel.κFix β s) (speakU u s i) none)
abbrev secondV (A:ℝ) (i:Fin 4)(a:Ho)(s:ℕ) : Family Z:= household Z (scoreActor P s 4 A 0 (speakU u s i) (some a))
abbrev firstPair (β:ℕ→ℝ)(A:ℝ) := firstV P u β A 0* firstV P u β A 1
abbrev secondS (A:ℝ)(i:Fin 4):= ∑ a:Ho,secondV P u A i a
abbrev second_for (A:ℝ)(a b:Ho): ℕ→Family Z:= secondV P u A 2 a * secondV P u A 3 b
def secondPair (A :ℝ) := secondS P u A 2*secondS P u A 3
lemma second_all (A:ℝ) : secondPair P u A = ∑ i:Ho,∑ j:Ho, second_for P u A i j:= by unfold secondPair second_for secondS; simp_rw [sum_mul,mul_sum]
lemma second_pure (A:ℝ)(s m)(x y) : secondPair P u A s m x= secondPair P u A s m y:=by
 rw [second_all]; simp_rw [Finset.sum_apply]; rfl
lemma standby (s:ℕ)(β:ℕ→ℝ)(A:ℝ)(a b:Ho) :
 let f := fun L=> stampL P s 4 A (Jewel.κFix β s) (speakU u s) (playT a b) L
 let A' := firstPair P u β A s
 let B := second_for P u A a b s
 A'=f [0,1] ∧ B=f [2,3] ∧ A'*B=f [0,1,2,3] := by
 intro f A' B;
 have h₁:A'=f [0,1]:=by unfold f stampL; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl
 have h₂:B=f [2,3]:=by unfold f stampL; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl
 exact ⟨h₁,h₂,(congrArg₂ (·*·) h₁ h₂).trans (by unfold f; rw [show ([0,1,2,3]:List (Fin 4))=[0,1]++[2,3] from rfl]; unfold stampL; rw [List.map_append,List.prod_append])⟩ -- nth?
include ha W p g
lemma storyline (L:List (Fin 4))(n:L.Nodup)(a b:Ho) : MeanShot P f (fun s=> stampL P s 4 A (κ s) (speakU u s) (playT a b) L)
               (tariff L (playT a b) trajectory polarization spot4 spot4):=
 paidAdjacents P L _ f p ha W face4 mask spot4 u g (fun i j h=> allSpots h ▸ (.of_forall fun _=> rfl)) 4 le_rfl (n.imp (fun {i} {j} (f : _)=> spot_non i j f)) -- implicit Pairwise, fix
lemma individual (a b:Ho) : MeanShot P f (firstPair P u β A) (payStaff face4 mask spot4 spot4 0 1) ∧
         MeanShot P f (second_for P u A a b) (paysMatter mask spot4 2 3 a b)∧
         MeanShot P f (firstPair P u β A * second_for P u A a b) (duetPrice face4 mask spot4 spot4 0 1 2 3 a b):=by
  let q₀:= playT a b; let X (L):=fun s=>stampL P s 4 A (κ s) (speakU u s) q₀ L
  refine ⟨?_,?_,?_⟩
  · rw [←mixPrice face4 mask spot4 spot4 q₀ 0 1 rfl rfl,show firstPair P u β A=X [0,1] from funext fun s=>(standby P u s β A a b).1]
    exact storyline P f p ha W u g _ (by decide) a b
  · rw [←qprice face4 mask spot4 spot4 q₀ 2 3 a b rfl rfl, show second_for P u A a b=X [2,3] from funext fun s=>(standby P u s β A a b).2.1]
    exact storyline P f p ha W u g _ (by decide) a b
  rw [←bothPrice face4 mask spot4 spot4 q₀ 0 1 2 3 a b rfl rfl rfl rfl,show firstPair P u β A * second_for P u A a b=X [0,1,2,3] from funext fun s=>(standby P u s β A a b).2.2]
  exact storyline P f p ha W u g _ (by decide) a b

theorem forces_unselected :
    MeanShot P f (firstPair P u β A) (payStaff face4 mask spot4 spot4 0 1) ∧
    MeanShot P f (secondPair P u A) (allMatter mask spot4 2 3)∧
    MeanShot P f (firstPair P u β A * secondPair P u A) (finalV face4 mask spot4 spot4 0 1 2 3)∧
    Tendsto (fun s=> averageCredit P s (firstPair P u β A s) (secondPair P u A s)) atTop (𝓝 wakeForceBill)∧
    Tendsto (fun i:ℕ × ℕ=> confirmedCredit P i.1 (ι i.2) (ν i.2) (firstPair P u β A i.1) (secondPair P u A i.1)) towerLimit (𝓝 wakeForceBill):=by
  let x:= firstPair P u β A; let y:= secondPair P u A; let V:= finalV face4 mask spot4 spot4 0 1 2 3; let R:=payStaff face4 mask spot4 spot4 0 1; let S:=allMatter mask spot4 2 3
  have H(a b:Ho):=individual P f p ha W u g a b
  let a:Ho:= ⟨0,true⟩; have U:= (H a a).1
  have F: MeanShot P f y S:=by unfold y S; rw [←pure_combine,second_all]; exact addAllMean P f p _ _ _ fun i _=> addAllMean P f p _ _ _ fun j _=> (H i j).2.1
  have G: MeanShot P f (x*y) V:=by unfold y V; rw [←fleet_price,second_all, mul_sum]; simp_rw [mul_sum]; exact addAllMean P f p _ _ _ fun i _=> addAllMean P f p _ _ _ fun j _=> (H i j).2.2
  refine ⟨U,F,G,?_⟩; unfold wakeForceBill; rw [←interference_bill]; exact ⟨G.realized.sub (U.realized.mul F.realized), G.approved.sub (U.approved.mul F.approved)⟩

#print axioms forces_unselected

omit ha W p g
open EmberWind.Staff
open CF.Pannier.Chancel
local notation "D_" s:max => apertureScale P A s

-- Holds & Rent companion.
abbrev wheelS (s:ℕ) (i:J₀) : Finset Cover:= skyDeck (nodeC (u s i)) 12
lemma arose {s S} {U V : Set RSpace} {x} (h: HeldAt P s U x S) (w:U ⊆ V) : HeldAt P s V x S:=⟨h.1,h.2.1,h.2.2.trans w⟩
lemma pieceMore {s S T} {x y} {U}
    (h:HeldAt P s U x S)(v:HeldAt P s U y T): HeldAt P s U (x*y) (S∪T):=
 ⟨(h.1.mono subset_union_left).mul (v.1.mono subset_union_right), (covariant_parts _ h.2.1 v.2.1).2, silhouette_union ▸ Set.union_subset h.2.2 v.2.2⟩
lemma potential (d:ℝ)(p:0<d)(i j:J₀)(V:factorT i≤factorT j): region_ d i i ⊆ region_ d i j ∧ region_ d j j ⊆ region_ d i j := ⟨enlargeRow d _ _ _ _ p le_rfl V,enlargeRow d _ _ _ _ p V le_rfl⟩
lemma secondOK (s:ℕ)(i:J₀)(A:ℝ) : secondS P u A i s∈ observ P.calibration (wheelS u s i) false:=by
 unfold secondS; rw [Finset.sum_apply]; refine Subalgebra.sum_mem _ fun a _=> ?_
 let S:= speakU u s i; let b:= (matter_voice S a).hushed ((δ s A:ℂ)^3)
 have t: {S.xo} ⊆ wheelS u s i:= Finset.singleton_subset_iff.mpr (owns _ _)
 exact ⟨((b.1.narrow _).mono t),fun _=> b.2 _⟩

structure PairedReport (A:ℝ)(u:ℕ→ Fin 4→ Cover) (s:ℕ) (β:ℕ→ℝ) (f:ℕ→ℕ) : Prop where
 left : HeldAt P s (region_ (apertureScale P A s) 0 1) (firstPair P u β A s) (wheelS u s 0 ∪ wheelS u s 1)
 rightS : HeldAt P s (region_ (apertureScale P A s) 2 3) (secondPair P u A s) (wheelS u s 2 ∪ wheelS u s 3)
 fee(V:Side): seatsPaid P (speakU u s) (A+1) 4 s V
 beats(n:ℕ) : ‖wakeForceBill‖/2 < ‖averageCredit P (s+n) (later P s n (firstPair P u β A s)) (later P s n (secondPair P u A s))‖
 leads : ∀ᶠ m in atTop, ‖wakeForceBill‖/2 < ‖confirmedCredit P s (physicalPeriod P f m) (physicalCut P f m) (firstPair P u β A s) (secondPair P u A s)‖
 gap : Slant (apertureScale P A s/2) (region_ (apertureScale P A s) 0 1) (region_ (apertureScale P A s) 2 3)
 inside : ∀ (i : Fin 4), silhouette P.par P.width s (wheelS u s i) ⊆ cellAt (spot4 i) (apertureScale P A s) (1/8)
include ha W p g
lemma billAtSpots : ∀ᶠ s:ℕ in atTop, PairedReport P A u s β f := by
 let S:= spot4
 obtain ⟨Y₀,A₁,G₁,v,t⟩:= forces_unselected P f p ha W u g
 have h := half_lt_self opening
 have fᵣ:= fuelAll P ha face4 mask S u g 4 le_rfl (lt_add_one A)
 filter_upwards [v.norm.eventually (lt_mem_nhds h), (towerLate _).1 (t.norm.eventually (lt_mem_nhds h)),fᵣ,
       eventually_all.mpr (show ∀ i, ∀ᶠ s:ℕ in atTop, silhouette P.par P.width s (wheelS u s i) ⊆ cellAt (S i) (D_ s) (1/8) from fun i=> apartment P ha (g i) (1/8) (by positivity) 12)] with s p v g k
 let d:=D_ s
 have η:0<d:= apert_pos ..
 let ℓ:= firstPair P u β A; let W₂:= secondPair P u A
 have hz(i:J₀): silhouette P.par P.width s (wheelS u s i) ⊆ region_ d i i := (k i).trans (shadow_spot i d)
 have he(i:J₀) : HeldAt P s (region_ d i i) (firstV P u β A i s) (wheelS u s i) :=
     ⟨(usable P _ _ 4 β A (u s i) le_rfl s).1,(usable P _ _ 4 β A (u s i) le_rfl s).2, hz i⟩
 have hq(i:J₀) : HeldAt P s (region_ d i i) (secondS P u A i s) (wheelS u s i) := let f := ((obs_in ..).1 (secondOK P u s i A)); ⟨f.1.widen,f.2,hz i⟩
 obtain ⟨y₁,y₂⟩:= potential d η 0 1 (by norm_num [factorT]); obtain ⟨p₁,p₂⟩:= potential d η 2 3 (by rw [show factorT 2=3/2 from rfl,show factorT 3=5/2 from rfl]; norm_num)
 have T:= pieceMore P (arose P (he _) y₁) (arose P (he _) y₂); have B:= pieceMore P (arose P (hq _) p₁) (arose P (hq _) p₂); have H := diagram d η
 have qd : Disjoint (region_ d 0 1) (region_ d 2 3):= Set.disjoint_left.mpr (fun a h H' => by have he : a 2 + d/2 < a 2:= (H.1 _ h _ H').1 2; linarith only [he,η])
 refine ⟨T,B,g,fun n=>?_,v,H.1,k⟩
 rw [held_price P (show HeldAt P s _ (ℓ s) _ from T) (show HeldAt P s _ (secondPair P u A s) _ from B) qd]; exact p
#print axioms billAtSpots
universe wᵣ
omit p W ha g
-- all on Election, can integrate into further Wake questions. still mixed apparatus first pair.
theorem wakeElectionWithStory (X : TintDemand) (Mc : ℕ) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ),
      Spine.PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      Spine.QualifiedWakeReadout.{wᵣ} P K ∧ P.PhysicalWakeGram ∧
      ∀ f : ℕ → ℕ, StrictMono f →
      ∃ c : ℕ → ℕ, StrictMono c ∧ ∃ β, Tuned P (f ∘ c) β ∧
      ∀ A : ℝ, 0 < A → ∀ (d : ℕ), 0 < d → ∀ D : Cover,
      ∃ u : ℕ → Fin 4→ Cover, (∀ s i (j : Axis), (d:ℤ) ∣ u s i j - D j) ∧ (∀ i, Appoint P.par A (fun s=> u s i) (spot4 i)) ∧
          ∀ᶠ s in atTop, PairedReport P A u s β (f ∘ c) := by
  obtain ⟨P,K,E,h,pose,T,F⟩ := Spine.wakeElectionWithPhysicalGram.{wᵣ} X Mc
  refine ⟨P,K,E,h,pose,T,F,fun f r => ?_⟩
  obtain ⟨c,β,v,p⟩ := tuneFurther P r; refine ⟨c,v,β,p, fun A g d w D => ?_⟩
  have X (x:Gaia):∃ u:ℕ→ Cover,Appoint P.par A u x∧∀ s (j:Axis),(d:ℤ)∣ u s j-D j:= ⟨_, P.announces d w g D x⟩
  choose t ht W using fun i=> X (spot4 i)
  exact ⟨fun s i=> t i s, fun s i=> W i s, ht, billAtSpots P _ p g h _ ht⟩
#print axioms wakeElectionWithStory

end Resolving
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
