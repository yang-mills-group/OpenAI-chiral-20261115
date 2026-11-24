import YM.LocalFieldBounds.Motif.Season
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.LocalFieldBounds.Motif
open Filter Function Set Metric MeasureTheory 
open scoped Topology ComplexOrder InnerProductSpace NNReal Classical
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
open CF.QuadClock.ShapeLab SoulField SatinWard.Installment
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open Polaris.Rampart _root_.GarnetAct.Cut
open Set MeasureTheory
open _root_.YM.SatinWFixed Andesite Carton _root_.YM.Boundary Probe
open CF.Py.Rate.LocalLimit Preparation
open CF.Buffered.Afterglow.Tower
open Preparation.Tabletop CasaF.Signboard
open CF.Py.Rate.LocalLimit.Preparation.Yoke
open CF.Ione.Clock CF.Moto CF.LitCurrent AuroraX Verdance Lattice
open CF.QuadClock.SignSlot
open Chili
open YM.WakeFields CF
open Papal.Moon
open SatinWard
universe u

open Resolving ResolutionFrame

attribute [local irreducible] Spine.Register

open Metric
variable {X Z:TintDemand}{Q:Supplier}{m:ℕ}{η:Type}[Fintype η][Nonempty η]
  {ε' target:ℝ}(y : Programme.{u} X Z Q m η ε' target)

abbrev Fiesta : ℕ→Type :=
  Festival y.P y.M y.ht.tendsto_atTop y.Costs.ledger.rocky.night η
    (study y.τ y.P Z y.T y.Pay y.C y.Γ)
    (assets (Asteroid y.P.par.K y.T y.Pay y.C y.Γ))
    y.β
abbrev Actresses {f0:ℕ} (a:Fiesta y f0) : ℕ→ℕ→ℕ→Type :=
  Portrait y.P y.M y.ht.tendsto_atTop a.Wj a.ed y.Costs.ledger.rocky.night
    a.V' y.β a.a'
abbrev Rights {f0:ℕ} (a:Fiesta y f0) : ℕ→Prop :=
  Pageant y.P y.M y.ht.tendsto_atTop a.Wj a.ed y.Costs.ledger.rocky.night
    a.V' y.β a.a'

/-- Actual show. Take year activated at strictly
increasing dates. Even any conull rider requested at this bound possible,
via w and choosing at n independently of x request. -/
structure Stage : Type where
  f0 : ℕ
  a : Fiesta y f0
  w:ℕ
  v:ℕ
  n:ℕ
  chain:f0<w ∧ w<v ∧ v<n
  right:Rights y a w
  guest:Actresses y a w v n

abbrev Eligible (t:y.P.Spectrum0 3→ Prop) :Prop := ∀ᵐ x∂y.P.pillars 3, t x

lemma late_at (t:y.P.Spectrum0 3→ Prop) (ht:Eligible y t) (B:ℕ) :
    ∃ s:Stage y, B<s.f0 ∧ t s.guest.atx := by
  obtain ⟨f0,h,⟨a⟩⟩ := ((eventually_gt_atTop B).and y.calendars).exists
  obtain ⟨w,g,d⟩ := ((eventually_gt_atTop f0).and a.spot.scene).exists
  obtain ⟨v,j,p,q⟩ := ((eventually_gt_atTop w).and d.tenor).exists
  obtain ⟨n,b,i,P,σ,c,k⟩ := ((eventually_gt_atTop v).and q).exists
  obtain ⟨s,_,_,_,u⟩ := k t ht
  exact ⟨⟨f0,a,w,v,n,⟨g,j,b⟩,d,s⟩,h,u⟩
lemma very_late : Nonempty (Stage y) := by
  obtain ⟨s,_⟩ := late_at y (fun _ => True) (Eventually.of_forall fun _=>True.intro) 0
  exact ⟨s⟩
variable (X Z Q m η ε' target)
structure Production where
 prog: Programme.{u} X Z Q m η ε' target
 date: Stage prog

lemma dressed [DecidableEq η]
    (sK:Fintype.card (Announcement Wage4 η) ≤ m)
    (sJ:Fintype.card (Announcement Wage3 η) ≤ m)
    (w:0<ε') :
    Nonempty (Production.{u} X Z Q m η ε' target) := by
  obtain ⟨p⟩ := programme.{u} X Z Q m η sK sJ ε' target w
  obtain ⟨s⟩ := very_late p
  exact ⟨p,s⟩

/-- One purchase: require physical parameter > 1. -/
abbrev smallCast : ℕ :=
  Fintype.card (Announcement Wage4 Unit) + Fintype.card (Announcement Wage3 Unit)
abbrev Lone := Production.{0} (fun _ _ _ _ _ _=>0) (fun _ _ _ _ _ _=>0)
  (fun _ _ _ _ _ _ _ _ _ _ _ _=>0) smallCast Unit 1 1

theorem specimen : Nonempty Lone := dressed _ _ _ _ _ _ _ (Nat.le_add_right ..)
  (Nat.le_add_left ..) zero_lt_one

#print axioms late_at
#print axioms dressed
#print axioms specimen
end YM.LocalFieldBounds.Motif
