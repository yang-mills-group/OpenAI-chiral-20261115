import YM.LocalFieldBounds.Motif.Theatre
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

/- avoid giant early elaboration reductions -/
attribute [local irreducible] Spine.Register
structure Programme (X Z:TintDemand)(Q:Supplier)(m:ℕ)(η:Type)[Fintype η][Nonempty η]
     (ε' target:ℝ) where
  hε : 0<ε'
  sitsK: Fintype.card (Announcement Wage4 η) ≤ m
  sitsJ: Fintype.card (Announcement Wage3 η) ≤ m
  τ:ℝ
  hτ:1 ≤ τ ∧ ΛcrestF τ
  P:Spine
  U:P.Register
  E:ℝ
  w:ℕ
  f:ℕ→ℕ
  β:ℕ→ℝ
  M:P.par.R.L.val%16=1
  large:64 ≤ P.par.R.L.val ∧ 15 ∣ P.par.R.L.val
  Costs:Squall.{u} w m (billUp τ (wardRate τ X Z) Z) P U E
  ht : StrictMono f
  count : (2+(m:ℝ))*Ione.strive_E 6<w
  pose : uniform P U Q target ε'
  nt : Tuned P f β
  bill : ReflectedGaugeLower P β ∧ SignedDenominator P
  rank : ∃ b C t r,P.CouncilGrant U b C t f r β ∧ P.PublicKernel f r
  T: Hove.Grant P.par.K.j 2
  Pay:ℝ
  C:ℝ
  Γ:ℝ
  W:ℝ→ℝ
  V:ℝ→ℝ
  F:ℝ→ℝ
  Z':ℝ→ℝ
  fee : FinanceLeaf (pushGarden (wardRate τ X Z)) (paidUp τ Z) m P T Pay C Γ W V F Z' w
  wages : StageBooking P T Pay C Γ W V F Z' m (study τ P Z T Pay C Γ) τ
  calendars : ∀ᶠ f0 in atTop, Nonempty (Festival P M ht.tendsto_atTop Costs.ledger.rocky.night η (study τ P Z T Pay C Γ) (assets (Asteroid P.par.K T Pay C Γ)) β f0)

variable (X Z:TintDemand)(Q:Supplier)(m:ℕ)(η:Type)[Fintype η][Nonempty η]
theorem programme [DecidableEq η]
    (sK:Fintype.card (Announcement Wage4 η) ≤ m)
    (sJ:Fintype.card (Announcement Wage3 η) ≤ m)
    (ε' target:ℝ) (w:0<ε') :
    Nonempty (Programme.{u} X Z Q m η ε' target) := by
  obtain ⟨τ,i,j,P,K,E,n,f,β,M,c,ht,
     ⟨h₁,k,h₂,h₃⟩,⟨T,Pay,C,Γ,W,V,F,Z',p,r,b⟩,v,g,t,u⟩ :=
        Installment.treaty.{u} η X Z Q sK sJ ε' target w
  refine ⟨w,sK,sJ,τ,⟨i,j⟩,P,K,E,n,f,β,M,⟨h₂,h₃⟩,c,ht,h₁,k,v,
     ⟨g,t⟩,u,T,Pay,C,Γ,W,V,F,Z',p,r,?_⟩
  obtain ⟨a,d,s,y,k,z⟩ := u
  exact b.mono fun i h=>january_debut P M _ _ h₂ k z h
#print axioms programme

end YM.LocalFieldBounds.Motif
