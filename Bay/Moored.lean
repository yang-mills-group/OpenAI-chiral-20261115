import Bay.Venue
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


open Buffered
namespace Berth
variable (w:Berth)
variable {M m L:ℕ} {F C D:ℝ→ℝ}
 {I:Type}[LinearOrder I][Fintype I]
 {E B:I→ Aura w.side→ℝ}
 {r:blazeK w.side}
 {a c:ℝ}

abbrev GaugeBill (M:ℕ)(σ:I→Seat w.side): Prop:=
   Multiplicity σ M ∧ LatticeWide σ w.p.B
abbrev Glut (G :Orbit w.side→Prop): Prop:=
  ∀ᵐ u∂city w.side,G u

variable 
 (T:I→footprint w.side)(σ:I→Seat w.side)(b:I→ℝ) 
 (o:I→Stencil w.side) (y:I→phy w.side)
 (v:I→ Sour.Bag w.side) (G:Orbit w.side→Prop)
 (U:Mew.Key I→ RegBudget w.side)(W:Mew.Key I→ForceBudget w.side)



/-- Full package with maybe smaller target price. Independent of spacing in
  stencil pair; disjoint among reads (pairwise physical supports in each read).
  This structure, with chosen U,W, is convenient to forget construction. -/
structure Moored (T:I→footprint w.side)(σ:I→Seat w.side)(b:I→ℝ)
 (o:I→Stencil w.side)(y:I→phy w.side)(G:Orbit w.side→Prop)
 (L:ℕ)(t:ℝ)
 (U:Mew.Key I→ RegBudget w.side)(W:Mew.Key I→ForceBudget w.side):Prop where
   actual(i:I):Accompanies (T i) (b i) (o i) (y i)
   paid:Receives w.p L σ U W w.H t

   flow:w.Reloaded T σ b o y U W G
   capFee : w.kick→w.Palladium U W t

variable {w T σ b o y v G U W}
-- consequences at point
variable {t:ℝ}
lemma Moored.loanForce (k:w.Moored T σ b o y G L t U W)(i:I):
 Dark primeU (emberTip W i) w.p w.H t:=by
 obtain ⟨a,c,g,u,z⟩:=k.paid
 have y0:= z (update 0 i 1)
 rw [(g.head i 1).2,one_smul] at y0
 exact (y0 (fun i=>by rw [update_apply];split<;> simp)).2

lemma Moored.salary (k:w.Moored T σ b o y G L t U W)
 (h:w.kick) (l:List I)
 (p:ψS σ l)(g: independent l T)
 (S:footprint w.side)(m:Bool)
 (A:Mark w.side)(d:AtSupport m S A)
 (f:Disjoint (stair l T) S):
 w.sharp (w.pages o l*A)=tipI (w.ovation U W A) l/w.cap :=
   -- conjunction
   by
   obtain ⟨j,e⟩:=d.env.cost
   rw [((k.capFee h).2 A d.env |>.2 l).2.1]
   exact (k.flow.confirms l p g S m A d f h j e).paid

lemma unspooled
 (q:w.Thermal M L F C D r)
 (h:w.Rig a c m)
 (g:w.GaugeBill M σ)
 (d:w.Cached σ v L E B C D)
 (p:w.Quest T b o y v G)

 (hg:w.Glut G)
 (s:ℕ)(j:w.lampCap ≤ s)(τ:Ids w.side):
 let U:=w.flareE d σ s τ
 let V:=w.flareF d σ s
 w.Moored T σ b o y G L (icedCost w.P M L F D w.x) U V∧
 ∀ i, νTip U i=kilnTip d.bill σ τ i∧ 
      emberTip V i=νΦK (rootF w.R (flare d.bill) s) {i}:=by
 obtain ⟨e,x⟩:= stickerPrice q g.1 g.2 d s τ
 intro U V
 exact ⟨⟨p.pair,e, shrug h q g.1 d p hg j τ,fun w=> (shrewd h w e).publishes h.pulse.roof.bill⟩,x⟩

lemma cacheTherm (e:w.Thermal M L F C D r)
 (g:w.GaugeBill M σ)(p:∀i,w.loanY (σ i) (v i) C D):
 ∃ E B:I→Aura w.side→ℝ,∃ d:w.Cached σ v L E B C D,OrbitRack (w.coincert e.1) σ w.q w.R.K w.H 
     (flare d.bill) (riseF E) (riseF B) r (flareM (w.melt σ v L)):=by
 obtain ⟨E,B,d⟩:=cacheMine e p
 exact ⟨E,B,d,farm e.1 σ g.1 (hearth L) d⟩

end Berth
