import Bay.C.Lapel
import Bay.C.Talon
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation

open Salt SU Swell QuadClock Mew Vow.TreasuryFog BProof.Bide
open scoped YM.CF.Mew

variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]


variable (w:Berth)
abbrev melted (S:I→SealV w.side)(L:ℕ):=w.melt (gr S) (paints S) L

def Licensed (S:I→SealV w.side)(L s:ℕ)
 (U:Mew.Key I→RegBudget w.side)(V:Mew.Key I→ForceBudget w.side):Prop:=
 ∃ (c r:I→Aura w.side→ℝ)
    (p:∀i, Orchard w.p w.q w.H (melted w S L i) (c i) (r i))
    (τ:Ids w.side),
   Chromatic w.p w.q w.H w.R.K p s ∧ ∀ i,
    νTip U i=kilnTip p (gr S) τ i ∧
    emberTip V i=νΦK (rootF w.R (flare p) s) {i}

/-- sealed. `s` common high-degree cutoff when comparing -/
structure Dons (S:I→SealV w.side)(L s:ℕ)(b:ℝ)
 (U:Key I→RegBudget w.side)(V:Key I→ForceBudget w.side)
 : Prop extends Hops w S L b U V where
  lit: Licensed w S L s U V

variable {w} {S:I→SealV w.side}{T:J→SealV w.side}{L s:ℕ}{b d:ℝ}
 {U:Key I→RegBudget w.side}{V:Key I→ForceBudget w.side}
 {G:Key J→RegBudget w.side}{K:Key J→ForceBudget w.side}


lemma pin_V (p:w.s≤w.P.run.uv w.k)(a:Dons w S L s b U V)
 (c:Dons w T L s d G K) (θ:Sweep w.side)
 (i:I)(j:J)(u:Steering θ (S i).ink (T j).ink)
 (e:(boxA θ).symm (S i).root=(T j).root):
 passingR w.side θ (νTip U i) (νTip G j) ∧ passingF w.side θ (emberTip V i) (emberTip K j):=by
 obtain ⟨z,t,h,α,y,v⟩:=a.lit
 obtain ⟨Z,P,r,δ,H,k⟩:=c.lit
 rw [(v i).1,(k j).1,(v i).2,(k j).2]
 have ℓ:Steering θ (melted w S L i) (melted w T L j):=by
    change Steering _ _ (stick L (T j).root _ _)
    rw [←e]; exact Driving θ _ _ _ u -- fill
 have l:passingF w.side θ w.R.K w.R.K:=by
    intro X x c'
    exact (((w.P.run.voyage w.i).X (w.P.run.uv w.k)).pull.note _ p).nite.face θ trivial _ (spinZ ..) _ _ _ c'
 refine ⟨?_,pin_U ℓ l y H⟩
 unfold kilnTip gr
 rw [←e]
 exact sore θ ℓ (h i) (r j) _ _ _

lemma licensing {M m:ℕ}{a c:ℝ}{F C D:ℝ→ℝ}{r:blazeK w.side}
 (g:w.Thermal M L F C D r)(h:w.Rig a c m)(k:w.Tall)
 (u:w.GaugeBill M (gr S))(z:∀ i,Grant w C D (S i))
 (j:w.lampCap ≤ s):
 ∃ U V,Dons w S L s (icedCost w.P M L F D w.x) U V:=by
 let τ:Ids w.side:=Classical.arbitrary _
 obtain ⟨E,B,d,t⟩:=Berth.cacheTherm g u
      (v:=paints S) (fun i=>(z i).charged)
 obtain ⟨y,b⟩:=hops_book g h k u z d s j τ
 refine ⟨_,_,y,E,B,d.bill,τ,?_,b⟩
 have e:1 ≤w.H:= w.P.par.height
 exact ⟨e,fun _ a=>mint_U t e s a,fun X=> (sealF (N:=Vale.mesh (w.P.run.ir w.i) w.P.par.R.L w.s)
    (B₁:=w.P.par.block) (R:=w.R) (w.coincert g.1) _ _ _ _ t s e X).2⟩
