import Bay.C.Curtain
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.C
open QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise



open Rate LocalLimit Preparation Pitching Focus 
set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
local notation "VΔ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine


namespace HullF
variable (w:HullF)(b:Rib w.P)(M:ℕ)(g:Outfit)(t:ℕ)
structure Sails (w:HullF)(b:Rib w.P)(M:ℕ)(g:Outfit)(t:ℕ):Prop where
 count:w.gaps
 aboard:w.steeple
 showboat:w.scene b M 
 levee:FleetX w.newb g M w.L.val t
 apron:∃r,w.valid b M r
 low:0≤w.amt M g t
 high:w.amt M g t≤w.pouch b

variable {w b M g t}
-- step one: heel G coarse site for arbitrary pose x at fine
variable (x:Site w.sea)(s:Sweep w.sea)(shoe:w.Sails b M g t)
local notation "fM"=>w.flagroot x s
local notation "πp"=>w.dport x s
open FleetX
open scoped YM.CF.Mew
open Swell

include shoe
lemma passages
 (f:w.newb.First)(d:w.newb.Before g.a g.b g.m x f)
 (v:Sour.Bag w.sea)(u:w.newb.WearY g.m x f g.a g.c g.b v):
 ∃J,OrderT w.newb g t x fM f v J:=
 shoe.levee.order d (w.berthroot x s shoe.aboard) u

-- each solo σq
lemma soloist {m:ℕ}{a:w.Apron}(p:w.valid b M a)
 (T:SealV w.sea)
 (h:σq w.newb g t T)
 (r:T.root=fM)
 (y:Velvet s)
 (z:1≤M)
 (l:w.newb.lampCap ≤ m):
 ∃E F o,ShipF w b M g t a (fun _:Fin 1=>πp) (fun _=>watch s T) E F m o :=

   flotilla _ _ shoe.showboat p shoe.count shoe.low shoe.high shoe.levee
    (gridLib w x s (fun _=>T) ((Fintype.card_fin _).le.trans z) (fun _=>r)) 
    (fun _=>shoe.levee.sweeping h s y) l

end HullF
open BPress (NPL)
local notation "FQ"=>Till.qL
def fcE(P:VΔ)(s i k:ℕ):HullF:=⟨P,s,i,k⟩
variable {P:VΔ}{b:Rib P}{M:ℕ}{g:Outfit}
section
lemma helmStep (n:ℕ)(e:Edge P (SceneF P b M))
 (h:Helm P g)
 (f:Dry P (fun w=>w.Rig g.a g.c g.m)):∀ᶠ t in atTop,
  NPL (Funds P g t) ∧ HopsRate P.par.R (Dosage P g t) n ∧
  (∀m l, WaitZ P.par.R (powZ n) (Year P g m l t) ∧ Dry P (fun w=>FleetX w g m l t))∧
  Edge P (fun s i k=> (fcE P s i k).Sails b M g t):=by
 filter_upwards [h.ready n] with t fees
 have u(m l):WaitZ P.par.R (powZ n) (Year P g m l t) ∧ Dry P (fun w=>FleetX w g m l t):=by
    refine ⟨(fees.2.2 _ _).1, ?_⟩
    filter_upwards[(fees.2.2 m l).2, f] with j a b
    filter_upwards[a,b] with i y z k h
    exact y k h (z k h)
 refine ⟨fees.1,fees.2.1,u,?_⟩

 let L:=P.par.R.L
 filter_upwards[e, Dry.next (u M L.val).2,
    plankF b.Γ (u M L.val).1,(Work.E01.radiusB_tendsto.comp
      ((turnover P.par).comp (tendsto_add_atTop_nat 1))).eventually_ge_atTop (drift L)] with s j k l y
 filter_upwards[j,k] with i d p q z
 have egg:=p q z
 have hh:= HullF.apron_exists (fcE P s i q) b M (d q z)
 refine ⟨z,?_,d q z,egg,hh,l.1,l.2⟩
 show drift L≤24*(takeUp P (s+1) i q).p.B
 rw [egg.prop.sizeB]
 exact y.trans (Nat.le_mul_of_pos_left _ (by decide))
