import Anomaly.Hop.Paste
import Anomaly.Ship.Public
import Anomaly.Separate.Pitch
/-! Lease consumers. Use generated forms on all subsequent Steps.Passes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.QuadClock
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
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
open Oise Rive
open Ione.Clock
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Tc"=> mid N B
local notation "Tf"=> mid P B
local notation "Wν" => (duty_Q X.p.order X.p.power*W)
-- CP protocol reports.
variable {j k mc:ℕ}
variable {r:I→Site (mid N B)}{A:I→ArcΦ}{a:I→ℝ}{X₁:Key I→RegBudget (mid P B)}{X₂:Key I→ForceBudget (mid P B)}
open Vow.TreasuryFog Roots Sour
structure BornEconomy (Ω':Occlus X.p) (O:Finset I)(M:ℕ)(σ:I→Site (mid N B))(E:Key I→RegBudget (mid N B))(K:Key I→ForceBudget (mid N B))(r:I→ℂ)
 (J:I→ Bag (mid N B))(A:I→ Swell.phy (mid N B))(Y:I→ RegBudget (mid N B))(F:I→ Cusp (mid N B))(t:I→ℂ)(E':Key I→ RegBudget (mid N B))(V:Key I→ForceBudget (mid N B))(q:ℕ)(f c y:ℝ) :Prop where
   grant : ∃ (a b:I→ Aura (mid N B)→ℝ),∃ H:∀ (i:I) (X':Aura (mid N B)),Sour.Flight X.p q X' h (J i X') (a i X') (b i X'),Thrust P_ G₀ H Ω' O M σ A E K (α_ξ r) Y F t E' V
   stage : ∀ z:Key I,(∀ i, ‖z i‖≤ f)→ IncX primeU (rim_C (Cube.node ∘σ) (E+E') z) X.p h c ∧ Dark primeU (bustle (Cube.node∘σ) (K+V) z) X.p h y -- remove Yp unused
-- post-polynomial. proof supplies for cap.
structure TourCap (L:Side)(σ:I→Site (mid N B))(E:Key I→RegBudget (mid N B))(F:Key I→ForceBudget (mid N B))(Φ:I→ArcΦ)(x y a:ℝ) : Prop where
    pulse: Notice σ E F
    earn: ∀ z:Key I,(∀ i,‖z i‖≤2)→ IncX primeU (E z) X.p h x ∧ Dark primeU (F z) X.p h y
    acre: ∀ i,Axon L.val (σ i) X.p (νTip E i) h a (Φ i)
    polys :∃ (P:Key I→ RegBudget (mid N B))(F':Key I→ForceBudget (mid N B))(M:I→ I→ℂ), E= (clearRoot σ P ∘ toV_C (Cube.node ∘ σ) M) ∧ F=(bustle (Cube.node∘σ) F' ∘ toV_C (Cube.node∘σ) M)
    -- add ‖ξ‖ and offsets separately.
variable {Ω':Occlus X.p}{O:Finset I}{J₀:I→ Bag (mid N B)} {A₀:I→ Swell.phy (mid N B)} {Y₀:I→RegBudget (mid N B)}{F₁:I→Cusp (mid N B)} {E:Key I→RegBudget (mid N B)}{F':Key I→ForceBudget (mid N B)}{D:Key I→RegBudget (mid N B)}{K':Key I→ForceBudget (mid N B)}{x t':I→ℂ}{f c y:ℝ}
variable {k':ℕ}{nM:ℕ}
-- Crest. note shadow V in structure not captured? likely passed first V Grasp.Hi.P
#check BornEconomy
variable (Tκ: BornEconomy V P_ G₀ X h Ω' O k r E F' x J₀ A₀ Y₀ F₁ t' D K' k' f c y)
variable (hv:Furnace X O k' r E F' (α_ξ x) h T b g) (hz:CrestPay X.p (Cube.node ∘r) E (X.p.supportExponent+1) h T) (u:8≤ X.p.B)(pδ:Ω'.η=(X.p.B:ℝ)⁻¹)(hp:1≤h)
local notation "Zσ"=> Cube.node ∘ r
local notation "EΦ"=> clearRoot r (E+D)
local notation "KΦ"=> bustle (Cube.node ∘r) (F'+ K')
variable (M:I→I→ℂ)
local notation "Λ"=> toV_C (Cube.node ∘r) M
local notation "Υx"=> EΦ ∘ Λ
local notation "ΥF"=> KΦ ∘ Λ
local notation "τ"=> (x+t')
local notation "Bol" F:max G:max T:max z:max=> color_b X X.beta (X.F+F z) X.slip (X.K+G z) (X.v+α_ξ T z)
include Tκ hv hz u pδ hp
lemma Review_cap (p:Force_M X.p.B (Cube.node ∘r) nM)(w:∀ z:Key I,(∀ i,‖z i‖ ≤2)→∀ i,‖toV_C (Cube.node ∘r) M z i‖≤ f) (l:Side)(Vθ:I→ArcΦ)(Vξ:I→ℝ)(v:ℝ)(H:∀ i,Axon l.val (r i) X.p (νTip E i+Y₀ i) h (Vξ i) (Vθ i))(α:∀ i,(∑ j∈pipe_ζ (Cube.node ∘ r) i,‖M j i‖* Vξ j)≤v)(a:0 ≤ v): TourCap X h l r (Υx) (ΥF) (markerCore (Cube.node ∘r) M Vθ) (2*v*nM+c) y v:=by
 obtain ⟨F,V,Wk,q⟩:=Tκ.grant; let C:=Tκ.stage
 let w':= lease_ticket P_ G₀ Wk q hv hz u pδ hp
 obtain ⟨N,S,F⟩:=w'
 let pL:=limited P_ G₀ Wk q hv hz u pδ hp
 have H₀:(E+D) 0=0:= (by rw [Pi.add_apply,q.live.1, hv.E0,add_zero])
 have hX(i:I): νTip (E+D) i=νTip E i+ Y₀ i:= ((cropEra H₀ r pL.1.toSiltQ pL.2.toBudK).2 i).1 ▸ (S i).1
 obtain ⟨x,t,z⟩:= token_stamp r (E+D) (F'+K') M X N H₀ pL.1.toSiltQ pL.2.toBudK C p hp w Vθ Vξ (fun i=> by rw [hX]; exact H i) α a
 exact ⟨x,z,t,_,_,_,rfl,rfl⟩ -- existential F' rfl synth placeholders issue

lemma account (L:List I)(vS:L.length ≤ k)(q:ψS (Cube.node ∘r) L) (i:Orbit (mid N B))(t:IsStarProjection (Dial.spar K.j X.J.M (G₀ i))) (p:Injective (priorP i.2))(xH:FleetS X.p.threshold i.1)(z:∀ l:List I,l.map (Cube.node∘r)=L.map (Cube.node∘r)→(Leit O l).Pairwise fun x y=> Commute (A₀ x i) (A₀ y i)) : tipI (fun j:Key I=> denZ (Bol (Υx) (ΥF) (markerCore (Zσ) M τ) j) P_ G₀ i) L = snow (Zσ) M (fun j=> acts (((Leit O j).map fun z=>A₀ z i).prod) (tipI (fun z:Key I=> denZ (color_b X X.beta (X.F+E z) X.slip (F' z) (X.v+ α_ξ x z)) P_ G₀ i) (Leit (Finset.univ\ O) j))) L:=by
 obtain ⟨f,v,w,T⟩:=Tκ.grant
 let U':=lease_ticket P_ G₀ w T hv hz u pδ hp
 have h:=sworn_den (C:=G₀) (U':=P_) r (E+D) (F'+K') M V X τ L q i
 refine h.trans (rer _ _ _ fun l t'=>?_); have hz:l.length=L.length:= by simpa using congrArg List.length t'
 let Z:=U'.2.2 l (hz.symm ▸ vS) (show (l.map (Cube.node ∘ r)).Nodup from t'.symm ▸ q) i t p xH (z _ t')
 -- notation resolution z
 change tipI (fun z':Key I=> _) l=_; rw [sum_ring]; exact Z
-- expose laws on first outputs. use with canonical Lease and V.
lemma crestReport :
   ∃ (a b':I→ Aura (mid N B)→ℝ),∃ Q:∀ i j,Sour.Flight X.p k' j h (J₀ i j) (a i j) (b' i j),
    (∃ v w r₀, OrbitRack Ω' (Cube.node∘r) k' X.K h (zealPitch J₀ a b' Q) v w r₀ (fun z x Y=>pinSeries J₀ z Y x)) ∧ νTip (Υx)= markerCore (Cube.node ∘ r) M ((νTip E)+Y₀) ∧ emberTip (ΥF)= markerCore (Cube.node∘r) M (emberTip F'+ emberTip (mkCup X.p X.K (zealPitch J₀ a b' Q) k F₁)):=by
 obtain ⟨A,V,u₀,H⟩:=Tκ.grant
 let p:= (lease_ticket P_ G₀ u₀ H hv hz u pδ hp).2.1
 refine ⟨A,V,u₀,H.funds,funext (fun i=>?_),funext (fun i=>?_)⟩
 · rw [tipE_c, show νTip (clearRoot r (E+D))=νTip E+Y₀ from funext fun i=>(p i).1]
 rw [tipF_c, show emberTip (bustle (Cube.node∘r) (F'+K'))=emberTip F'+ _ from funext fun i=>(p i).2]
end YM.CF.QuadClock
