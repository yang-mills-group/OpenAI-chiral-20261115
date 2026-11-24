import ZecaSide
import ZecaSlip
import SatinThinQuizPair
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "G"=>P.ManyF 3 ξ
local notation "ε"=>P.physicalEnergy 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "ν"=>P.nv 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola M)

open DoseTravel Set

variable (A:ℕ→P.Apron) (c r n:ℕ→ℕ) (w:Lead.Clan→Prism)
 (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
 (T:P.HandleWith x c r A n)(R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)


variable (D:Cilium P x)
 (b:∀i, P.Lustre 3 (P.advocate 3 x 3) (D i) (P.soldTrumpet A c r n w i))

local notation "ℒ"=>Lead.Clan


variable (p q:Vantage)(o:p 3<q 3)(i:ℕ)
abbrev orb :=
 bubble S (P.minkX x D (skate p i)) (P.minkX x D (skate q i))
abbrev inkZ(qp:Vantage)(d:ℝ≥0):=duration (d+d)+sideways (-(qp 3))

lemma orb_side(t:ℝ): P.orb x D p q i (sideways t)=
   P.minkPrice x D (skate p i) (skate (q+ripple t) i):=by
 ext1 a f
 unfold orb bubble minkPrice;rw [Matrix.of_apply,tip_side,Matrix.of_apply,P.mintshift]

include R b
lemma mint_spray (p:Vantage)(z:ℒ)
 (d:ℝ≥0)(j:0<d):
 Tendsto (fun i=>E d (P.minkX x D (skate p i) z))
   atTop (𝓝 (M S (homeV p) (P.profilesZ x V w z d))):=by
 rw [P.euProfile x A c r n w V g h T R D b z d j]
 exact skate_go S ν (P.nova 3 ξ) (P.prepaid 3 ξ) (D z) p d j


lemma orbit_spray (d:ℝ≥0)(j:0<d)(m:(d:ℝ)=(q-p) 3/2):
 Tendsto (fun i=>P.orb x D p q i (inkZ (q-p) d)) atTop
     (𝓝 (P.pointPrism x V w (q-p))):=by
 refine tendsto_pi_nhds.mpr fun y=>tendsto_pi_nhds.mpr fun z=>?_
 let B:= (S).edge (-(q-p) 3)

 have e:=P.mint_spray x A c r n w V g h T R D b p y d j
 have e':=P.mint_spray x A c r n w V g h T R D b q z d j
 have h:= (e.inner (𝕜:=ℂ) ((B.continuous.tendsto _).comp e'))
 dsimp only [B] at h
 rw [P.back_cart,m] at h
 exact h.congr fun _=> (bubble_split _ _ _ j _ _).symm

include o
lemma mink_buy (h':ReadsSix (P.pointPrism x V w (q-p))):
 ∀ᶠ i:ℕ in atTop, ∃ᶠ t:ℝ in 𝓝 0, ReadsSix
   (P.minkPrice x D (skate p i) (skate (q+ripple (-t)) i)):=by
 let d:=((q-p) 3 /2).toNNReal
 have w':0<(q-p) 3 := sub_pos.mpr o
 have y:0<d:= Real.toNNReal_pos.mpr (half_pos w')
 have hp:= P.orbit_spray x A c r n w V g h T R D b p q d y (Real.coe_toNNReal _ (half_pos w').le)
 filter_upwards [hp.eventually (readsSix_open.mem_nhds h')] with i k
 have e:=bubble_found S (P.minkX x D (skate p i)) (P.minkX x D (skate q i))
       (show inkZ (q-p) d∈ OS.Semigroup.inside from length.mpr (add_pos y y)) k
 exact e.mono fun t v=>by
         rw [←P.orb_side]
         exact v
#print axioms mink_buy
