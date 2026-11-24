import Gingham.Ruff.Moonstone
import Gingham.Ruff.Rosehip

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false


variable {a c μ d l}
variable {ν:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ d ν F)
open GarlandBook
private lemma poised {m t:Side}{K':Calibration} {M:Mark t} {F:Family K'}
  (e:K'.c m=t)(p:Tapestry.arrange _ _ e (F m)=M)(w: List (Axis×ℤ)):
    Tapestry.arrange _ _ e (Ballet w F m)=maiden w M:=by
 subst t;exact congrArg (maiden w) p
namespace Lander
include β
#check poised

abbrev Levee := Regalia
abbrev cream(P:Spine)(ρ a c:ℝ):=max 0 (CF.Gingham.Ruff.GarlandBook.milk ρ (underlay P.par) a c)
lemma collar (hp:0≤ρ):∀ᶠ s:ℕ in atTop, ∀j:Axis,
 Levee P ρ s ν (wisp (~p~ s)) (F s (some j)) (cream P ρ a c):= by
 filter_upwards [β.clearFor 1 zero_le_one 2 le_rfl] with s h j
 refine ⟨((β.loaded s).train (some j)).check,
            (enclave_spec _).mpr (((β.loaded s).train (some j)).pays none).2.1,
            le_max_left ..,?_⟩
 filter_upwards [h.1] with n t
 intro r
 let i:= irr P (ν n)
 have hdeck:=poised (deckM P s (ν n)) (F:=F s (some j) (some n))
                  (β.onDeck _ _ (some j) t) r
 have h': (exhibit P.run P.large s i) (Ballet r (F s (some j) (some n)))=maiden r (t.gb.bassin t.bre j):=hdeck
 rw [show irr P (ν n)=i from rfl,h']
 exact (readySnow _ _ t.gears.tag r j hp).raise (le_max_right ..)
#print axioms collar
open Six
#print Anthem
#check rosy
#check Cosmos.anthem
#print Rialto


abbrev resin (P:Spine)(t a c:ℝ):=
   CF.Gingham.Ruff.refrain t (underlay P.par) a (pepCharge (underlay P.par) a c)
lemma lamps {δ t:ℝ}{X:Rialto 6 P.par.d δ t}
   (w:Anthem P a c μ d δ t X):
    ∀ᶠ s in atTop, ∃r:Levee P ρ s ν (wisp (~p~ s)) (F s none)
                           (resin P δ a c*(~p~ s).threshold ^ 2),
             PureGauge K r.ticket:=by
 filter_upwards [rosy β X w] with s g
 obtain ⟨r,p⟩:=GaugePrice (ρ:=ρ) (s:=s) (ν:=ν)
       ((β.loaded s).train none) g.2
 exact ⟨r,p⟩


#print axioms lamps

lemma ensemble {δ t:ℝ}{X:Rialto 6 P.par.d δ t}
   (w:Anthem P a c μ d δ t X)(hp:0≤ρ):
 ∀ᶠ s in atTop,∀z:ℂ,Levee P ρ s ν (frond K (~p~ s)) (wingtip z (F s))
    (‖z‖*(resin P δ a c*(~p~ s).threshold ^ 2 +8*cream P ρ a c)):=by
 filter_upwards [β.collar hp,β.lamps (ρ:=ρ) w] with s g h z
 let S:=frond K (~p~ s)
 have p:∀j v,v=(1:ℤ) ∨ v= -1 → Regalia P ρ s ν S (Spur j v (F s)) (cream P ρ a c):=
    fun j v w=> ((g j).stems j v).broaden (Frond_lobe j _ w)
 let C:=cream P ρ a c
 have u(j):= (p j 1 (.inl rfl)).apart (p j (-1) (.inr rfl))
 have u₁ :Regalia P ρ s ν S (∑j, (Spur j 1 (F s)-Spur j (-1) (F s))) (∑ _j:Axis,(C+C)):= 
    Regalia.winding (fun j _=> (u j).broaden (union_subset subset_rfl subset_rfl))
 have a: ∑ _j:Axis,(C+C) =8*C:=by
   rw [sum_const,card_univ,show Fintype.card Axis=4 from rfl]
   simp only [nsmul_eq_mul];push_cast; ring
 rw [a] at u₁
 exact ( ((h.choose.lime u₁).broaden (union_subset (frond_sp _ _) (Finset.Subset.refl _))).scale z )

