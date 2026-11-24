import Velour.Gallery.Twinned
import Velour.Sequins.Foil

/-! # Assaying on a single sleeve at a time. 
Charge from literal grid readings, then slider. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

open YM.Velour


variable (P:Spine)(a:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 a j
local notation "S"=> P.seasons j ξ
local notation "Ω"=> P.heaven j ξ
variable (p q:Vantage)(A:P.Apron)(l o r:ℝ)
local notation "B"=> A.kiss P j
local notation "w"=> A.realWidth P j

abbrev beads (i t:ℕ): ℝ:=
  (P.singleState j t ξ (P.prepared t B (velourSampleBead p i)* P.prepared t A (velourSampleBead q i))).re
lemma flounce_bead (p:Vantage)(A:P.Apron) (v:P.ManyF j ξ):
 Tendsto (fun i=> (P.sleeveEu j ξ (velourSampleBead p i) l r A) v) atTop
      (𝓝 (P.cloaked j ξ (A.realWidth P j) l r (P.mounted j ξ A) p v)):= by
 exact sprinkle _ _ _ (P.cloaked_cont j ξ _ l r (P.mounted j ξ A) _)


/-- Index `(i,t)`: sliders i, refined grid t. Grid→∞ first. -/
def kindling : Filter (ℕ×ℕ):=
 atTop.bind (fun i=>atTop.map (Prod.mk i))
instance kindling.exists : kindling.NeBot:= by

 constructor
 intro h
 obtain ⟨n,t⟩ := (eventually_bind.mp (show ∀ᶠ i in kindling,False from eventually_false_iff_eq_bot.mpr h)).exists
 exact t.exists.choose_spec

def scrollwall (i:ℕ) : ℝ:=
 (inner ℂ Ω ((P.sleeveEu j ξ (velourSampleBead p i) l o B) ((P.sleeveEu j ξ (velourSampleBead q i) o r A) Ω))).re
def scrollprice : ℝ:=
 (inner ℂ Ω ((P.cloaked j ξ w l o (P.mounted j ξ B) p)
     ((P.cloaked j ξ w o r (P.mounted j ξ A) q) Ω))).re
lemma scroll_sum :
 Tendsto (P.scrollwall a j p q A l o r) atTop (𝓝 (P.scrollprice a j p q A l o r)):=by
 let v:=P.cloaked j ξ w o r (P.mounted j ξ A) q Ω
 refine Complex.continuous_re.tendsto _ |>.comp
    (tendsto_const_nhds.inner (firmly _
       (norm_nonneg (P.mounted j ξ B)) ?_
       (P.flounce_bead a j l o p B v) (P.flounce_bead a j o r q A Ω)))

 refine Eventually.of_forall fun i=> ?_
 have h:(velourSampleBead p i).Normalized:=prescribed ..
 refine (P.flounce_price j ξ _ _ _ _ (velourSampleBead p i)).trans ?_
 rw [show SampleDose.l1 (velourSampleBead p i)=1 from ?_,one_mul]
 exact (integral_congr_ae (Eventually.of_forall fun y=>Real.norm_of_nonneg (h.1 y))).trans h.2

private lemma guards (p:Vantage) (j:Axis)(l r width:ℝ)
 (e:l<p j-width ∧ p j+width<r):
 ∀ᶠ i in atTop,∀y∈tsupport (velourSampleBead p i).val,l<y j-width ∧ y j+width<r:= by
 let T:= {y:Vantage|l<y j-width ∧ y j+width<r}
 have a: IsOpen ({y:Vantage | l< y j-width} ∩ {y:Vantage | y j+width<r}) := (isOpen_lt continuous_const (by fun_prop)).inter
                     (isOpen_lt (by fun_prop) continuous_const)
 exact closes p (fun _=>p) tendsto_const_nhds T (a.mem_nhds e)


lemma assay (J:P.Ellis 3 a)
 (e:l<p j-w ∧ p j+w<o)
 (g:o<q j-w ∧ q j+w<r):
 Tendsto (fun t=> P.beads a j p q A t.1 t.2)
     kindling (𝓝 (P.scrollprice a j p q A l o r)):=by
 have y:=A.real_width_pos P j
 have u:l<o:= by linarith only [y,e.1,e.2]
 have v:o<r:= by linarith only [y,g.1,g.2]
 have m:∀ᶠ i in atTop,Tendsto (P.beads a j p q A i) atTop
    (𝓝 (P.scrollwall a j p q A l o r i)):= by
    filter_upwards [guards p j l o w e,guards q j o r w g] with i b c
    exact (Complex.continuous_re.tendsto _).comp
       (P.broadPair a J j B A (velourSampleBead p i) (velourSampleBead q i) l o r u v b c)
 refine tendsto_def.mpr fun U hu=>?_
 change ∀ᶠ i in kindling,_
 apply eventually_bind.mpr
 filter_upwards [m,(P.scroll_sum a j p q A l o r).eventually (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hu))] with i h t
 exact eventually_map.mpr (h.eventually (mem_interior_iff_mem_nhds.mp t))
#print axioms assay
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
