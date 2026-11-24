import Velour.Wadding.Violet
import Velour.Gathers.Rush
import Velour.Gathers.Cord
import Velour.Gathers.Slacken
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


variable {P:Spine}{K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}
local notation "ξ"=> P.advocate 3 x 3
local notation "ω"=> P.colorZero 3 ξ
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "ℋ"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ℰ"=> P.seasons 3 ξ
local notation "C"=> Lead.Clan
variable {R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}{A:ℕ→P.Apron}{n:ℕ→ℕ}{w:C→Prism}
    {V: ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)}
    {g h : ℕ} {X : P.HandleWith x c r A n}
variable {realY : C → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)}{Z:C→C→Boundary.Distn E4}
local notation "𝓕₄"=> M4Furnish P K c r x R i₀ F U A n w V g h X realY Z
local notation "𝓑"=> P.Bobbin 3 ξ
local notation "D"=> (ℰ).muslin
local notation "Ω"=> P.firstTulle 3 ξ
local notation "θ"=> P.detects 3 ξ
local notation "Q"=> P.bobQuote 3 ξ
local notation "γ"=> P.ThinVelour x A c r n w
local notation "Λ"=> P.profilesZ x V w


namespace M4Furnish
lemma vio_silky (u:𝓕₄)(e:γ)(z:P.M4Velvet x A c r n)
    (t:P.TottyCup x A)(a:C):
    (u.violet e a).Joint ∧ P.Totty 3 ξ (P.gaugeTrumpet A c r n w a):=
    P.silky_trumps a x A X z.2 (t 3 []) w

-- Identify the very two-point boundary *including on relative test*
-- even as joint costed. Parametrize by Joint just on those sold.

variable {p k:ℕ→ℕ}{M:ℕ→Test4}{f:Test4}
variable {a b:Lead.Clan}

lemma cord_left (u:𝓕₄)(e:γ)
    {m:ℕ}{c':ℝ}{Y:(G).Op}
    (j:(u.violet e a).Receives m c' Y)(b:Lead.Clan)(f:Test4):
   Z a b f = inner ℂ (Y ((ℰ).weight m Ω).val)
             ((ℰ).weight m (θ (u.violet e b) f Ω)).val:=by
 let g := (P.satin_storage 3 ξ).1 (u.violet e b)
 let w := (Ribs.prepaid j)
 have t:= (ℰ).tendstoCord (P.crown_vac 3 ξ u.emperor)
    w.gaze (g.harvest f)


 let d(t:ℝ):=(t/2).toNNReal
 have hg:Tendsto d (𝓝[>] 0) (𝓝[>] 0):=by
   refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within d ?_
      (eventually_mem_nhdsWithin.mono fun z p=>Real.toNNReal_pos.mpr (half_pos (show 0<z from p)))
   have p:Continuous d:= continuous_real_toNNReal.comp (continuous_id.div_const 2)
   have y:=p.tendsto 0
   simp only [d,zero_div,Real.toNNReal_zero] at y
   exact y.mono_left nhdsWithin_le_nhds
 exact tendsto_nhds_unique (u.real_line e a b f) (t.comp hg)
#print axioms cord_left


variable {l₁ l₂ r₁ r₂:ℕ→ℝ≥0}

theorem real_line_joint (u:𝓕₄)(e:γ)
   (j:(u.violet e a).Joint) (w:(u.violet e b).Joint)
   (gp:Tendsto p atTop atTop)(gk:Tendsto k atTop atTop)
   (q:Tendsto l₁ atTop (𝓝 0))(v:Tendsto l₂ atTop (𝓝 0))
   (q':Tendsto r₁ atTop (𝓝 0))(v':Tendsto r₂ atTop (𝓝 0))
   (y:Tendsto M atTop (𝓝 f)):
    Tendsto
       (fun i=> (ℰ).CordPair (Ω).val (M i)
         ((u.violet e a).quietSlot P 3 ξ (p i) (l₁ i) (r₁ i))
         ((u.violet e b).quietSlot P 3 ξ (k i) (l₂ i) (r₂ i))) atTop
      (𝓝 (Z a b f)):= by
 obtain ⟨m,c',Y,h⟩:= j.receives
 rw [u.cord_left e h b f]
 have s:=w.surges gk y v v'
 rw [P.heatL_nil,one_mul,mul_one] at s
 exact (ℰ).tendstoCord (P.crown_vac 3 ξ u.emperor)
    (Ribs.gaze_warm h gp q q').gaze s


lemma real_action_joint (u:𝓕₄)(e:γ)(j:(u.violet e a).Joint)
   (gp:Tendsto p atTop atTop)(q:Tendsto l₁ atTop (𝓝 0))(q':Tendsto r₁ atTop (𝓝 0))
   (y:Tendsto M atTop (𝓝 f)):
    Tendsto
       (fun i=> ((u.violet e a).visits P 3 ξ (p i) (l₁ i) (r₁ i) (M i) Ω).val)
        atTop (𝓝 (realY a f)):=by
   have t:=j.surges gp y q q'
   rw [P.heatL_nil,one_mul,mul_one] at t
   rw [←u.lofty_val e a f]
   exact (t.at_one _).plain

theorem matched_joint (u:𝓕₄)(e:γ)
   (j:(u.violet e a).Joint) (w:(u.violet e b).Joint)
   (gp:Tendsto p atTop atTop)(gk:Tendsto k atTop atTop)
   (q:Tendsto l₁ atTop (𝓝 0))(v:Tendsto l₂ atTop (𝓝 0))
   (q':Tendsto r₁ atTop (𝓝 0))(v':Tendsto r₂ atTop (𝓝 0)):
   Tendsto
       (fun i=> inner ℂ (Ω).val
         (((u.violet e a).windBack.visits P 3 ξ (p i) (l₁ i) (r₁ i) (sachet_LocalFieldBounds F) *
           (u.violet e b).visits P 3 ξ (k i) (l₂ i) (r₂ i) (sachet_LocalFieldBounds U)) Ω).val)
      atTop (𝓝 (Z a b (tieAt (sachet_LocalFieldBounds F) (sachet_LocalFieldBounds U)))):= by


 have t:=(j.turn.surges gp (tendsto_const_nhds (x:=sachet_LocalFieldBounds F)) q q').mul
          (w.surges gk (tendsto_const_nhds (x:=sachet_LocalFieldBounds U)) v v')
 rw [P.heatL_nil,one_mul,mul_one,one_mul,mul_one] at t
 rw [←u.jewel_boundary e a b]
 exact tendsto_const_nhds.inner (t.at_one Ω).plain

#print axioms real_line_joint
#print axioms real_action_joint
#print axioms matched_joint
end M4Furnish
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
