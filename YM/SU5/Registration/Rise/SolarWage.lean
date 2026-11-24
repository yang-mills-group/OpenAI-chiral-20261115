import YM.SU5.Registration.Rise.Campaign
import YM.SU5.Registration.Tuple
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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
open _root_.YM.SatinRegistration
open Regis.Head Regis.Head.Brecht
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

/-! # Existence of a SAME M4 tuple with this cap bound

Sharper variants of the purchases in `PoweredElection` & `EdgeLab`. In particular
no change of Experiment/n *when* finding the prism kernels for those
stencils. To keep a proof interface independent of how one purchased that
finer scale or chose the new times, give earnings relative to a specified
experiment, specified gauge sequence (earned elsewhere) and any `HandleWith`.

This step in the election *does not yet pay* the matter sensor in the cap. We
only hold the price at EACH fixed pad for the gauge calibration kernel used
in the local-field problem (and price ALL these aspect points down to zero).
-/
variable (P: Spine)(x:P.Spectrum0 3)(K:P.Register)(J:P.Ellis 3 x)(c r:ℕ→ℕ)
variable (g h:ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(v:ℕ→ℕ)
variable {A C b:ℝ}
include J
lemma appointed_camera (s:P.NightCop)(L':Odd P.par.R.L.val)(d:∀ᶠ s:ℕ in atTop, treasury A C P s (s+1) (s+1))(hb:0<b)
    (p:CruisePreparation P A C b K c r g h x J)(S:ScoutAnthem P x A C g h b v a)(W:∀ j l, AtGlassRate P x j g h l v a) :
    ∃ (A:ℕ→P.Apron)(V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), GalaxyShow P x g h A V ∧ P.PoweredHeat x V ∧ (∀ i, PureGauge P.calibration (A i).F) ∧ P.Funding x A:=by
 -- Select width sequence AFTER specifying gauge station and experiment. subsidy clamp. StrictMono here on same regulator (not comparison across histories). Reuse ballot against actual attachment in `PoweredElection` proof.
 obtain ⟨ψ,q,t⟩:= (S.rides p.station.2.1).forks
 let v':= v ∘ ψ; let a':= a ∘ ψ; have hT:= S.move q; obtain ⟨d',u⟩:= hT.station
 let hj:StrictMono v':= u.fast; obtain ⟨k,Y,Z⟩:= P.radiated x v' hj a' g h hT
 let X:= P.cinema x g h v' a' k hj
 let hH:Radiates P x X Y:=Z; let V:GalaxyShow P x g h X Y:= ⟨hH,fun i=> P.pleading_b ..,fun i=> P.pleading_g ..,fun y w=> Spine.freemen P _ g h v' hj a' k Y hT p.station.2.1.le p.station.1 hb Z p.opera y w,fun j l k' u v a b t g p' => P.scenic_right x j J Z Z l k' t g (sub_pos.mpr p'),fun j l k u v a b t g p' => P.scenic_left x j J Z Z l k t g (sub_pos.mpr p')⟩
 refine ⟨X,Y,V,P.cinema_powers x _ _ v' a' hj k Y (fun j l=> ?_) V,(fun i=> P.cinema_pure ..),P.fiscal_camera x g h v' a' hj k s L' (hT.rides p.station.2.1) d t⟩
 exact AtGlassRate.carries j (W j l) q

local notation "G"=> P.ManyF 3 (P.advocate 3 x 3)
lemma packages_rows {Y:Supplier}{L M:ℝ}(e:uniform P K Y L M)(τ:Experiment P K c r x J)(X:ℕ→ P.Apron) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)) (t: GalaxyShow P x g h X V)(p: P.PoweredHeat x V)(T:∀ i,PureGauge P.calibration (X i).F) (n:ℕ→ℕ)(q:P.HandleWith x c r X n):
    ∀ᶠ i:ℕ in atTop,∃ (w:Lead.Clan→ Prism) (F U:SampleDose) (Y:Lead.Clan→ Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3))(Z:Lead.Clan→ Lead.Clan→ Boundary.Distn E4), M4Tuple P K c r x J i F U X n w V g h q Y Z := by
 let B':= P.makeFleet x c r X n τ q t.heat T; let h0(w:Lead.Clan→ Prism):= P.get_armada x X c r n w q V g h t B'
 filter_upwards [P.ordersPrism x g h V 1 t J K reviewEarlierBox reviewLaterBox thinEarlier le_rfl le_rfl τ zero_lt_one] with i he
 obtain ⟨F,U,w,t'⟩:=he
 let z:P.FullPrismLab x X c r n w V g h q 1 F U reviewEarlierBox reviewLaterBox (c i) (r i) K:=P.honorLab x _ _ _ _ _ _ _ _ _ (h0 w) J _ _ _ _ _ _ _ _ thinEarlier le_rfl le_rfl t'
 -- there are implicit arguments. use #check
 have spent(a:Lead.Clan):= P.prism_both_edges x X c r n w a V g h q p z.armada
 obtain ⟨d',l⟩:=Schedule.very_late (daylight (timeMesh P.par)) (a:=2)
 refine ⟨w,F,U,_,_,P.terminalBeta K e,τ,trans6 τ,z.keeps.normalized.1,z.keeps.normalized.2,z.keeps.earlier,z.keeps.laterProbe,z.keeps.fixed.1,z.keeps.fixed.2,z, ?_, p,P.real_order x X c r n w V g h q J F U _ _ K (fun a=> (spent a).2) z,spent,P.fullPrism_azure_margin x X c r n w V g h q F U z,P.fullPrism_azure_limits x X c r n w V g h q F U z,P.fullPrism_excludes_azure_gauge x X c r n w V g h q F U z⟩
 exact ⟨d',P.registerMatched x X c r n w F U q V d' g h _ _ K z l.le,T,P.earnsSplitShadow x X c r n w F U q V g h J z T,P.pulse_components x X c r n w F U q d' V g h z l.le⟩
omit J
#print axioms appointed_camera
#print axioms packages_rows
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
