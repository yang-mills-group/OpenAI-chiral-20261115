import GaugeFieldConstruction.Pisane
import GaugeFieldConstruction.Balala
import GaugeFieldConstruction.Minoa
import GaugeFieldConstruction.Canna
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Esther
import GaugeFieldConstruction.Polder
import GaugeFieldConstruction.Sotto
import GaugeFieldConstruction.Soapstone
set_option autoImplicit false
set_option maxRecDepth 1300
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 180000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {k:Side}{d:ℕ}{x y:Cover}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
-- θ.Ship manifestation $pR`. Tick frame transport from **fixed** Reifier to any actual $l$.
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts YM.GaugeFieldConstruction
local notation "Sp"=>Cauchy.Spin
open scoped Kronecker
namespace Violets
open ArtCart Simmer Py.Rate.LocalLimit.Papal.FrameP
open ArtCart Simmer Py.Rate.LocalLimit.Papal.FrameP
open Spectrix Gleam.Guide.Prims -- namespace tune
variable {O: Type} [NormedAddCommGroup O][InnerProductSpace ℝ O][MeasurableSpace O][BorelSpace O][FiniteDimensional ℝ O]
variable (G:Genre)(Z V:ℝ)(w:300<n.val)
lemma cashM (p:F∈ Glamor (Θk n x) G Z)(h:MatPays F G (Θk n x) c v)(w:300<n.val) : ∀ j:ShapeZ n x G,‖CrispC F x G j‖≤ max |c| (2*|c|):=by
 let o:=Θk n x
 have hp:= (matron p w).1
 cases G with
 | gauge=>intro i; exact ((h.bill none i).trans (le_abs_self _)).trans (le_max_left ..)
 | pure=>
    rintro ⟨i,j⟩; change ‖SipF n x F i j‖≤ _; rw [←FoldF n x F 0,FoldD,norm_mul,show ‖Γpay n x i j‖=1 from (by rw [Γpay,←feesA n x true i j]; apply feeV_n),one_mul];
    have he(k:Bool):‖νTune n x F 0 (bet0 x k i j) Genre.pure‖≤ |c|:=by
       let Z:= hereV n (bet0 x k i j); let V:Fin Genre.pure.orderB → Frills o:= Fin.elim0; refine le_trans ?_ (le_abs_self c); rw [show νTune _ _ _ _ _ _=pracR (Θk n x) F Genre.pure Z V from ?_]; apply h.bill; let c:ℝ:=(Nat.factorial Genre.pure.orderB:ℝ)⁻¹; exact congrArg (fun u:Fin Genre.pure.orderB → tangD n=> c • entry_H F Z Genre.pure.orderB u) (funext fun i:Fin Genre.pure.orderB=>Fin.elim0 (show Fin 0 from i))
    exact (norm_sub_le ..).trans ((add_le_add (he true) (he false)).trans ((le_of_eq (two_mul ..).symm).trans (le_max_right ..)))
 | mixed=>
    rintro ⟨i,j,t⟩; change ‖SipM n x F (Pi.single t 1) i j‖≤_; rw [←FoldM n x _ _ _ _ hp,FoldD,norm_mul,show ‖Γpay n x i j‖=1 from (by rw [Γpay,←feesA n x true i j]; apply feeV_n),one_mul]
    have he(k:Bool):‖νTune n x F (Pi.single t 1) (bet0 x k i j) Genre.mixed‖≤ |c|:= (h.bill (hereV n _) (fun _=>t)).trans (le_abs_self c) -- tune
    exact (norm_sub_le ..).trans ((add_le_add (he true) (he false)).trans ((le_of_eq (two_mul ..).symm).trans (le_max_right ..)))
-- choose bound
lemma kiosk (w:300<n.val): ∃ A0:ℝ,1≤ A0 ∧ ∀ (x:Cover)(F:Paper n), F∈ Glamor (Θk n x) G Z→∀ j:ShapeZ n x G,‖CrispC F x G j‖≤ A0:=by
 obtain ⟨c,v,h,hv,t⟩:= Rc_mo n w Z G; have he: 1 ≤ max |c| (2*|c|):=(h.trans (le_abs_self _)).trans (le_max_left ..)
 exact ⟨_,he,fun x _ p i=> cashM _ _ p (t _ _ p) w i⟩
end Violets
end ArtCart
end MastTin
end YM.CF.XGarden
end
