import YM.CF.BPress.Homes.Window
import YM.CF.BPress.Mount.Extends
/-!
 Use the full B-phase extension procedure even off the produced assembled
 data. This last property isn't needed to pay any of the contour weights.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Homes
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Extensor Mount
variable {s m B N:Side}
variable {U:Driver (mid m B)}{F:GramM (mid m B)}{G:Brace.Duet m B}{Y Z T A:Pledge}{V:Wish U Y Z T}{P:Edition U}{a q g u v:ℝ}
variable {α:Type*}(R:α→ U.Pose)
structure Sealbook (C:Calyx P R) : Prop where
 body(t)(x:U.Pose): C.body t x.val=P.op t x
 hull(t)(x:U.Pose): C.hull t x.val=P.reg t (x,x.val.G)
lemma portfolio(H:Passports U F G V P A a q g u v): ∃ C:Calyx P R, Sealbook R C:=by
 let X:=U.Pose; haveI:StandardBorelSpace U.Pose:=domain U V
 obtain ⟨C⟩:= mounting H (fun x:X=>x) (measurable_id' (α:=X)); refine ⟨⟨C.body,C.hull,C.pay,C.phaseRec,fun i t=>C.eye (R i) t,fun i t=>C.C_eye (R i) t⟩,⟨fun t x=>C.eye x t,fun t x=>C.C_eye x t⟩⟩
end YM.CF.BPress.Homes
#print axioms YM.CF.BPress.Homes.portfolio
