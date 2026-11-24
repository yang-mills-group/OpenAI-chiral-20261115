import YM.CF.DPress.Chess.Green.Porus
import YM.CF.Chaff.Diet
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Green
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube RP Phase Branch Mir Mir.Trip Brace Nacre Window Tenant
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m B:Side}{l':Site (More m)}
local notation "V_"=> CSide m B
local notation "I_"=> northTrip m l'
local notation "α_"=> W.i
local notation "κ_"=> mealU (lagX W.od) 1 inert (V_)
local notation "J_"=>costarU m B l' (northZ m B) W.i
local notation "Θc"=> seamShift m B W.i
namespace Mirror
open Spark
variable (F:Fixed.Test (CSide m B))
def ν(F:Fixed.Test (CSide m B)) (x: Pack m B):FC (Model (CSide m B)) := twist (quantU (costarU m B l' (northZ m B) W.i)) (crossL (helix _).symm (F (through B (northTrip m l')⁻¹ x.1)))
variable (p:Attend W B l')(g:Boss (CSide m B) (W.crop (CSide m B) 0) F)
include p g F
lemma give (h:Continuous F): OfferedF m B W.i (ν W (l':=l') F) false:=by
 obtain ⟨u,g⟩:=g; have hu:Continuous (through B (I_)⁻¹):= Wilson.continuous_pull ..; exact ⟨(breeze (quantU (costarU m B l' (northZ m B) W.i))).comp ((Spark.cxC _).comp (h.comp (hu.comp continuous_fst))),fun x=>twist_Ty (J_) (port_Γ W p) (site_h W (g.even _)),fun x y u=> by unfold ν; rw [g.reads _ _ (Green.reading W p u.gaugeS)]⟩ -- tune
lemma look : squareR m B l' (northZ m B) W.i (ν W (l':=l') F) false= Chaff.leer m B (peer W F * F) :=by
 obtain ⟨u,g⟩:=g; let U:=J_; let C:= quantU U; let A:= ν W (l':=l') F; funext i; let α:=onPack B (I_) i; let V:=i.1
 let R:= (helix (CSide m B)).symm; have hu:A α=twist C (crossL R (F V)):=congrArg (fun x=> twist C (crossL R (F x))) (backT (l':=l') V); have ht:A (Pbar m B W.i α)= twist C (crossL R (F (W.shine V_ V))):=congrArg (fun x=> twist C (crossL R (F x))) (sendU W p W V)
 let Z:=crossL R (W.θ _ (F (W.shine _ V))*F V); change twist (star C) (Reflect.chord false • (theta (finger m B W.i) (A (Pbar m B W.i α)) * A α)) = Z; unfold Z; rw [show Reflect.chord false=(1:ℂ) from rfl,one_smul,ht,hu]; rw [←inter_κ W p (g.even (W.shine _ V)), Spark.cx_m,← map_mul, twist_inv] -- tune order
end Mirror
end YM.CF.DPress.Chess.Green
#print axioms YM.CF.DPress.Chess.Green.Mirror.look
