import YM.SU5.Assay.Film
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration
variable {c:Option Bool}{a b x y:P.Test}
/-!
# Billing book of a flash N. Internal order over colors not significant.
-/
variable (P)
variable {n:ℕ}(A:Lead n)(Z:Lead.Clan)
local notation "C"=>Window.colors Z
open Film
local notation "w"=> Film.wire P A
local notation "e"=>Film.ember P A
noncomputable def stockFolio : P.Folio:=
 let v:P.Folio:= Finset.toList (C) |>.flatMap (fun i=>(Finset.toList (C)).flatMap fun j=>[(Film.wire P A i j, Film.ember P A i j)])
 v.ink (Lead.sing n A.wave)
lemma stock_paid_eq :P.stockS Z A=Lead.sing n A.wave • ∑ i∈ Window.colors Z,∑ j∈ Window.colors Z, w i j * e i j:= by
 apply Subtype.ext
 let F(i j:SU.Slot):=coilC A i j*trailC A i j
 have hp: Papal.household K (A.groundWord Z)= Lead.sing n A.wave • ∑ i∈Window.colors Z,∑ j∈Window.colors Z,Papal.household K (F i j):=by rw [Lamour.Bridge.Celeste.banner_sum]; unfold Papal.household; funext m; simp_rw [Pi.smul_apply,Finset.sum_apply];rfl
 apply hp.trans
 change _=(screenHall K).val (Lead.sing n A.wave • ∑ i ∈ (C), ∑ j ∈ (C), w i j * e i j)
 simp only [map_smul,map_sum]; rfl
lemma stock_prices (h:nodeC A.birth≠nodeC A.death):
 P.Wove (some Z.2) A.patio (P.stockS Z A) (P.stockFolio A Z):=by
 let g:GVertex:=fun i=> if i=nodeC A.death then SU.central else 1
 rw [P.stock_paid_eq]
 unfold stockFolio
 -- letI? reduce let
 apply Wove.smul
 exact Wove.stapleMore _ _ (C) (fun _ p=> Wove.stapleMore _ _ (C) (fun _ q=>Wove.fibre (write_price _ _ _ _ _ g (if_neg h) (if_pos rfl) p q)))

noncomputable def defaultFolio (n:ℕ):P.Folio:= (P.stockFolio (P.flash n) Z).ink ((↑(purePrice Z):ℂ)⁻¹)
lemma flash_prices (h:P.calibration.ℓ<n):P.Wove (some Z.2) (P.flash n).patio (P.defaultR Z n) (P.defaultFolio Z n):=by
 have hp:=Finset.disjoint_left.mp (P.pin_disjoint _ _ _ (P.pocket_gap 0 n h)) (Finset.mem_singleton_self _)
 exact Wove.smul (P.stock_prices (P.flash n) Z (fun t=>hp (Finset.mem_singleton.mpr t))) _
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
