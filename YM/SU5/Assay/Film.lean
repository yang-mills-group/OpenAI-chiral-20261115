import YM.SU5.Assay.Wove
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
# Native components from actual Wilson coefficients x chiral bilinears,
with termwise credentials. The label $Z$ retained in the raw formulas.
-/
namespace Film
variable {n:ℕ}(A:Lead n)(Z:Lead.Clan)(i j:SU.Slot)
variable (P)
local notation "U"=>A.patio
noncomputable def wire:P.Test:= ⟨Papal.household K (coilC A i j),
   broadCompile K U (InTest.seed (coil_paid A i j)).widen⟩
lemma ember_licensed : InTest K false U false (Papal.household K (trailC A i j)):=
 InTest.mul (f:=removal K A.death (dnSpin A.slot) j) (g:=creation K A.birth (upSpin A.slot) i)
 (.remover j (dn_half _) (porchGone A)) (.creator i (up_half _) (porchBorn A))
noncomputable def ember:P.Test:= ⟨_,broadCompile K U (ember_licensed P A i j).widen⟩
variable (g:Cover→SU.E)(u:g (nodeC A.birth)=1)(w:g (nodeC A.death)= SU.central)
variable (p:i∈Window.colors Z)(v:j∈Window.colors Z)
local notation "q"=>phaseName Z.2
include u v w
private lemma coil_weight (X:LinksC): coilFlag A i j (Lattice.gauge g X)= q⁻¹ * coilFlag A i j X:=by
 have h:(Window.family j).2=Z.2:=congrArg Prod.snd (Finset.mem_filter.mp v).2
 unfold coilFlag
 rw [travel_gauge,A.moves,u,w,one_mul]
 let t:= Lattice.travel X (nodeC A.birth) A.traceV
 let t':=t*SU.central⁻¹
 have hp:(matter t').val*(matter SU.central).val = (matter t).val:=congrArg Subtype.val
    (show matter t' * matter SU.central = matter t by rw [←map_mul]; unfold t'; rw [inv_mul_cancel_right])
 have e:(matter t').val i j * q = (matter t).val i j:=by
   rw [by_charge] at hp
   rw [←hp,Matrix.mul_diagonal,←charge_identity,h]
 have ne:q≠0:= norm_ne_zero_iff.mp (by rw [pname_unit]; norm_num)
 change (matter t').val i j= _
 rw [←e,mul_comm ((matter t').val i j),inv_mul_cancel_left₀ ne]

private lemma coil_circle : Circular U g (Papal.household K (coilC A i j)) (q⁻¹•Papal.household K (coilC A i j)):=by
 let f:=coilFlag A i j
 intro m G h V
 let R:=(K).c m
 let ff:LinksC:=onC R V.1
 have r: f (onC R (Lattice.gauge G V.1))= f (Lattice.gauge g ff):=
   (coil_paid A i j).locus (onC R (Lattice.gauge G V.1),onC R (Lattice.gauge G V.2))
     (Lattice.gauge g ff,Lattice.gauge g (onC R V.2)) (gauge_trace g h V.1) (gauge_trace g h V.2)
 let uR:=tradew R G
 change f (onC R (Lattice.gauge G V.1)) • (1:FC (Single R))=twist (quantU uR) (q⁻¹ • (f ff • (1:FC (Single R))))
 rw [smul_smul,twist_scalar,map_one]
 exact congrArg (fun z:ℂ=>z • (1 : FC (Single R))) (r.trans (coil_weight A Z i j g u w v ff))
lemma wire_price : pennant K g (wire P A i j)= q⁻¹•wire P A i j:=by
 let x:=wire P A i j
 have ht:P.Yarn U x:= ⟨_,coil_paid A i j,rfl⟩
 exact appointed K U g x (q⁻¹•x) (coil_circle P A Z i j g u w v) ((bay K U true).smul_mem
   (widerBay K U false ht.part) q⁻¹)
include p
lemma ember_price :pennant K g (ember P A i j)=q•ember P A i j:=by
 let S:=({nodeC A.birth}:Finset Cover); let T:= ({nodeC A.death}:Finset Cover)
 have hl:removal K A.death (dnSpin A.slot) j∈ SinglePocket K Z.2 T false:= pocket_removal K Z.2 T
    (Finset.mem_singleton_self _) (congrArg Prod.snd (Finset.mem_filter.mp v).2) (dn_half _)
 have hr:creation K A.birth (upSpin A.slot) i∈ SinglePocket K Z.2 S true:=pocket_creation K Z.2 S
    (Finset.mem_singleton_self _) (congrArg Prod.snd (Finset.mem_filter.mp p).2) (up_half _)
 have hx:(ember P A i j).val∈RawPair K Z.2 S T:= Submodule.subset_span (show _∈_ from ⟨_,hl,_,hr,rfl⟩)
 have hd:S∪T⊆A.patio:= Finset.union_subset (Finset.singleton_subset_iff.mpr (porchBorn A)) (Finset.singleton_subset_iff.mpr (porchGone A))
 exact appointed K U g _ _ (pocket_charge K Z.2 S T U g hd (fun _ h=> Finset.mem_singleton.mp h ▸ u) (fun _ h=>Finset.mem_singleton.mp h ▸ w) hx)
   ((bay K U true).smul_mem (show ember P A i j∈bay K U true from (ember_licensed ..).widen) _)
lemma write_price : P.Fibre (some Z.2) U (wire P A i j) (ember P A i j):=by
 refine ⟨⟨_,coil_paid A i j,rfl⟩,fun _ _ _=>rfl,ember_licensed ..,fun W x=>?_⟩
 obtain rfl:=Option.some.inj x.symm -- subst W?
 exact ⟨g,wire_price _ _ _ _ _ g u w v,ember_price _ _ _ _ _ g u w p v⟩
end Film
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
