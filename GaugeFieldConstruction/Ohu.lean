import GaugeFieldConstruction.MomArt
import GaugeFieldConstruction.Olla
import GaugeFieldConstruction.Synod
import YM.UVNext.PRICED_KERNELS.Basin
import YM.CF.Yaw.Viv
import GaugeFieldConstruction.Plaid
import GaugeFieldConstruction.Corbie
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
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
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
-- comparison at any ordered roots, including swapping order if word products price same (test via ∀sublists). Keys.C.
variable (F':Fork n I)(r':ℝ)(W:Support (More n))(B:Pane n)(N:I→Boke n I)(σ':I→Seat n)(v':stabH F')
variable (U:UNI (Single n))(p b:Bool)
local notation "Q'"=>paintR p b U
local notation "Rλ"=>lotY p b U
local notation "H_F"=> cryH F V (0:Key I) A
local notation "H'_F"=> cryH F' W (0:Key I) B
variable {m:Type}[LinearOrder m][Fintype m]
lemma arch_F (Y Z:FC (FinV n))(h: acts Y (vacuum (FinV n))=acts Z (vacuum _)): acts (Rλ Y) (vacuum (FinV n))=acts (Rλ Z) (vacuum _):=by
 let s:=p.xor b; let V:=spice U b; let P:= quantU V
 have hf(X:FC (FinV n)): acts (Rλ X) (vacuum (FinV n))= acts P.val (dove s (acts X (vacuum (FinV n)))):=by
    change acts (sings s _ X) _=_; rw [singT,twist_formula]; let x:=vacuum (FinV n); change acts (P.val*_ *star (quant V.val)) x=_; rw [act_mul,remove_vac_pair,act_mul,dove_acts,show dove s x=x from dove_base ..] -- P.val whnf infer type
 rw [hf,hf,h]
include v v'
variable (L T:List I)(h:L.Nodup)(t:T.Nodup)(hs:stampK M L)(ht:stampK N T)
local notation "P0"=> disks I V A (Keeps F r M L)
local notation "Pv"=> disks I W B (Keeps F' r' N T)
open NormedSpace
omit v v'
lemma ask_H (X:Dough (FinV n)): VogueΓ X= acts X.val (vacuum (FinV n)):=by change _ =_; change acts ((Pastry.cane _).cook X) _=_; rw [Poly_Φ] -- omit p
include h t hs ht v v'
lemma Scroll_M (g:List I)(hg:ψS σ g)(hu:ψS σ' g)(υ:g⊆L)(τ:g⊆T)(pF:∀ l:List I,l.Sublist g → ((skimT I T l).map fun i=> artΨ0 I W B H'_F (N i)).prod= Rλ (((skimT I L l).map fun i=>artΨ0 I V A H_F (M i)).prod)):tipI Pv g=Q' (tipI P0 g):=by
 -- θ symbol orientation.At pivot. log.Z indexes
 refine stem_path (Seat n) σ P0 (γRise_P ..) Pv ((paintR p b U).toRingHom) g hg (disk_Z I V A M F r v L hs) (disk_Z I W B N F' r' v' T ht) (γRise_P ..) ?_
 intro l w; apply vogue_inj
 let Gζ:=tipI (exp ∘ P0) l; let X:= ((skimT I L l).map fun i=>artΨ0 I V A H_F (M i)).prod
 have hv: VogueΓ Gζ=acts X (vacuum _) := Memo I σ V A M F r v L h hs l (List.Subset.trans w.subset υ) ((w.map σ).nodup hg)
 -- local notation initial arg order V x σ? verify
 have hK:= Memo I σ' W B N F' r' v' T t ht l (List.Subset.trans w.subset τ) ((w.map σ').nodup hu); rw [pF _ w] at hK; refine hK.trans ?_; rw [ask_H ..] -- includes args?!
 rw [ask_H ..] at hv; exact arch_F _ _ _ _ Gζ.val hv.symm
-- global when order unchanged.
omit v v' h t hs ht
#print axioms Scroll_M
end MastTin
end YM.CF.XGarden
end
