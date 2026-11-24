import GaugeFieldConstruction.Laps
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
variable (I:Type)[LinearOrder I][Fintype I]{G:Type}[LinearOrder G][Fintype G](J:Type)[DecidableEq J]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
def disks (S:Boke n I) :Key I→Dough (FinV n):= Bore0 V A S
#print disks
abbrev skimT (L T: List I):= L.filter fun i=>decide (i∈T)
def artΨ0 (K:FinV n→ FinV n→ℂ)(x:Boke n I): FC (FinV n):= binW (Icycle K) (cryY V (1:Key I) A x)
lemma Brew_H (H:FinV n→ FinV n→ℂ)(L:List I)(p:stampK M L)(z:Key I): surveyR V A M (Icycle H) L z= brewK (fun i=>artΨ0 I V A H (M i)) L z:=by
 unfold surveyR brewK; refine congrArg List.prod (List.map_congr_left (fun i v=>?_)); rw [front_U i (M i) V A z (p i v),map_smul]; rfl -- tune
open NormedSpace
-- trust by Dough ext
lemma Poly_Φ (g:Dough G): (Pastry.cane G).cook g=g.val:=by
 change Poly.eval _ _=g.val; nth_rw 1 [(fineShape g).allP]; rw [map_sum]; simp_rw [map_smul, Poly.eval_oneT]; exact (fineShape _).allP.symm -- tune
abbrev VogueΓ : (Dough G) →L[ℂ] Wave G := (seeF (vacuum G)).comp (seeFC (Pastry.cane G))
lemma vogue_inj :Injective (VogueΓ (G:=G)):=by
 intro x y q; change acts ((Pastry.cane G).cook x) (vacuum G)=acts ((Pastry.cane G).cook y) (vacuum G) at q; rw [Poly_Φ,Poly_Φ] at q
 apply Subtype.ext; change x.val=y.val; conv_lhs=>rw [(fineShape x).allP]
 conv_rhs=>rw [(fineShape y).allP]
 apply sum_congr rfl; intro i _; rw [Sault.col, Sault.col,q]
include v
lemma Memo (L:List I)(h:L.Nodup)(p:stampK M L)(Y:List I)(t:Y⊆L)(s:ψS σ Y):
  VogueΓ (tipI (exp ∘ disks I V A (Keeps F r M L)) Y)=acts (((skimT I L Y).map fun i=>artΨ0 I V A (cryH F V (0:Key I) A) (M i)).prod) (vacuum (FinV n)):=by
 let Z:= disks I V A (Keeps F r M L); let H(i:I):= artΨ0 I V A (cryH F V (0:Key I) A) (M i); let K:=cryH F V (0:Key I) A; let Q:= Icycle K
 let f(z:Key I):=acts (brewK H L z) (vacuum (FinV n)); let D:= exp ∘ Z
 have hh:River D:= (γRise_P _ _ (Keeps F r M L)).exp_V
 have hx: tipI (VogueΓ ∘ D) Y= VogueΓ (tipI D Y):= sim_H hh VogueΓ Y roots
 rw [← hx]; apply Eq.trans _ ((show tipI f Y= _ from ?_))
 · have hg:= Formal_Canon V σ A F r M (Pastry.cane (FinV n)) Q (iceK K) K (vacuum _) (heroK K) L (cry_H F v V A) (fun i u z h=> Eq.trans (front_U i (M i) V A z (p i u)) (by rw [h,zero_smul]))
   simp_rw [show ∀ z:Key I, surveyR V A M Q L z= brewK H L z from fun i=> Brew_H I V A M K L p i] at hg; exact hg.queen Y s
 rw [show tipI f Y= acts (tipI (brewK H L) Y) (vacuum (FinV n)) from sim_H (brew_R H L) (seeF (vacuum (FinV n))) Y roots,survey_cash H L h Y (List.Nodup.of_map σ s),if_pos t]
#print axioms Memo

lemma disk_Z(L:List I)(p:stampK M L): disks I V A (Keeps F r M L) 0=0:=by
 let K:=Keeps F r M L; have hv: cryY V 0 A K=0:=by
    unfold cryY; suffices he:∀ S: Boke n I,S.Sublist K→ Lee S (fun e=>egest e V 0 A • (Pi.single e.val 1:PairLog (FinV n)))=0 from he K (List.Sublist.refl _)
    intro S; induction S with|nil=>intro; rfl|cons i l ih=> intro t; rw [consA,ih ((List.sublist_cons_of_sublist i (List.Sublist.refl l)).trans t),add_zero]; have hp:= deepH r F M L p i (t.subset List.mem_cons_self); unfold egest GJ.stalk; cases v:i.keys with|nil=> contradiction| cons j l=> simp
 unfold disks Bore0; rw [hv,map_zero]
end MastTin
end YM.CF.XGarden
end
