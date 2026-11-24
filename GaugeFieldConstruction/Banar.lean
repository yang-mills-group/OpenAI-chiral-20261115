import GaugeFieldConstruction.Telamp
import GaugeFieldConstruction.Fink
import GaugeFieldConstruction.Fume
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
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
variable (σ:I→Seat n)(Vα:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (tι:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
variable (TX: Sweep n)(P:BudgetPoint)(L:ℕ)(x:Scree.Hub n)
-- slotwise description of table variations including same orientation. no inequality used on Tensor powers.
variable (J:Type)[LinearOrder J][Fintype J]
variable (s:I→J)(N:J→ Boke n J)(F':Fork n J)(σ':J→Seat n)
variable (p:List I)(q:List J)(Y0:List I)(h:p.Nodup)(Lq:q.Nodup)(u:Y0⊆p)(Q':Y0.map s⊆q)
variable (vξ:stampK M p)(wξ:stampK N q)(vA:ψS σ Y0)(b:∀i∈Y0,σ' (s i)=σ i)(v':stabH F')
lemma ξNod_s : ψS σ Y0→(∀i∈Y0,σ' (s i)=σ i)→ ψS σ' (Y0.map s):=by intro q p; unfold ψS; rw [List.map_map,List.map_congr_left (f:=σ'∘s) (g:=σ) (fun i t=>p _ t)]; exact q
include u h Lq Q' vA v b v' vξ wξ
variable (G:I→ Torches n)
-- order Forward with support limb not moved.
variable (Qμ:∀i∈Y0,∃ f g h c v,Bouquet I i P f g h v (G i) σ (M i) c)(Pμ:∀ i∈Y0,∃ f g h c v,Bouquet J (s i) P f g h v (G i) σ' (N (s i)) c)
variable (B:∀ X: Support (More n),∀ A:Pane n,cryH F X 0 A=cryH F' X 0 A)(t:∀ l:List I,l.Sublist Y0 → skimT J q (l.map s)=(skimT I p l).map s)
include B Qμ Pμ t
local notation "EC"=> Keeps F r M p
local notation "ET"=> Keeps F' r N q
local notation "σς"=> Y0.toFinset
local notation "σρ"=> (Y0.map s).toFinset
open NormedSpace
lemma wrap_V : cacheS J σ' σρ S ET= cacheS I σ σς S EC:=by
 funext A
 have hv:= ξNod_s I σ J s σ' Y0 vA b
 apply sub_eq_zero.mp; apply cache_H S (fun S=>cacheS J σ' σρ S ET A-cacheS I σ σς S EC A); intro X _
 rw [sum_sub_distrib]; apply sub_eq_zero.mpr; rw [←Disk_version I σ X A EC Y0 vA,←Disk_version J σ' X A ET (List.map s Y0) hv]
 symm; apply same_R s _ _ (γRise_P ..) (γRise_P ..) Y0 (List.Nodup.of_map σ vA) (List.Nodup.of_map σ' hv) (disk_Z _ _ _ _ _ _ v _ vξ) (disk_Z _ _ _ _ _ _ v' _ wξ)
 intro l z; change tipI (exp ∘ disks J X A ET) (l.map s)=tipI (exp∘ disks I X A EC) l; apply vogue_inj; rw [Memo J σ' X A N F' r v' _ Lq wξ _ (List.Subset.trans (z.map s).subset Q') (((z.map s).map σ').nodup hv), Memo I σ X A M F r v _ h vξ _ (List.Subset.trans z.subset u) ((z.map σ).nodup vA),t l z, List.map_map]; apply congrArg (fun x=> acts x (vacuum (FinV n))); apply congrArg List.prod; refine List.map_congr_left fun i w=> ?_
 let hx:= z.subset (a:=i) (of_decide_eq_true (List.mem_filter.mp w).2); obtain ⟨a,b0,h,c,v',Qk⟩:= Qμ i hx; obtain ⟨a',b',h',c',v1,Qm⟩:= Pμ i hx
 unfold Function.comp artΨ0; rw [B X A]; dsimp only; rw [Bloom_M J X A (s i) _ a' b' h' v1 (G i) _ _ Qm, Bloom_M I X A i _ a b0 h v' _ _ _ Qk,b i hx]
variable (b0:darkH F)(b1:darkH F')
include b0 b1
lemma wrapκ_cur (f:(σς).card=1): cacheS J σ' σρ S (foli ET)= cacheS I σ σς S (foli EC):=by -- issue macros.field
 obtain ⟨i,g⟩:=Finset.card_eq_one.mp f; have ht:σρ={s i}:=by rw [κMap,g,image_singleton]
 have hp:i∈Y0:= List.mem_toFinset.mp (by rw [g]; exact mem_singleton_self _)
 obtain ⟨a,B,h0,D,E,vΘ⟩:= Qμ i hp; obtain ⟨a',b',h',c',v4,x0⟩:=Pμ i hp -- shadow
 rw [ht,g, Ink_sageY J σ' N F' r S _ v' b1 q Lq wξ (Q' (List.mem_map_of_mem hp)), Ink_sageY I σ M F r S i v b0 p h vξ (u hp),bonO I σ S M P a B h0 E D G _ vΘ]; rw [bonO J σ' S N P a' b' h' v4 c' (fun _=> G i) _ x0,b i hp]
lemma wrapκ : entryS σ' L P ET σρ x=entryS σ L P EC σς x:=by
 have hp:(Finset.image σ' σρ)=(Finset.image σ σς):=by rw [κMap, image_image]; exact Finset.image_congr fun i v=> b i (List.mem_toFinset.mp v)
 have hv:= ξNod_s I σ J s σ' Y0 vA b
 have hc:(σρ:Finset J).card=(σς:Finset I).card:=by rw [List.toFinset_card_of_nodup (List.Nodup.of_map σ vA),List.toFinset_card_of_nodup (List.Nodup.of_map σ' hv),List.length_map]
 have hg(S b):QuotaΥ J σ' σρ S L P b x=QuotaΥ I σ σς S L P b x:=by simp only [QuotaΥ,MarksΥ,padS,hp,hc]
 rw [sum_stamp,sum_stamp]; apply sum_congr rfl; intro S _; simp_rw [hg, hc,wrap_V I σ M F r v S P J s N F' σ' p q Y0 h Lq u Q' vξ wξ vA b v' G Qμ Pμ B t]; split; next hK=> rw [wrapκ_cur I σ M F r v S P J s N F' σ' p q Y0 h Lq u Q' vξ wξ vA b v' G Qμ Pμ B t b0 b1 hK]
 rfl
#print axioms wrapκ
end MintB
end MastTin
end YM.CF.XGarden
end
