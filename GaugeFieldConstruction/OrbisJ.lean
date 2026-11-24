import GaugeFieldConstruction.FairNumJ
import GaugeFieldConstruction.SamarsJ
import GaugeFieldConstruction.Energia4
import GaugeFieldConstruction.EarthY
import GaugeFieldConstruction.TurnBridgeJ
import GaugeFieldConstruction.FineAlJ
import GaugeFieldConstruction.PaceDoorJ
import GaugeFieldConstruction.EssenceJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 72000
variable (i k:ℕ) {P' V: Side} {f r t v :ℕ}
local notation "B"=> P.block
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "X_" s:max=> RootBook Y i k s
local notation "µ" s:max=> city (Ω s)
variable {I J G:Type} [Fintype I] [Fintype J][LinearOrder I][LinearOrder J] [LinearOrder G]
variable (p:(Y.voyage i).kick≤ k)
local notation "ν"=> Y.uv k
local notation "θ"=> P.R.L
variable (w:I→G)(X: HousingJ Y i G)(K:G→Prop)(t:f ≤Y.uv k)(E: List I→Orbit (side Y i f)→ Phys (side Y i f))(A:I→Mark (side Y i (Y.uv k)))
variable {N:Side}
variable (σ:I→Seat (side Y i f))(R:I→I→ℂ)
variable (vP:κWork G (Seat (side Y i f)) w σ)
local notation "κ0"=> RevenueT Y i k
local notation "ƒ"=> convoy Y i k t
local notation "Gc"=> city (side Y i (Y.uv k))
-- scalar shift law offset taps
variable (F: Finset I→ RegBudget (side Y i f))(Z:Finset I→ForceBudget (side Y i f))(V:I→ℂ)
local notation "Λt"=> RootBook Y i k f
local notation "Ux"=> (Y.voyage i).CapeT f
open Ing.Ivey Ing.Ivey.ShoreQ Onwards Ing.Iona Fock.Wosk
variable (R:I→FC (Single N))
-- purely combinatorial partitions
lemma skySet (L:List I)(T:Finset I): (Roots.wingX L T).toFinset=L.toFinset∩T:=by ext; simp [Roots.wingX]
lemma miniX (Q:Key I→Phys N)(P:List I)(v:P.Nodup)(p:River Q)(M:List I)(h:M.Nodup)(q:∀ j∈ P,Q∘ dune j=Q): let T:= P.toFinset; let l:= M.toFinset∩T; tipI (fun z=>acts (LaterOp R P z) (Q z)) M=acts ((List.map R (List.filter (·∈ l) P.reverse)).prod) (tipI Q (wingR M l)):=by
 intro T l; let H:= LaterOp R P; let V(l':List I):=(List.map R l').prod; let D:= List.filter (fun i=>decide (i∈l)) P.reverse; let A:= (@fleshB (Single N) _ _)
 have ht: H=brewK R P.reverse:=rfl
 -- selection root.s
 have hc(S:Finset I)(x: S⊆ M.toFinset): (Roots.wingX M S).toFinset=S:=(skySet ..).trans (inter_eq_right.mpr x)
 have hx(S:List I) (e:S.Nodup): tipI H S=if S ⊆ P.reverse then V (List.filter (fun i=>decide (i∈ S.toFinset)) P.reverse) else 0:=by
    rw [ht,survey_cash]; simp only [List.mem_toFinset]; rfl; all_goals first|exact e|simpa using v -- tune
 change tipI (GJ.pulseV A H Q) M=A _ _; rw[distrD A (show River H from brew_R _ _) p _ h]; rw [sum_eq_single_of_mem (s:= M.toFinset.powerset) (f:=fun i=> A (tipI H (Roots.wingX M i)) (tipI Q (wingR M i))) l (mem_powerset.mpr inter_subset_left)]
 · rw [hx _ ((wing_sub M l).nodup h), if_pos ?_,hc l inter_subset_left]
   intro i u; apply List.mem_reverse.mpr; have hp:=List.mem_toFinset.mpr u; rw [hc l inter_subset_left] at hp; exact List.mem_toFinset.mp ((Finset.mem_inter.mp hp).2)
 intro S u e; have hr: S⊆M.toFinset:= mem_powerset.mp u
 rw [hx _ ((wing_sub M S).nodup h)]
 split_ifs with hS; swap; rw [map_zero]; rfl -- tune
 have hX:S⊆l:=by
    intro i b; apply mem_inter.mpr; refine ⟨hr b,List.mem_toFinset.mpr (List.mem_reverse.mp (hS (List.mem_toFinset.mp ?_ )))⟩; rw [hc S hr]; exact b
 obtain ⟨i,pV,y⟩:=not_subset.mp (show ¬l⊆ S from fun v₀=> e (Finset.Subset.antisymm hX v₀))
 let R':= wingR M S; have uE: i ∈ R':=by change i∈ Roots.wingX M _; simp [Roots.wingX,y, List.mem_toFinset.mp (mem_inter.mp pV).1]
 have j:i∈P:=List.mem_toFinset.mp (mem_inter.mp pV).2
 obtain ⟨d,m,a'⟩:= List.append_of_mem uE; have hf: R'.Perm (i::(d++m)):=a' ▸ List.perm_middle
 rw [show tipI Q (wingR M S)=0 from (move_ζ hf p roots).trans ?_,map_zero]; exact tip_charity i Q _ p (q _ j)
-- Masks by cuts
lemma restrictedT {N:Type}[NormedAddCommGroup N][NormedSpace ℂ N][CompleteSpace N](f g:Key I→N)(T:Finset I) (s:List I)(e:∀ i∈T,i∉s)(h:∀ i∈hill I,(∀ j∈T,i j=0)→ f i=g i): tipI f s=tipI g s:=by
 induction T using Finset.induction_on generalizing f g with
 | empty=> exact lace_C s (fun i v=> h i v (by simp)) roots
 | insert i T u ih=>
    rw [←tip_V (f:=f) i s (e _ (mem_insert_self ..)),←tip_V (f:=g) i s (e _ (mem_insert_self ..))]; refine ih _ _ (fun j t=>e j (mem_insert_of_mem t)) (fun x p v=> h _ (dune_P i p) (fun j t=>?_)); by_cases h:j=i; · rw[h,dune,update_self]
    rw [dune, update_of_ne h,v j ((mem_insert.mp t).resolve_left h)]
variable (Q:List I)(PxN: Q.Nodup)(x0:Orbit (side Y i f))(H:I→ FC (Single (side Y i f)))
local notation "ι'"=> Q.toFinset
local notation "V0"=> CrushJ (Q.toFinset) F
local notation "Vk"=> CrushJ (Q.toFinset) Z
local notation "ΦD"=> Ask Y i k σ F Z
include PxN
lemma Orbis (s:List I)(p:s.Nodup): let l:= s.toFinset∩ Q.toFinset;
   tipI (fun z=> acts (LaterOp H Q z) (denZ (BreathJ Λt σ V0 Vk 0 z) P.U Ux x0)) s=acts (((Q.reverse.filter (·∈l)).map H).prod) (ΦD 0 (wingR s l) x0):=by
 intro l; let Q0(z:Key I):=denZ (BreathJ Λt σ F Z 0 z) P.U Ux x0; let P0(z:Key I):=denZ (BreathJ Λt σ V0 Vk 0 z) P.U Ux x0
 have hp :River P0:= inputRunV Y i k σ V0 Vk 0 (zeroR _) _; have he(z):P0 z= Q0 (veilJ Q.toFinset z):=by simp [P0,Q0,BreathJ,craveJ] -- tune Z shadow
 have e(i:I)(t:i∈ Q): P0∘ dune i=P0:=by
    funext z; rw [comp_apply,he,he]; apply congrArg Q0; funext j; unfold veilJ; split; rfl; next v=>exact update_of_ne (fun p:j=i=> v (p.symm ▸ List.mem_toFinset.mpr t)) _ _
 let f:= miniX H P0 Q PxN hp s p e; refine f.trans ?_; apply congrArg (fun x=> acts _ x); change tipI P0 _=tipI Q0 _; apply restrictedT _ _ (Q.toFinset) -- tune
 · intro i t g; obtain ⟨u,e⟩:= List.mem_filter.mp g; exact (mem_compl.mp (of_decide_eq_true e)) (mem_inter.mpr ⟨List.mem_toFinset.mpr u,t⟩)
 intro i _ V; rw [he]; apply congrArg Q0; funext j; unfold veilJ; split; exact (V _ (by assumption)).symm; rfl
#print axioms Orbis
#check tip_charity
#check fleshB
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
