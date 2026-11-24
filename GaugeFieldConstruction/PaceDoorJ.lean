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
lemma totesCJ {b:Bool}{S:Support (More N)} (U:I→Mark N)(T:Finset I)(h:∀ i∈T,PostSupport b S (U i)): PostSupport b S (∑ i∈T,U i):=by induction T using Finset.induction_on with|empty=> rw[sum_empty];exact PostSupport.zeroM| insert i T g ih=> rw [sum_insert g]; exact (h _ (mem_insert_self ..)).addM (ih fun _ p=>h _ (mem_insert_of_mem p))
lemma rackTJ (U:I→Orbit N→Phys N)(T:Finset I) (h:∀ i∈T,Version (city N) (U i)): Version (city N) (∑ i∈T,U i):=by
 induction T using Finset.induction_on with|empty=>rw[sum_empty]; exact ver_of (u:=fun _:Orbit N=>(0:Phys N)) ⟨measurable_const,0,fun _=>le_of_eq (norm_zero)⟩|insert i T q ih=> rw [sum_insert q]; exact plusV (h _ (mem_insert_self ..)) (ih fun i p=>h _ (mem_insert_of_mem p))
lemma debt0K (Z:Scree.Loom N)(Q:Mark N): markedRead Q Z (0:Orbit N→Phys N)=0:=by unfold markedRead; simp
lemma debt0U (Z:Scree.Loom N)(V:Orbit N→Phys N): markedRead 0 Z V=0:=by unfold markedRead; simp_rw [Pi.zero_apply]; unfold letterRead; simp only [ContinuousLinearMap.comp_apply,map_zero,ContinuousLinearMap.zero_apply,integral_zero]
lemma cost_sumJ (U: J→ Mark (side Y i f))(T:Finset J)(S:Orbit (side Y i f)→Phys (side Y i f))(p:∀ i∈T,PostSupport false univ (U i))(v:Version (city _) S) : markedRead (∑ i∈T,U i) ((Y.voyage i).CapeT f) S= ∑ i0∈T,markedRead (U i0) ((Y.voyage i).CapeT f) S:=by
 induction T using Finset.induction_on with
 | empty=>rw[sum_empty,sum_empty]; exact debt0U _ _
 | insert j T g ih=> have Q(j)(x:j∈T): PostSupport false univ (U j):=p j (mem_insert_of_mem x); rw [sum_insert g,sum_insert g,palm_plus Y i _ (p j (mem_insert_self ..)).env (totesCJ U T Q).env v,ih Q]
lemma cost_vJ (U:J→ Orbit (side Y i f)→Phys (side Y i f))(T:Finset J) (h:∀ i∈T,Version (city _) (U i))(A:Mark (side Y i f))(p:Envelope A): markedRead A ((Y.voyage i).CapeT f) (∑ i∈T,U i)=∑ j∈T,markedRead A ((Y.voyage i).CapeT f) (U j):=by
 induction T using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact debt0K _ _
 | insert j T g ih=> have hp(a)(u:a∈T): Version (city _) (U a):=h a (mem_insert_of_mem u); rw [sum_insert g,sum_insert g]; exact (ring_plus (f:=f) Y i A p (h _ (mem_insert_self ..)) (rackTJ U T hp)).trans (congrArg (_+ ·) (ih hp))
section snowJ
variable (σ:I→Seat (side Y i f))(R:I→I→ℂ)
abbrev κWork (Q R: Type)(x:I→Q)(y:I→R): Prop:=∀ i j:I,x i=x j↔ y i=y j
variable (vP:κWork G (Seat (side Y i f)) w σ)
include vP
lemma fondΩ (l t:List I)(h:l.map σ=t.map σ): l.map w=t.map w:=by
 induction l generalizing t with
 | nil=> have H:t=[]:=by simpa using h.symm
         rw[H]
 | cons j l ih=>cases t with
    | nil=>simp at h
    | cons t z=>simp only[List.map_cons,List.cons.injEq] at h ⊢; exact ⟨(vP ..).2 h.1,ih z h.2⟩
lemma gala_ψ (L:List I) (h:galaJ w L):ψS σ L:=by
 induction L with
 | nil=> simp [ψS]
 | cons i l ih=> obtain ⟨p,e⟩:= List.pairwise_cons.mp (show List.Pairwise (·<·) _ from h); refine List.nodup_cons.mpr ⟨?_,ih e⟩; intro v; obtain ⟨x,h,w'⟩:=List.mem_map.mp v; have he:= p (w x) (List.mem_map_of_mem h); exact (ne_of_lt he) ((vP ..).mpr w'.symm)
omit vP
abbrev turnoverJ (Q:List I→ Orbit N→Phys N)(C:I→I→ℂ)(t:List I)(x:Orbit N):= Roots.snow σ C (fun l=>Q l x) t
abbrev perturbJ (A:I→Mark N)(C:I→I→ℂ)(i:I): Mark N:= ∑ j∈pipe_ζ σ i,C j i • A j
lemma artEq (X:List I→ Orbit N→Phys N)(l:List I)(a:I) : turnoverJ Y i σ X R (a::l)= ∑ j∈pipe_ζ σ a, R j a • turnoverJ Y i σ (fun s=>X (j::s)) R l:=by funext x; unfold turnoverJ; rw[Roots.snow,Finset.sum_apply]; rfl
lemma permit_S (L: List I)(S:List I→ Orbit N→Phys N)(p:∀ T,T.map σ=L.map σ→Version (city N) (S T)):Version (city N) (turnoverJ Y i σ S R L):=by
 induction L generalizing S with
 | nil=> exact p _ rfl
 | cons j l ih=> rw [artEq]; refine rackTJ _ _ fun k q=> multV (ih _ ?_); intro T x; exact p (k::T) (by rw [List.map_cons,List.map_cons,x,(mem_filter.mp q).2])
lemma red_bill (L:List I)(S:List I→Orbit (side Y i f)→ Phys (side Y i f))(q:Mark (side Y i f))(e:Envelope q)(h:∀ T,T.map σ=L.map σ → Version (city _) (S T)): markedRead q ((Y.voyage i).CapeT f) (turnoverJ Y i σ S R L)= Roots.snow σ R (fun l=>markedRead q ((Y.voyage i).CapeT f) (S l)) L:=by
 induction L generalizing S with
 | nil=> rfl
 | cons j l ih=>
    have p (k)(t:k∈pipe_ζ σ j)(T:List I)(v:T.map σ=l.map σ): Version (city _) (S (k::T)):= h _ (by rw [List.map_cons,List.map_cons,v,(mem_filter.mp t).2])
    rw [artEq,cost_vJ]; rotate_left
    · exact fun i0 t=>multV (permit_S Y i σ R l _ (p _ t))
    · exact e
    rw [Roots.snow]; exact sum_congr rfl fun k t=>(ring_scale Y i q (R k j)).trans (congrArg (fun x:ℂ=>R k j • x) (ih _ (p k t)))
lemma homes (j:I){S: Support (More N)}(F:I→Mark N)(h:∀ i,σ i=σ j → PostSupport false S (F i)): PostSupport false S (perturbJ Y i σ F R j):= totesCJ _ _ fun i v=> (h i (mem_filter.mp v).2).smulM _
include vP
lemma Listos.perturb (P':Listos Y i w X K (Y.uv k) A) : Listos Y i w X K (Y.uv k) (perturbJ Y i σ A R):=by
 refine ⟨fun i' => homes _ _ _ _ _ _ (fun i _=> P'.owns _),fun j p=>homes _ _ _ _ _ _ ?_⟩; intro j' u; have h:= (vP ..).mpr u; rw [←h]; exact P'.slit j' (h.symm ▸ p)
#print axioms permit_S
#print axioms Listos.perturb
#print axioms red_bill
end snowJ
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
