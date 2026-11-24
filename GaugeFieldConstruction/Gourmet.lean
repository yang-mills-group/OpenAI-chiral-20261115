import GaugeFieldConstruction.Muek
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
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
variable (i:I)
namespace MintB
open Wosk
variable (i:I)(S:Hubber n)(F:Paper n)(P:BudgetPoint)(b a h c:ℝ)(d:Bool)
def veilD (j:Wa n): RankU n:=j.map fun (t,i,y)=> ((t,i),(!t,y))
def harpQ (X:ChartP n): PairLog (FinV n):=∑ i:Wa n,X i • Pi.single (veilD i) 1
def useS (p:Paper n)(V:Support (More n))(d:Finset (Seat n)): Paper n:= if V⊆ d then p else 0
abbrev mintP (v:Torches n)(o:Seat n)(Q:Support (More n)):Paper n:= useS v.1 (Pach o) Q + ∑ i:Hubber n,useS (v.2 i) i Q
variable (o:Seat n)
abbrev Benck (v:Torches n)(A:Pane n)(V:Hubber n):= αLines (mintP v o V) A
def mug (S:Hubber n)(i:I)(F:Paper n)(H:Wa n→ℝ)(k:Bool)(x:Wa n):Vulcan I n:=⟨S,[i],veilD x,F x,H x,k⟩
-- explicit stencil leg reader
abbrev fumeE (Q:Boke n I)(h a b:ℝ):= Lee Q (wageL a b h)
def Slag(Q:Boke n I):= Q.filter fun i=> !i.pure
-- optional null purge; supports widths.
variable (ι:I→Seat n) (T:Torches n)
structure Portrait (A:Paper n)(Q:Boke n I):Prop where
 etched :∀ e∈Q,e.keys=[i]∧ e.seat=S ∧e.pure=d
 heat:CostP ι P Q
 blankF :∀ x:Hubber n,∀ y: Pane n,cryY x (1:Key I) y Q= harpQ (αLines (useS A S x) y)
 ideal : Lee Q PinInk= AlphaY A
 fairL : fumeE I Q h a b ≤ b*Branch.rent a S*c
 emptyQ: A=0 → Q=[]
#print Portrait
lemma haloΦ (Y:Paper n)(d:Finset (Seat n))(X:Pane n): harpQ (αLines (useS Y S d) X)=(if S⊆d then harpQ (αLines Y X) else 0):=by
 unfold useS; split; exact rfl; simp [harpQ,αLines]
lemma born_R (U:TrackD P S h F c)(v: F≠0→ Dock (ι i) S)(t:0≤b): ∃ Q:Boke n I, Portrait I i S P b a h c d ι F Q:=by
 by_cases p:F=0
 · subst F; refine ⟨[],fun i t=>by simp at t,fun i t=>by simp at t,fun i y=>by rw [haloΦ]; split <;>simp [cryY,Lee,harpQ,αLines],AlphaØ.symm,le_trans (show fumeE I [] h a b≤(0:ℝ) from Eq.le rfl) (mul_nonneg (mul_nonneg t (Real.exp_pos _).le) (track_pos U)), fun _=>rfl⟩
 let L:= v p; obtain ⟨H,u,w⟩:=U
 let Z:= univ.filter (fun i:Wa n=>DomainP S i)
 let Q:= Z.toList.map (mug I S i F H d)
 refine ⟨Q,fun e u=> ?_,fun e v=>?_,fun x V=>?_,?_,?_, (fun v=> False.elim (p v))⟩
 · obtain ⟨y,t,rfl⟩:=List.mem_map.mp u; exact ⟨rfl,rfl,rfl⟩
 · obtain ⟨y,t,rfl⟩:=List.mem_map.mp v; let Y:=mug I S i F H d y; let T:= (mem_filter.mp (Finset.mem_toList.mp t)).2; refine ⟨⟨(u y).1,fun i t=>List.mem_singleton.mp t ▸ L.1⟩,?_ ,L.2⟩; unfold puffQ; intro i j e; change veilD y=_ at e; rcases y with _|⟨k,i',j'⟩; contradiction; unfold veilD at e; obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj e); exact T
 · unfold cryY Q; rw [mapA,Lee,leafage]; rw [haloΦ]; split
   next t =>
      have hx(y:Wa n):egest (mug I S i F H d y) x 1 V=F y V:=by unfold mug egest; simp [t,GJ.stalk] -- tune
      simp_rw [hx]; refine (Finset.sum_subset (f:=fun y=>F y V • (Pi.single (veilD y) 1:PairLog _)) (subset_univ Z) fun j _ v=>?_)
      rw [(u j).2 (fun t=>v (mem_filter.mpr ⟨mem_univ _,t⟩))]; simp
   next s => apply Finset.sum_eq_zero; intro t _; simp [egest,mug,s]
 · funext x; unfold AlphaY Q; rw [mapA,Lee,leafage,Finset.sum_apply]
   have hy (y:Wa n): PinInk (mug I S i F H d y) x= F y x • civic_K y:=by rcases y with _|y; rfl; obtain ⟨k,i,j⟩:=y; rfl
   simp_rw [hy]; refine Finset.sum_subset (f:=fun j=>F j x • civic_K j) (subset_univ Z) fun i _ p=>?_ -- maybe defeq motive lambda requires case j
   rw [(u i).2 (fun h=>p (mem_filter.mpr ⟨mem_univ _,h⟩))]; simp
 unfold fumeE Q; rw [mapA,Lee,leafage]; apply le_trans _ (mul_le_mul_of_nonneg_left w (mul_nonneg t (Real.exp_pos _).le)); have hx:(∑ i∈ Z,papW n h i* H i) ≤ ∑ i,papW n h i*H i:= Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> mul_nonneg (papW_v _) (u i|>.1.1)
 apply le_trans _ (mul_le_mul_of_nonneg_left hx (mul_nonneg t (Real.exp_pos _).le)); rw [Finset.mul_sum]; refine le_of_eq (Finset.sum_congr rfl fun j k=>?_); unfold wageL weightV; simp only [mug, List.length_singleton,pow_one]; let H:=mug I S i F H d j; have hv:Lite h H.val=papW n h j:=by rcases j with _|j <;> rfl
 change Lite h H.val*_=_; rw [hv]; ring
end MintB
end MastTin
end YM.CF.XGarden
end
