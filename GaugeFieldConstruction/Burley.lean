import GaugeFieldConstruction.Hoon
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
variable (I:Type)[LinearOrder I][Fintype I]
variable {e a d b c k u f E:ℝ}(F:Elm n Unit e a c)(R:Loom n)(k u:ℝ)(p:BudgetPoint)(m:ℕ)(b0:ℝ)(T:Ids n)
local notation "Y"=>Single n
local notation "B_"=>LoreM n I Unit
def LemKer (i j:Y)(S:Hubber n) :B_:=⟨Sect S m,[],(),kiosk S m u R T (fun x=> releaseQ F S x i j),DeskK b0 e*F.W S i j,false⟩
def eBook (i j: Y): Toil I (Seat n) (Pane n):= ((Finset.univ.filter fun S=>F.W S i j≠0).toList.map fun S=>LemKer I F R u m b0 T i j S)
local notation "eV"=>eBook I F R u m b0 T
def baseK (i:Y): B_:=⟨{Ekm n (true,i)},[],(),fun _=>(1:ℂ)/2,1,false⟩
def unitK (i j:Y):Toil I (Seat n) (Pane n):= if i=j then [baseK I i] else []
def street : Fork n I
 | (true,i), (false,j)=> unitK I i j ++ eV j i
 | (false,i),(true,j)=> unitK I i j ++ (eV i j).map merP
 | _, _=>[]
local notation "Kern"=> street I F R u m b0 T
variable (v:Roof n u k m R)(h:k<e)(hp:0<e)(v0:0≤ b0)(tK:coinH f b0)(z:hud_T 7 f)(t:1≤f)(w:p.threshold ≤ u)(s:p.order≤6)
include hp v h v0 tK
lemma LArmor0(i j:Y)(S:Hubber n): let e':=LemKer I F R u m b0 T i j S; (Baro f e 6 S (fun x=> releaseQ F S x i j) e'.won) ∧ (F.W S i j≠0→ Grove (terr _) e'.seat ∧ Ekm n (true,i)∈e'.seat∧ Ekm n (true,j)∈ e'.seat):=by
 intro e'; let Z:=toll_Baro F S tK hp v0 i j; have hu:=Z.1; refine ⟨⟨hu.1,hu.2.1,hu.2.2.1,fun V _ _ _ U x v t=> (hu.2.2.2 _ U x v t).order (by decide)⟩,fun t=>⟨?_ ,?_,?_⟩⟩
 · exact crown_H (Z.2 t).1 _
 · exact halo_subset _ _ (Z.2 t).2.1
 exact halo_subset _ _ (Z.2 t).2.2
include z t w s
lemma lemKer_g(i j:Y)(S:Hubber n): let x:=LemKer I F R u m b0 T i j S; Micro p x.seat x.amt x.won:= houseT v h T z t w s _ _ (LArmor0 I F R k u m b0 T v h hp v0 tK i j S).1 -- tune
lemma lem_phase(i j:Y):∀ e∈ eBook I F R u m b0 T i j, e.keys=[] ∧ e.pure=false ∧ Micro p e.seat e.amt e.won ∧Grove (terr _) e.seat ∧ Ekm n (true,i)∈e.seat∧ Ekm n (true,j)∈e.seat:=by
 intro e t₀; obtain ⟨x,y,rfl⟩:=List.mem_map.mp t₀; exact ⟨rfl,rfl,lemKer_g I F R k u p m b0 T v h hp v0 tK z t w s _ _ x,(LArmor0 I F R k u m b0 T v h hp v0 tK ..).2 ((mem_filter.mp (Finset.mem_toList.mp y)).2)⟩
omit v hp h s tK w v0 z t
lemma unit_fee(i:Y): let e:=baseK I i; Micro p e.seat e.amt e.won ∧ Grove (terr _) e.seat:=by
 refine ⟨⟨zero_le_one, Env.compact (by change Continuous (fun _=>_); exact continuous_const),fun _ _ _=>rfl,fun _ _=>allows_const _ (by change ‖(1:ℂ)/2‖≤1; norm_num)⟩, Grove.single _⟩ -- tune
lemma κunit_g(i j:Y):∀ e∈ unitK I i j,e.keys=[]∧ e.pure=false∧ Micro p e.seat e.amt e.won∧Grove (terr _) e.seat ∧ Ekm n (true,i) ∈e.seat ∧ Ekm n (true,j)∈e.seat:=by
 intro e h; unfold unitK at h; split at h
 next k=> subst j; rw [List.mem_singleton.mp h]; exact ⟨rfl,rfl,(unit_fee I p i).1,(unit_fee I p i).2, mem_singleton_self _,mem_singleton_self _⟩
 simp at h
include v h hp v0 tK z t w s
lemma Ker_Ω : Fort p Kern:=by
 have he(i j:FinV n): ∀ e∈ Kern i j,e.keys=[]∧e.pure=false∧Micro p e.seat e.amt e.won∧ Grove (terr _) e.seat∧ Ekm n i∈ e.seat∧ Ekm n j∈ e.seat:=by
    rintro e r; rcases i with ⟨b,i⟩; rcases j with ⟨p',j⟩; cases b <;> cases p'
    · simp [street] at r
    · obtain h1|h1:=List.mem_append.mp r; exact κunit_g I p _ _ e h1
      obtain ⟨y,q,rfl⟩:= List.mem_map.mp h1; obtain ⟨a,b,μ,o,M,J⟩:=lem_phase I F R k u p m b0 T v h hp v0 tK z t w s _ _ y q; have hx:= micro_ms μ (-1:ℂ); rw [norm_neg,norm_one,one_mul,neg_one_smul] at hx; exact ⟨a,b,hx,o,M,J⟩
    · obtain h1|h1:=List.mem_append.mp r; exact κunit_g I p _ _ e h1
      obtain ⟨a,b,μ,o,L,N⟩:= lem_phase I F R k u p m b0 T v h hp v0 tK z t w s _ _ e h1; exact ⟨a,b,μ,o,N,L⟩
    simp [street] at r
 exact ⟨fun i j e t=>(he i j e t).1,fun i j e t=>(he i j e t).2.1,fun i j e t=>(he i j e t).2.2⟩
#check YM.UVNext.PricedKernels.funnel
end MastTin
end YM.CF.XGarden
end
