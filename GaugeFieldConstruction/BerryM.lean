import GaugeFieldConstruction.Gourmet
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
variable (T:Torches n)(ι:I→Seat n)
variable (U: Boke n I)
structure Bouquet (z:ℝ):Prop where
 headM:∃ H: Boke n I,∃ X:Hubber n→ Boke n I, Portrait I i (Pach (ι i)) P b a h c true ι T.1 H ∧ (∃ V: Hubber n→ℝ,(∀ i',0 ≤ V i'∧ Portrait I i i' P b a h (V i') false ι (T.2 i') (X i'))∧ (∑ i',Branch.rent a i'* V i') ≤ z)∧ U= H++ (Finset.univ (α:=Hubber n)).toList.flatMap X
#print Bouquet
-- support Pach $
lemma composeL (x:ℝ)(v: Inscribe P (ι i) h a T c x)(t:0≤b): ∃ Q:Boke n I, Bouquet I i P b a h c T ι Q x:=by
 obtain ⟨H,f⟩:= born_R I i _ _ P b a h c true ι v.1 (by intro; exact ⟨halo_subset _ _ (mem_singleton_self _),crown_H (Branch.Grove.single _) 24⟩) t
 obtain ⟨V,H',l⟩:= v.2; have hp(X):∃ Q,Portrait I i X P b a h (V X) false ι (T.2 X) Q:= born_R I i X (T.2 X) P b a h _ false ι (H' X).1 (fun h=>Classical.byContradiction (fun t=>h ((H' X).2 t))) t
 choose Z g using hp; exact ⟨_,⟨H,Z,f,⟨V,fun i=>⟨track_pos (H' i).1, g _⟩,l⟩,rfl⟩⟩
#print axioms composeL
variable {C':ℝ}(p:Bouquet I i P b a h c T ι U C')
local notation "Qx"=>Pach (ι i)
include p
lemma Bloom_up : (∀ v∈U,v.keys=[i]) ∧ CostP ι P U :=by
 obtain ⟨H,S,q,⟨c,v,t⟩,p⟩:=p.headM; subst U; refine ⟨fun j t=>?_,fun e t=>?_⟩
 · rcases List.mem_append.mp t with k|k; exact (q.etched j k).1; obtain ⟨x,-,h⟩:= List.mem_flatMap.mp k; exact ((v x).2.etched _ h).1
 rcases List.mem_append.mp t with k|k; exact q.heat _ k; obtain ⟨x,-,h⟩:=List.mem_flatMap.mp k; exact (v x).2.heat _ h
omit p
def harpZ : ChartP n →ₗ[ℂ] PairLog (FinV n) :=
   { toFun:= harpQ
     map_add':=by intro x y; simp [harpQ,add_smul,sum_add_distrib]
     map_smul':=by intro z x; simp [harpQ,smul_sum,mul_smul] }
lemma harp_A(v:ℂ)(A:Paper n)(x:Pane n):harpZ (αLines (v • A) x)= v • harpZ (αLines A x):=map_smul harpZ v (αLines A x)
lemma chart_c (S:Finset (Hubber n))(g:Hubber n→Paper n):αLines (∑ i∈S,g i) A=∑ i∈ S,αLines (g i) A:=funext fun x=>by unfold αLines; simp_rw [Finset.sum_apply] -- tune
lemma harm_p {V:Type}(S:List V)(p: V→Bool)(v:∀ i∈S,p i=false): List.filter p S=[]:= List.filter_eq_nil_iff.mpr fun i t=>by rw [v i t]; simp -- tune
include p
lemma Bloom_M :cryY V (1:Key I) A U= harpZ (Benck (ι i) T A V):=by
 obtain ⟨H,S,q,⟨c,v,t⟩,p⟩:=p.headM; subst U; unfold cryY; rw [appA,joinA]; change cryY V (1:Key I) A H+Lee (Finset.univ (α:=Hubber n)).toList (fun i=>cryY V (1:Key I) A (S i))= _; rw [show Lee _ _= ∑ i:Hubber n,cryY V (1:Key I) A (S i) from leafage .. ] -- tune name
 -- marine memo
 let z:=αLines (useS T.1 Qx V) A; let G(i:Hubber n):= harpZ (αLines (useS (T.2 i) i V) A)
 rw [q.blankF]; unfold Benck mintP; let V'(i:Hubber n):=αLines (useS (T.2 i) i V) A; rw [show αLines (useS T.1 (Pach (ι i)) V + ∑ i:Hubber n,useS (T.2 i) i V) A=z + αLines (∑ i:Hubber n,useS (T.2 i) i V) A from rfl,chart_c, map_add, map_sum]; exact congrArg (harpZ z+·) (sum_congr rfl fun i _=> (v i|>.2.blankF V A))
lemma Bloom_s(t:0≤b): fumeE I (foli U) h a b ≤ b*Branch.rent a Qx*c ∧ fumeE I (Slag I U) h a b ≤ b*C'∧ (∀ x∈foli U,x.seat=Qx)∧ Lee (foli U) PinInk=AlphaY T.1:=by
 obtain ⟨H,S,q,⟨c,v,T₀⟩,p⟩:=p.headM; subst U; let Q:=(Finset.univ (α:=Hubber n)).toList.flatMap S; have hp(X)(p:X∈Q):X.pure=false:=by obtain ⟨i,t,h⟩:=List.mem_flatMap.mp p; exact ((v i).2.etched _ h).2.2
 rw [show foli (H++Q)= H from ?_,show Slag I (H++Q)=Q from ?_]
 exact ⟨q.fairL, by
    unfold fumeE Q; rw [joinA, Lee, leafage]; apply le_trans _ (mul_le_mul_of_nonneg_left T₀ t); rw [mul_sum]; exact sum_le_sum fun i w=>(v i|>.2.fairL).trans_eq (mul_assoc ..),fun i u=>(q.etched _ u).2.1,q.ideal⟩
 swap
 · unfold foli; rw [List.filter_append,harm_p Q _ hp,List.filter_eq_self.mpr (fun i u=>(q.etched i u).2.2), List.append_nil]
 unfold Slag; rw [List.filter_append,harm_p H _ (fun i t=>by simp [(q.etched i t).2.2]),List.filter_eq_self.mpr (fun i u=>by simp [hp i u]),List.nil_append]
#print axioms Bloom_s
end MintB
end MastTin
end YM.CF.XGarden
end
