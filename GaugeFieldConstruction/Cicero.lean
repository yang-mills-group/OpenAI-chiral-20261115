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
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
variable (T: Sweep n)(P:BudgetPoint)(L:ℕ)(x:Scree.Hub n)
local notation "Ωv"=> boxA T
open SeasonH
-- bookkeeping singleton
variable (a b h c u:ℝ)(jB:ℕ)(i:I)(A':Torches n)
lemma scoop_κ {V G:Type}[AddCommMonoid G](V':List V)(f:V→G)(h:V→Bool)(v:∀i∈ V',h i=false→f i=0): Lee V' f= Lee (V'.filter h) f:=by
 induction V' with|nil=>rfl|cons i L ih=> have ht:= ih fun i t=> v i (List.mem_cons_of_mem _ t); rw [consA,List.filter_cons, ht]; split; exact (consA ..).symm; next g=> rw [v i List.mem_cons_self (by simpa using g),zero_add]
local notation "Sζ"=> jB
local notation "qP"=> Pach (σ i)
lemma hailed (U:Boke n I): entryS σ jB P U {i} x=Lee (Cull I i U) (fun e=>LexS σ e x jB P {i}):= by apply scoop_κ; intro e p h; apply Lex_blank; rw [Incζ_U]; simpa using h
lemma hail_B (U:Boke n I): entryW σ jB P U h {i} x= Lee (Cull I i U) (fun e=>Lex_B σ e x jB P {i} h):=by
 apply scoop_κ; intro e p h; rw [Lex_B,if_neg]; intro p; obtain ⟨q,u,-⟩:= (mem_filter.mp p).2; have hp:= (Incζ_U I σ e i).1 ⟨q.symm,u⟩; simpa [hp] using h -- tune
lemma off_S (U:Boke n I)(v:σ i ≠ x.val.1): entryS σ jB P U {i} x=0 ∧ entryW σ jB P U h {i} x=0:=by
 have hv(e): x∉ marksY σ e jB P {i}:=by intro p; apply v; symm; simpa using ((mem_filter.mp p).2).2.2.2
 induction U with
 | nil=>exact ⟨rfl,rfl⟩
 | cons i Q h=> unfold entryS entryW at *; rw [consA,consA,LexS,if_neg (hv i),Lex_B,if_neg (hv i),zero_add,zero_add]; exact h -- names i shadow
variable (l:List I)(υ:l.Nodup)(w:stampK M l)(H: Bouquet I i P b a h c A' σ (M i) u)(q:darkH F)(s:stabH F)(v':i∈l)
include H w q s v' υ
lemma ship_S (hN: 2*(ThermalH jB*P.B)<(More n).val)(hp:coverNumber P.B x.val.2≤jB): entryS σ jB P (Keeps F r M l) {i} x= if x= Zhub (σ i) then AlphaY A'.1 else 0:=by
 rw [sum_stamp]; simp only [card_singleton,↓reduceIte];
 have he(S0:Hubber n): QuotaΥ I σ {i} S0 jB P false x=0:=by
    unfold QuotaΥ; rw [if_neg]; intro p; have hx:= (mem_filter.mp p).2.1; simp only [padS,card_singleton,Bool.false_eq_true,↓reduceIte,image_singleton,singleton_biUnion] at hx; rw [hx] at hp; exact (Nat.not_succ_le_self _ ((lt_of_lt_of_le (ThickP jB P (σ i) hN) (Corona.cover_mono subset_union_right _)).trans_le hp)) -- tune
 have hT(S0:Hubber n):cacheS I σ {i} S0 (foli (Keeps F r M l))= if qP=S0 then AlphaY A'.1 else 0:= (Ink_sageY I σ M F r S0 i s q l υ w v').trans (bonO I σ S0 M P b a h c u (fun _=> A') i H) -- order
 simp_rw [he,hT,zero_smul,add_zero,smul_ite, smul_zero]; rw [Finset.sum_ite_eq, if_pos (mem_univ _)]
 have hy: MarksΥ I σ {i} qP jB P true={Zhub (σ i)}:=by
    ext i'; rw [mem_singleton]; unfold MarksΥ; simp only [padS,image_singleton,↓reduceIte,mem_filter,mem_univ,true_and,mem_singleton]; constructor; · intro p; exact Subtype.ext (Prod.ext p.2 p.1)
    intro p; rw [p]; exact ⟨rfl,rfl⟩
 unfold QuotaΥ; rw [hy]; by_cases p:x=Zhub (σ i); rw [if_pos (mem_singleton.mpr p),if_pos p,exp_Plate,card_singleton,Nat.cast_one,inv_one,one_smul]; rw [if_neg (mt mem_singleton.mp p),zero_smul,if_neg p]
omit H w q s v' υ
lemma lex_row (e: Vulcan I n)(p:Linca P σ e)(q:e.keys=[i]): let X: Scree.Hub n := ⟨(σ i,SpacePad jB P σ e),subset_union_left (p.stamp.port i (by rw [q]; simp))⟩; marksY σ e jB P {i}={X}:=by
 intro X; ext x; unfold marksY; rw [mem_singleton,mem_filter]; simp only [mem_univ,true_and,q,image_singleton,ψS,List.map_cons,List.map_nil,List.nodup_cons,List.nodup_nil,List.toFinset_cons,List.toFinset_nil, List.not_mem_nil,mem_singleton,insert_empty_eq,reduceCtorEq,not_false_eq_true,true_and,and_true]; constructor
 · intro p; exact Subtype.ext (Prod.ext p.2 p.1)
 intro p; rw [p]; exact ⟨rfl,rfl⟩
#print axioms ship_S
end MintB
end MastTin
end YM.CF.XGarden
end
