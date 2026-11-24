import GaugeFieldConstruction.Gantr3
import GaugeFieldConstruction.Mizan
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner Ladder3 Branch Tenant XGarden.MastTin
variable (F:RegLime I α n)(Q:LeaseQ γ n)(k:I)(M:Mica I β n){J:Type}[Fintype J](C:J→Factor3 n)
section
variable (P:BudgetPoint)(L:ℕ)(S:Ids n)(σ:I→Seat n)
abbrev AgeQ (Q:LeaseQ γ n)(C:Factor3 n)(i:AV3 Q C):ℕ:= i.1.val.1
abbrev AgeP (Q:LeaseQ γ n)(C:Factor3 n)(i:AV3 Q C):ℕ:= i.1.val.2
-- Seth col recipe; shorter.Pulus
abbrev archν (A:Factor3 n)(Q:LeaseQ γ n)(i:AV3 Q A)(V:Support (More n)):= discount (AgeQ Q A i) (AgeP Q A i) • Coral (A.issue V) (fun j=> Q.issue j V) (List.ofFn i.2.val)
local notation "G"=> Actors Q C
local notation "φ"=> Platform Q C P L
local notation "ρ"=> Craft3 F Q k M C (Platform Q C P L) S
local notation "Z" i:max=> nucleQ Q C i
local notation "H" i:max=> spark3 Q C P L i
abbrev PoleQ (i:Actors Q C):InkD n:=fun u=>fair ((archν (C i.1) Q i.2.1 ∅) (u,S))
local notation "KJE" i:max=> PoleQ Q C S i
abbrev DayQ (i:Actors Q C):Prop:= AgeP Q (C i.1) i.2.1=0
def IIW : Finset (Actors Q C):= univ.filter (fun i=>DayQ Q C i ∧ i.2.2=false)
@[reducible] noncomputable def rateWide (h:Hub n)(S:α→ Support (More n))(d:ℕ)(p:d=0):Unique (Heart h S d):=by
 subst d; let f:Fin 0→α:=Fin.elim0
 exact ⟨⟨⟨f,mem_filter.mpr ⟨mem_univ _,fun j=>Fin.elim0 j⟩⟩⟩,fun _=> Subsingleton.elim (α:=↥(LeadQ h.val.2 S 0)) _ _⟩ -- `lemma cannot returns Type`
lemma Vinc (i:Actors Q C)(h:i∈ IIW Q C)(x:Heart ((H i)) F.S (AgeP Q (C i.1) i.2.1)): let A:= C i.1; let p:=i.2.1; let K:= symbols_in F Q A k (Platform Q C P L i.1) p; (K.from_ x)=[k]∧ (K.pureT M S).termR x=PoleQ Q C S i ∧ Legist (H i) F.S (AgeP Q (C i.1) i.2.1) x=H i:=by
 intro Vx u A; let d:= AgeP Q Vx u; have ht:d=0:= (mem_filter.mp h).2.1; letI:IsEmpty (Fin d):=by rw [ht]; infer_instance
 have hn{Y:Type} (f:Fin d→Y): List.ofFn f=[]:= List.eq_nil_of_length_eq_zero (List.length_ofFn.trans ht)
 refine ⟨?_,?_,?_⟩
 · change _ :: rosterF (univ:Finset (Fin d)) _ = _; rw [univ_eq_empty]; simp [rosterF]
 · funext w; let Y:= loomR F Vx Q (AgeQ Q Vx u) d u.2 (H i) x
   let f:= fun j=> stamps F Q ∅ j (w,S); change fair (discount _ _ • scar _ (Y.map f))= fair (discount _ _ • scar _ _)
   unfold Y; unfold loomR; rw[hn,List.nil_append,List.map_ofFn,List.map_ofFn]; rfl
 apply Subtype.ext; refine Prod.ext rfl ?_; change (H i).val.2∪ ((univ:Finset (Fin d)).biUnion _) = _; rw [univ_eq_empty,biUnion_empty,union_empty]
lemma burnV (i:Actors Q C): let T:= Craft3 F Q k M C (Platform Q C P L) S i; (if T.needs=0 then Rinc σ T else 0)= if i∈IIW Q C then clipK σ (spark3 Q C P L i) [k] (PoleQ Q C S i) else 0:=by
 intro V; let A:= C i.1; let x:=i.2.1; let d:= AgeP Q A x; let B:= symbols_in F Q (C i.1) k (Platform Q C P L i.1) x
 by_cases h:i.2.2=true
 · have hp:V=B.busyT M:=by unfold V Craft3 κhop; rw[if_pos h]
   rw [if_neg (fun (t:i∈IIW Q C)=> (_root_.Bool.false_ne_true (((mem_filter.mp t).2.2).symm.trans h))),hp]; split; swap; rfl -- tune eq vs le
   unfold Rinc; apply Finset.sum_eq_zero; intro i _; funext b; unfold clipK; split; rfl; rfl
 rw [show V=B.pureT M S from (by unfold V Craft3 κhop; rw[if_neg h])]
 by_cases p:i∈IIW Q C; swap; · rw[if_neg (fun (e:(B.pureT M S).needs=0)=>p (mem_filter.mpr ⟨mem_univ _,e,Bool.eq_false_iff.mpr h⟩)),if_neg p]
 rw [if_pos p,if_pos (show (B.pureT M S).needs=0 from (mem_filter.mp p).2.1)]; unfold Rinc; let W:= Heart (H i) F.S d; letI: Unique W:=rateWide (H i) F.S d (mem_filter.mp p).2.1
 change ∑ x:W,clipK σ (Legist (H i) F.S d x) (B.from_ x) ((B.pureT M S).termR x)= _; rw[Fintype.sum_unique]; obtain ⟨t,x,y⟩:= Vinc F Q k M C P L S i p (default:W); rw [t,y]; exact congrArg (fun v=> clipK σ _ [k] v) x -- tune dependent
lemma whiteBill : (purchase3 F Q k M C (Platform Q C P L) S σ).X=∑ i∈ IIW Q C,clipK σ (spark3 Q C P L i) [k] (PoleQ Q C S i):=by
 change (∑ i:Actors Q C with (ρ i).needs=0,(ρ i).Rinc σ)=_
 rw [sum_filter]; let z(i:Actors Q C):= clipK σ (spark3 Q C P L i) [k] (PoleQ Q C S i); have he:(∑ i:Actors Q C,(if i∈ IIW Q C then z i else 0))=∑ i∈ IIW Q C,z i:=by rw [←Finset.sum_filter, Finset.filter_mem_eq_inter,Finset.univ_inter] -- tune
 rw[←he]; exact sum_congr rfl fun i _=> burnV F Q k M C P L S σ i
#print axioms Vinc
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
