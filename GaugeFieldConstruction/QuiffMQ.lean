import GaugeFieldConstruction.PhonicsQ
import GaugeFieldConstruction.Barrera4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
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
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n:Side}
variable (e:I↪J)(σ:I→Seat n)(σ':J→Seat n)
open Same4
local notation "Δ"=> PaintEV e
variable (F:XE I (InkD n) n)(K:KK I (Copy n) n) (F':XE J (InkD n) n)(K':KK J (Copy n) n)
variable (S:List I)
local notation "S'"=> List.map e S
variable (l m:ℕ)(a:l=m)(p:Hub n)
lemma news_Cue (A:Finset I): (List.map e (Cue I A)).Perm (Cue J (A.image e)):=by
 apply List.perm_of_nodup_nodup_toFinset_eq ((Finset.sort_nodup ..).map e.injective) (Finset.sort_nodup ..); ext; simp only [List.mem_toFinset, List.mem_map, mem_image,Mew.Cue,Finset.mem_sort]
-- rota counts
abbrev TubeMQ (T:KI I n):=PaintEV e T
lemma rotaRQ (A:Finset (KI I n)): let C:=FrameT F K; let C':=FrameT F' K'; (List.map e (rosterF A C.B)).Perm (rosterF (A.image (PaintEV e)) C'.B):=by
 intro C C'; let W:= PaintEV (T:=Force n) e; let T:= A.image W; have p':List.Perm (A.toList.map W) T.toList:=by
    apply List.perm_of_nodup_nodup_toFinset_eq ((nodup_toList _).map (ev_inj e _)) (nodup_toList _); ext i; simp only[List.mem_toFinset,List.mem_map,Finset.mem_toList,T,W,mem_image]
 unfold rosterF; let L:= A.toList; apply List.Perm.trans (l₂:=((A.toList.map W).map C'.B).flatten) ?_ (p'.map _|>.flatten) -- syntax
 change (List.map e (L.map C.B).flatten).Perm ((L.map W).map C'.B).flatten; generalize L=L
 induction L with
 | nil=> exact List.Perm.refl _
 | cons i L ih=> simp only[List.map_cons,List.flatten_cons,List.map_append]; exact (news_Cue e i.1).append ih
lemma caboDQ (A:List I)(V:List J)(u:(A.map e).Perm V) : ditch A S=[] ↔ ditch V (S.map e)=[]:=by
 have h(x):e x∈ S'↔ x∈ S:= by rw[List.mem_map]; exact ⟨fun ⟨_,t,b⟩=>e.injective b▸t,fun g=>⟨x,g,rfl⟩⟩
 constructor
 · intro t; by_contra p; obtain ⟨y,u'⟩:= List.exists_mem_of_ne_nil _ p -- tune theorem
   obtain ⟨v,w⟩:=List.mem_filter.mp (show y∈ditch V S' from u'); obtain ⟨i,v',rfl⟩:=List.mem_map.mp (u.mem_iff.mpr v); have z:i∈ ditch A S:=List.mem_filter.mpr ⟨v', decide_eq_true (fun g=> (show e i∉ S' from of_decide_eq_true w) ((h i).2 g))⟩; rw [t] at z; exact List.not_mem_nil z -- tune
 intro p; by_contra t; obtain ⟨j,v⟩:= List.exists_mem_of_ne_nil _ t; obtain ⟨x,y⟩:=List.mem_filter.mp (show j∈ditch A S from v); have z:e j∈ ditch V (S.map e):=List.mem_filter.mpr ⟨u.mem_iff.mp (List.mem_map_of_mem x),decide_eq_true (fun g=> (show j∉S from of_decide_eq_true y) ((h j).1 g))⟩; rw [p] at z; exact List.not_mem_nil z
local notation "ΡΙ"=> FrameT F K
local notation "ΡΘ"=> FrameT F' K'
lemma archFQ (A:Finset (KI I n)): (FrameT F K).tressV S A=[] ↔ (FrameT F' K').tressV (S.map e) (A.image (PaintEV e))=[] := caboDQ e S _ _ (rotaRQ e F K F' K' A)
lemma archPQ (W: Heart p (Dusk I n) l): rosterF univ (fun i:Fin l=> (FrameT F K).purseV S (W.val i))=[] ↔ rosterF univ (fun j:Fin m=> (FrameT F' K').purseV (S.map e) ((iκQ e l m p a W).val j))=[]:=by
 subst m; have h(i:Fin l):(ΡΙ).purseV S (W.val i)=[] ↔ (ΡΘ).purseV S' (Δ (W.val i))=[]:= caboDQ e S _ _ (news_Cue e (W.val i).1)
 let A i:=(ΡΙ).purseV S (W.val i); let B i:=(ΡΘ).purseV S' (Δ (W.val i))
 change rosterF univ A=[]↔ rosterF univ B=[]; -- use universal proof roster empty
 have v {d β:Type}[Fintype d][Fintype β][LinearOrder β](A:d→List β): rosterF univ A=[]↔ ∀ i,A i=[]:=by
    constructor
    · intro t i; by_contra p; obtain ⟨j,v⟩:=List.exists_mem_of_ne_nil _ p; exact List.not_mem_nil (show j∈([]:List β) from t ▸ (show j∈rosterF univ A from (roster_mem ..).2 ⟨i,mem_univ _,v⟩)) -- Lean elaborator
    intro t; by_contra p; obtain ⟨j,x⟩:= List.exists_mem_of_ne_nil _ p; obtain ⟨i,u,k⟩:= (roster_mem ..).1 x; rw[t] at k; simp at k
 rw[v A,v B]; exact forall_congr' h
lemma puff_Q (x:I)(p:List I): (p.map e).count (e x)=p.count x:=by
 induction p with
 | nil=>rfl
 | cons i p ih=> rw[List.map_cons,List.count_cons,List.count_cons,ih]; by_cases h:i=x<;>simp only [h,EmbeddingLike.apply_eq_iff_eq,beq_iff_eq,true_and] -- tune
lemma know_Q (t:List I)(v:List J)(q:List I)(g:(t.map e).Perm v): knowR t S q↔knowR v (S.map e) (q.map e):=by
 constructor
 · intro h i j; obtain ⟨i,p,rfl⟩:=List.mem_map.mp j; rw[←g.count_eq,puff_Q,puff_Q]; exact h _ p
 intro h i u; rw [←puff_Q e i t,g.count_eq,h _ (List.mem_map.mpr ⟨_,u,rfl⟩),puff_Q]
-- emptiness for out charges. use to eliminate unscoped entries!
lemma rangeRQ {W: Heart p (Dusk I n) l}(h: rosterF univ (fun i:Fin l=> (FrameT F K).purseV S (W.val i))=[])(i:Fin l): (W.val i).1⊆ S.toFinset:=by
 intro j u; by_contra v; have he:j∈ rosterF univ (fun i:Fin l=> (FrameT F K).purseV S (W.val i)):= (roster_mem ..).2 ⟨i,mem_univ _,List.mem_filter.mpr ⟨(mem_sort ..).mpr u,decide_eq_true (fun p=> v (List.mem_toFinset.mpr p))⟩⟩; rw [h] at he; simp at he -- decidable tune
lemma rangeKQ {W:Finset (KI I n)} (h:(FrameT F K).tressV S W=[])(i:KI I n)(w:i∈W): i.1⊆ S.toFinset:=by
 intro j u; by_contra v; have he:j∈(FrameT F K).tressV S W:=List.mem_filter.mpr ⟨(roster_mem ..).2 ⟨_,w,(mem_sort ..).mpr u⟩,decide_eq_true (fun p=>v (List.mem_toFinset.mpr p))⟩; rw[h] at he; simp at he
#print axioms rotaRQ
#print axioms archPQ
end Iona
end YM.CF.Scree.Ing
end
