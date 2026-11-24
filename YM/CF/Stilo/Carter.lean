import YM.CF.Stilo.Sight
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {A B:Type*} {w:Bout A}[Ring B]
lemma picks_mem {L:List A}(h:w ∈ picks L): w.back.length+1=L.length := by -- tune
 induction L generalizing w with
 | nil=> simp [picks] at h
 | cons i l ih=> rw [picks,List.mem_cons] at h; rcases h with rfl|h; rfl; obtain ⟨g,p,rfl⟩:= List.mem_map.mp h; change (_::_).length+1=(i::l).length; have hy:=ih p; simp only [List.length_cons]; omega
-- recursion (l.head)}
def ticketB (L: A→B)(G: A→A→B): ℕ→ List A → B
 | 0, _=>1
 | _+1, []=> 1
 | n+1,i::g=> L i *ticketB L G n g + ((picks g).map (fun x=> (if x.neg then -(G i x.front) else G i x.front)*ticketB L G n x.back)).sum
def taskC (L:A→B)(G:A→A→B)(j:List A):B:= ticketB L G j.length j
private lemma becalm (L:A→B)(G:A→A→B)(i:ℕ)(j:List A)(n:ℕ)(v:j.length ≤ i)(he:j.length≤n):ticketB L G i j=ticketB L G n j:=by
 induction i generalizing n j with
 | zero=> rw [show j=[] from List.eq_nil_of_length_eq_zero (by omega)]; cases n <;> rfl
 | succ i ih=> cases j with
             | nil=> cases n <;> rfl
             | cons x l=> simp only [List.length_cons] at v he; cases n; omega; rename_i m; rw [ticketB,ticketB,ih l m (by omega) (by omega)]; congr 2; apply List.map_congr_left; intro y t; congr 1; apply ih _ _ <;>have h:= picks_mem t <;>omega
lemma book_budget (L:A→B)(G:A→A→B)(j:List A)(n:ℕ)(v:j.length≤n):ticketB L G n j=taskC L G j:= becalm L G n j _ v le_rfl
lemma task_zero (L:A→B)(G:A→A→B):taskC L G []=1:=rfl
lemma task_one (L:A→B)(G:A→A→B)(i:A)(j:List A):taskC L G (i::j)= L i*taskC L G j+ ((picks j).map fun x=>(if x.neg then -(G i x.front) else G i x.front)*taskC L G x.back).sum:=by
 unfold taskC; rw [List.length_cons,ticketB]; congr 2; apply List.map_congr_left; intro a p; have he:= picks_mem p; rw [book_budget L G a.back j.length (by omega)]; rfl
-- view-incidence copy
variable {E:Type*}[SemilatticeSup E][OrderBot E][Fintype E][DecidableEq E]
def timetable (L:A→ Track E B)(G:A→A→Track E B):ℕ→List A→Track E B
 | 0,_=>ownH B E
 | _+1,[]=>ownH B E
 | n+1,i::l=> crank (L i) (timetable L G n l) + ((picks l).map fun x=>crank (if x.neg then -(G i x.front) else G i x.front) (timetable L G n x.back)).sum
abbrev spanned(L:A→Track E B)(G:A→A→Track E B)(j:List A):= timetable L G j.length j
lemma time_v(L:A→Track E B)(G:A→A→Track E B)(n:ℕ)(j:List A)(e:E): view e (timetable L G n j)=ticketB (fun i=>view e (L i)) (fun i k=> view e (G i k)) n j:=by
 induction n generalizing j with
 | zero=> exact view_one _
 | succ n ih=> cases j with
            | nil=> exact view_one _
            | cons i g=> rw [timetable,ticketB,view_add,view_crank, ih,map_List,List.map_map]; congr 2; apply List.map_congr_left; intro k p; rw [Function.comp_apply,view_crank, ih]; congr 1; split_ifs; exact map_neg (vAdd _) _; rfl
lemma spans(L:A→Track E B)(G:A→A→Track E B)(j:List A)(e:E):view e (spanned L G j)=taskC (fun i=>view e (L i)) (fun i k=>view e (G i k)) j:= time_v ..
lemma time_eq(L:A→Track E B)(G:A→A→Track E B)(n:ℕ)(j:List A)(p:j.length≤n): timetable L G n j=spanned L G j:=funext fun t=> proves fun i _=>by rw [time_v,spans]; exact book_budget _ _ j n p
lemma spanned_cons(L:A→Track E B)(G:A→A→Track E B)(j:List A)(i:A):spanned L G (i::j)=crank (L i) (spanned L G j)+ ((picks j).map fun x=>crank (if x.neg then -(G i x.front) else G i x.front) (spanned L G x.back)).sum:=by
 unfold spanned; rw [List.length_cons,timetable]; congr 2; apply List.map_congr_left; intro x p; have he:= picks_mem p; rw [time_eq L G j.length x.back (by omega)]
end YM.CF.Stilo
