import YM.CF.Stilo.Drum
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {ι I J A E n:Type*}[LinearOrder n][Fintype n]
open Scree Pastry
variable [Fintype E][OrderBotAux : SemilatticeSup E][OrderBot E][DecidableEq E]
section pay
variable {a b:Track E ℝ}
lemma crank_plus(A B C:Track E ℝ):crank (A+B) C=crank A C+crank B C:=funext fun i=> proves fun j _=> by rw [view_crank,view_add,view_add,view_crank,view_crank,add_mul]
lemma crank_list (X:Track E ℝ)(F:List (Track E ℝ)): crank F.sum X=(F.map fun i=>crank i X).sum:=by
 induction F with
 | nil=> change crank 0 X=0; exact funext fun i=> proves fun j _=>by rw [view_crank,view_zero,zero_mul]
 | cons i l h=> simp only [List.sum_cons,List.map_cons,crank_plus,h]
lemma crank_C (X F:Track E ℝ):crank F X=crank X F:=funext fun i=> proves fun j _=>by rw [view_crank,view_crank,mul_comm]
lemma crank_s(F G:Track E ℝ)(p:0 ≤ F)(q:0 ≤ G) : 0≤ crank F G:=by
 intro j; unfold crank coal; simp only [Finset.sum_apply]; refine sum_nonneg fun i _=> sum_nonneg fun k _=> ?_; rw [Pi.single_apply]; split_ifs; exact mul_nonneg (p _) (q _); exact le_rfl
lemma crank_mono(F X Y:Track E ℝ)(p:0≤F)(h:X ≤ Y): crank F X≤crank F Y:=by
 intro j; unfold crank coal; simp only [Finset.sum_apply]; refine sum_le_sum fun i _=>sum_le_sum fun k _=>?_ ; simp_rw [Pi.single_apply]; split_ifs; exact mul_le_mul_of_nonneg_left (h k) (p i); exact le_rfl
lemma crank_r(F X Y:Track E ℝ)(p:0 ≤ F)(h:X ≤ Y):crank X F ≤ crank Y F:=by rw [crank_C F,crank_C F Y]; exact crank_mono F X Y p h
abbrev payH (F:ι→Track E ℝ)(B:List ι):Track E ℝ:=List.foldr (fun i y=> crank (F i) y) (ownH ℝ E) B
lemma coinH : 0 ≤ ownH ℝ E:=fun _=>by unfold ownH; rw [Pi.single_apply]; split_ifs <;> exact_mod_cast (by norm_num)
lemma pay_S {F:ι→Track E ℝ}{B:List ι}(p:∀ i,0 ≤ F i): 0 ≤ payH F B:=by induction B with | nil=> exact coinH | cons i l ih=> exact crank_s _ _ (p i) ih
lemma order_pay(P:ι→ Track E ℝ)(L:List ι){x:Bout ι}(p:x∈ picks L) : payH P L= crank (P x.front) (payH P x.back):=by
 induction L generalizing x with
 | nil=> simp [picks] at p
 | cons i L ih=>
    rw [picks,List.mem_cons] at p; rcases p with rfl|p; · rfl
    obtain ⟨x,hb,rfl⟩:=List.mem_map.mp p; change crank (P i) (payH P L)= crank (P x.front) (crank (P i) (payH P x.back)); rw [ih hb, ←crank_A, crank_C (P x.front), crank_A]
lemma settle [DecidableEq ι] (L: List ι)(h:L.Nodup): ((picks L).map Bout.front).Nodup :=by
 suffices ((picks L).map Bout.front)= L from this.symm ▸ h
 clear h; induction L with
 | nil=>rfl
 | cons i l ih=> rw [picks,List.map_cons,List.map_map,show Bout.front ∘ beside i= Bout.front from rfl,ih]
-- bank positivity. x can carry any derivative bill ring. use orientation cost-neutral.
lemma fuseT [Ring A] (norm:A→ℝ)(v:∀ x y,norm (x*y)≤norm x*norm y)(p:∀ x y,norm (x+y)≤norm x+norm y)(g:norm 0=0)(F G:Track E A):norm ∘ crank F G ≤ crank (norm ∘ F) (norm ∘ G):=by
 have ht (S:Finset E) (f:E→ A): norm (∑ i∈ S,f i)≤∑ i∈S,norm (f i):=by
    induction S using Finset.induction_on with
    | empty=> simp [g]
    | @insert a S hb ih=> rw [sum_insert hb,sum_insert hb]; exact (p ..).trans (add_le_add_right ih _)
 intro j; unfold crank coal; simp only [Function.comp_apply,Finset.sum_apply]; refine le_trans (ht _ _) (sum_le_sum fun i _=> (ht _ _).trans (sum_le_sum fun k _=> ?_)); simp_rw [Pi.single_apply]; split_ifs; exact v _ _; exact g.le
lemma list_fuse [Ring A](norm:A→ℝ)(p:∀ x y,norm (x+y)≤norm x+norm y)(g:norm 0=0)(F:List (Track E A)):norm ∘ F.sum ≤ (F.map (fun f=>norm ∘ f)).sum:=by
 induction F with
 | nil=> exact fun t=>g.le
 | cons i l ih=> rw [List.sum_cons,List.map_cons,List.sum_cons]; exact fun j=> (p (i j) (l.sum j)).trans (add_le_add_right (ih j) _)
lemma esteem {M:Type*}[AddCommMonoid M][PartialOrder M][IsOrderedAddMonoid M](X:List ι)(F G:ι→M)(p:∀ i∈X,F i≤G i):(X.map F).sum ≤ (X.map G).sum:=by
 induction X with
 | nil=> exact le_rfl
 | cons i g ih=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons]; exact add_le_add (p i (List.mem_cons_self ..)) (ih fun j u=>p j (List.mem_cons_of_mem i u))
lemma deed {M:Type*}[AddCommMonoid M][PartialOrder M][IsOrderedAddMonoid M][DecidableEq ι](X:List ι)(F:ι→ M)(p:X.Nodup): (X.map F).sum=∑ i∈X.toFinset,F i :=by
 induction X with
 | nil=>simp
 | cons i g ih=> rw [List.map_cons,List.sum_cons,List.toFinset_cons,sum_insert (by simpa using (List.nodup_cons.mp p).1),ih (List.nodup_cons.mp p).2]
lemma engage [Ring A](norm:A→ℝ)(v:∀ x y,norm (x*y)≤ norm x*norm y)(p:∀ x y,norm (x+y)≤norm x+norm y)(g:norm 0=0)(he:norm 1≤1)(hy:∀ x,norm (-x)=norm x)(hz:∀ x,0≤norm x)[DecidableEq ι][Fintype ι](L:ι→Track E A)(G:ι→ι→Track E A)(S:ι→Track E ℝ)(W:List ι)(k:W.Nodup)(q:∀ i, norm ∘ L i +∑ j:ι,norm ∘ G i j≤ S i)(ℓ:∀ i, ownH ℝ E ≤ S i): norm ∘ spanned L G W ≤payH S W:=by
 suffices he: ∀ b (W:List ι), W.length<b→ W.Nodup → norm ∘ spanned L G W ≤payH S W from he (W.length+1) W (by omega) k
 have hs(i):0 ≤S i:=coinH.trans (ℓ i); intro b; induction b with
 | zero=>intro _ _; omega
 | succ b ih=>
    intro l hl p'; cases l with
    | nil=>
       intro t; change norm ((Pi.single ⊥ (1:A):Track E A) t)≤(Pi.single ⊥ (1:ℝ):Track E ℝ) t; simp_rw [Pi.single_apply]; split_ifs; exact he; exact g.le
    | cons i l=>
       simp only [List.length_cons] at hl; have hw:=(List.nodup_cons.mp p').2; have hx(x:Bout ι)(hh:x ∈ picks l):x.back.Nodup :=by
         -- from sublist
         suffices h :∀ l: List ι,∀ x∈ picks l, x.back.Sublist l from (h l x hh).nodup hw
         intro y; induction y with
         | nil=> simp [picks]
         | cons i l ih=> intro x u; rw [picks,List.mem_cons] at u; rcases u with rfl|w; exact List.sublist_cons_self _ _; obtain ⟨z,p,rfl⟩:= List.mem_map.mp w; exact (ih z p).cons_cons _
       let P:= norm ∘ L i; let Y:= payH S l; have hp : 0≤P:=fun t=>hz _; have hY:0≤Y:=pay_S hs
       let K(j):Track E ℝ:= norm ∘ G i j; have hk(i):0≤K i:=fun t=>hz _
       let A'(x:Bout ι):= if x.neg then -(G i x.front) else G i x.front; let V(x:Bout ι):=crank (A' x) (spanned L G x.back); let D:=picks l
       have hg₀(x:Bout ι): norm ∘ A' x=K x.front:=by unfold A'; split_ifs; exact funext fun t=> hy _; rfl
       have hh₁: norm ∘ crank (L i) (spanned L G l) ≤ crank P Y:= (fuseT norm v p g _ _).trans (crank_mono _ _ _ hp (ih l (by omega) hw))
       have hh₂(x:Bout ι)(p':x∈D): norm ∘ V x ≤ crank (K x.front) Y:=by
          apply (fuseT norm v p g _ _).trans; rw [hg₀ x]; apply crank_mono _ _ _ (hk _); apply (ih _ (by have h:= picks_mem p'; omega) (hx x p')).trans
          exact le_trans (le_of_eq (crank_L ..).symm) (le_trans (crank_r _ _ _ (pay_S hs) (ℓ x.front)) (order_pay _ l p').symm.le)
       rw [spanned_cons]; -- sum
       let R:= ∑ j:ι,K j
       have hK: ((D.map Bout.front).map K).sum ≤ R:=by rw [deed _ _ (settle l hw)]; exact sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> hk i)
       have hh₃: norm ∘ (D.map V).sum ≤ crank R Y:=by
          apply (list_fuse norm p g (D.map V)).trans; rw [List.map_map]
          apply (esteem D _ (fun x=> crank (K x.front) Y) hh₂).trans; apply le_trans ?_ (crank_r _ _ _ hY hK); rw [crank_list,List.map_map,List.map_map]; exact le_rfl
       change norm ∘ (_ + (D.map V).sum) ≤crank (S i) Y
       apply le_trans (show _≤ (crank P Y + crank R Y) from fun j=> (p _ _).trans (add_le_add (hh₁ j) (hh₃ j))) -- tune
       rw [←crank_plus]; exact crank_r _ _ _ hY (q i)
end pay
end YM.CF.Stilo
