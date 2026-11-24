import YM.CF.Stilo.Hoth
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {A:Type*}[Fintype A][DecidableEq A]{ι n:Type*}[LinearOrder n][Fintype n][LinearOrder ι][Fintype ι]
open Pastry Scree
lemma move_t (K:ι→ι→ℂ)(L:ι→n→ℂ)(P M R Q : List ι)(h:∀ i∈ M,∀ j∈R,K i j+K j i=0):let W:=taskC (lank L) (price K n)
 W (P++M++R++Q)= (-1:ℂ)^(M.length*R.length) • W (P++R++M++Q):=by
 intro W; have he(p r t:List ι)(i:ι)(v:∀ j∈ r,K i j+K j i=0):W (p++i::(r++t))=(-1:ℂ)^r.length • W (p++r++i:: t):=by
    induction r generalizing p i with
    | nil=> simp
    | cons j l ih=>
        have hf:= resetC L K p (l++t) i j; dsimp only at hf; rw [v j (List.mem_cons_self ..),zero_smul] at hf
        have hv:= ih (p++[j]) i fun k hk=>v k (List.mem_cons_of_mem _ hk)
        rw [List.length_cons,pow_succ',mul_smul,← show (p++[j]++l++i::t)=p++(j::l)++(i::t) from ?_] -- tune rhs
        · rw [← hv,neg_one_smul,List.cons_append]; apply eq_neg_of_add_eq_zero_left; simp only [List.append_assoc,List.cons_append,List.nil_append]; exact hf
        simp [List.append_assoc]
 induction M generalizing P R Q with
 | nil=>simp
 | cons i X ih=>
    have ht:= ih (P++[i]) R Q fun x hx=> h x (List.mem_cons_of_mem _ hx)
    have hv:= he P R (X++Q) i (h i (List.mem_cons_self ..))
    simp only [List.append_assoc,List.cons_append,List.nil_append] at ht hv ⊢; rw [ht, hv, smul_smul]; simp [pow_add, add_mul]
lemma cross_v (L:ι→n→ℂ)(K:ι→ι→ℂ)(P M R Q:List ι)(h:Even M.length)(hh:∀ i∈ M,∀ j∈ R,K i j=0∧ K j i=0)
 (ht:∀ i∈ P++R,∀ j∈ M++Q,K i j=0):let W:= taskC (lank L) (price K n)
 W (P++M++R++Q)=W (P++R)*W (M++Q):=by
 dsimp only; rw [move_t K L P M R Q ?v, show (-1:ℂ)^(M.length*R.length)=1 from (h.mul_right ..).neg_one_pow,one_smul]
 rw [List.append_assoc (P++R)]; exact cuttable _ _ _ _ fun i p j g=>by rw [price,ht i p j g,zero_smul]
 intro i p j g; rw [(hh _ p _ g).1,(hh _ p _ g).2,zero_add]
abbrev shelf(n:Type*)[LinearOrder n][Fintype n](A:Type*):=Track (Harper A) (FC n)
abbrev boxU (U:Harper A)(T:shelf n A):shelf n A:= crank (Pi.single U 1) T
lemma boxV (U V:Harper A)(T:shelf n A):view V (boxU U T)= if U≤ V then view V T else 0:=by rw [boxU,view_crank,singleV]; split <;> simp
variable {H R P Q:Harper A}
section factor
variable (L:ι→ shelf n A)(K:ι→ι→shelf n A)(v: Harper A→ι→ n→ℂ)(f: Harper A→ι→ι→ℂ)(p:∀ i a,view a (L i)=lank (v a) i)(ht:∀ i j a,view a (K i j)=price (f a) n i j)
include p ht
abbrev reveal (P:Harper A)(X:List ι):shelf n A:= boxU P (spanned L K X) -- p ht not parameters (def)
lemma reH (X:List ι)(a:Harper A):view a (reveal L K P X)= if P ≤ a then taskC (lank (v a)) (price (f a) n) X else 0:=by simp only [reveal,boxV,spans,p,ht]
omit p ht
lemma isolated(X:List ι)(H R P:Harper A)(g:∀ i∈X,view H (L i)=view R (L i))(h:∀ i∈X,∀ j∈X,view H (K i j)=view R (K i j))(u:P ≤ H ↔ P ≤ R):view H (reveal L K P X)=view R (reveal L K P X):=by
 rw [reveal,boxV,boxV, u]; split; swap; · rfl
 rw [spans,spans]; unfold taskC;
 suffices T:∀ n Y,Y ⊆ X → ticketB (fun i=>view H (L i)) (fun i j=> view H (K i j)) n Y=ticketB (fun i=>view R (L i)) (fun i j=> view R (K i j)) n Y from T _ X (List.Subset.refl _) -- tune
 intro n Y hX; induction n generalizing Y with
 | zero=> rfl
 | succ n ih=> cases Y with
            | nil=>rfl
            | cons i Y=>
                have hx:=hX (List.mem_cons_self ..); have hy:Y⊆X:= fun k t=>hX (List.mem_cons_of_mem i t); rw [ticketB,ticketB,g i hx,ih _ hy]; congr 2; apply List.map_congr_left; intro j p; obtain ⟨l,v⟩:=pick_wear Y p; rw [h i hx _ (hy l), ih _ (List.Subset.trans v hy)]
include p ht
lemma parts(B M T U:List ι)(e:Even M.length) (hP:P ≤ H)(hR: Q ≤ R)(hH:Disjoint (bay H) (bay R))(w:∀ J:Harper A,J ≤ H⊔R→ P⊔Q ≤ J →
 (∀ i∈ M,∀ j∈ T,f J i j=0 ∧ f J j i=0)∧(∀ i∈ B++T,∀ j∈ M++U,f J i j=0)∧ view J (reveal L K P (B++T))=view (J⊓H) (reveal L K P (B++T))∧ view J (reveal L K Q (M++U))=view (J⊓R) (reveal L K Q (M++U))) : reveal L K (P⊔Q) (B++ M++T++U) (H⊔R)= reveal L K P (B++T) H * reveal L K Q (M++U) R:=by
 apply localizes hH; intro J g; by_cases l:P⊔Q≤J
 · obtain ⟨hv,hf,h₁,h₂⟩:=w J g l; rw [←h₁,←h₂,reH L K v f p ht _ _,reH L K v f p ht _ _,reH L K v f p ht _ _,if_pos l,if_pos (le_sup_left.trans l),if_pos (le_sup_right.trans l)]; exact cross_v (v J) (f J) B M T U e hv hf
 rw [reveal,boxV,if_neg l,reveal,boxV,reveal,boxV]; by_cases k:P ≤ J⊓H
 · rw [if_neg (show ¬ Q ≤ J⊓R from fun p=> l (sup_le (k.trans inf_le_left) (p.trans inf_le_left))),mul_zero]
 rw [if_neg k,zero_mul]
end factor
end YM.CF.Stilo
