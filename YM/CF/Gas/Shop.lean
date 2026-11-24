import YM.CF.Gas.Grade
import YM.CF.Palot.Jade
import YM.CF.Palot.Sparkle
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Lattice Branch Tenant Petal Palot Stilo Corona RG Push.AbsoluteSums Trees Ursell
open scoped Topology Classical BigOperators
variable {ι A E:Type}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][CommSemiring E]
def labelB(X:ι→leaf A)(F:Finset ι→ E)(P:Finset ι)(R:Crowd A):=if rhythm (fun i=>(X i).val) P=R then F P else 0
def Yard(X:ι→leaf A)(F: Finset ι→ E):Prop:= F ∅=1 ∧∀ P Q:Finset ι, Disjoint (P.biUnion fun i=>(X i).val) (Q.biUnion fun i=>(X i).val) → Disjoint P Q → F (P∪Q)=F P*F Q
abbrev folk {A:Type}(P:A→Sort*) (a:A) := P a -- remove
lemma yard_p {X:ι→leaf A}{F: Finset ι→ E}(h:Yard X F): Org X (labelB X F):=by
 let V(i):=(X i).val
 have hu(R:Crowd A)(P:Finset ι):fits X P R ↔ rhythm V P≤ R:= by unfold fits rhythm; rw [Finset.sup_le_iff]
 refine ⟨fun s t p=>?_,?_,?_⟩
 · by_cases e:rhythm V s=t; exact (hu _ s).mpr e.le; exact False.elim (p (if_neg e))
 · unfold labelB rhythm; simp [h.1]
 intro S T i j p a b; have he: Disjoint i j:= disjoint_left.mpr fun {x} k l=> fits_i (a x k) (b x l) p; have ha:=(hu S _).mp a; have hb:=(hu T _).mp b; have hf:= Disjoint.mono (bay_m ha) (bay_m hb) p
 rw [beats, beats] at hf
 change (if rhythm V _ = S⊔T then _ else _)=_; rw [show rhythm V (i∪j)=rhythm V i⊔rhythm V j from (by simp [rhythm,Finset.sup_union]),h.2 i j hf he]
 by_cases e:rhythm V i⊔rhythm V j=S⊔T
 · obtain ⟨a,b⟩:=splits_eq p ha hb e; rw [if_pos e,labelB,labelB,if_pos a,if_pos b]
 rw [if_neg e]; unfold labelB; split_ifs with l r u; · exact False.elim (e (congrArg₂ _ l r))
 all_goals simp
-- partial roof collection
def slateF(X:ι→leaf A)(v:leaf A):=univ.filter fun P:Finset ι=> rhythm (fun i=>(X i).val) P=beamH v.val
def bankB(X:ι→leaf A)(F:Finset ι→ E)(p:leaf A):E:=mintF (labelB X F) (beamH p.val)
lemma bank_p(X:ι→leaf A)(F:Finset ι→E)(L:leaf A):bankB X F L=∑ i∈ slateF X L,F i:=(sum_filter ..).symm
lemma charT(X:ι→leaf A)(F:Finset ι→E)(h:Yard X F): ∑ i:Finset ι,F i=hGas ∅ (bankB X F):=by
 change _=hGas _ _; apply Eq.trans _ (chimeU (∅:Finset A) (yard_p h)); apply sum_congr rfl; intro i _; symm; simp [labelB,eq_comm]
variable{n:Side}
-- assign costs
abbrev bill_X (X:ι→Support n)(w:ι→ℝ)(a:ℝ)(i:Site n):=∑ j:ι with i∈X j,w j*rent a (X j)
lemma zeroΩ (T:Support n)(p:Grove (terr _) T): coverNumber 0 T=T.card:=by
 have he:Lattice.halo 0 T=T:=Finset.eq_of_subset_of_card_le (halo_subset ..) (by simpa using halo_size T 0)|>.symm -- tune order
 apply le_antisymm; · apply Corona.list_cost (D:=T); unfold covers; rw [he]; dsimp only; exact ⟨Subset.refl _,rooted p⟩
 simpa using Corona.pays T 0
lemma ticket {X:ι→Support n}{w:ι→ℝ}{r c:ℝ}(h:∀ i,w i≠0→Grove (terr _) (X i))(t:∀ i,0 ≤ w i)(g:∀ i,bill_X X w r i ≤ c):Ac.Hit X 0 w r c:=by
 intro i; refine ⟨fun j=>?_,(hasSum_fintype _).summable,?_⟩; · dsimp only; split; exact mul_nonneg (t _) (Real.exp_pos _).le; exact le_rfl
 rw [tsum_fintype]; apply le_trans _ (g i); unfold bill_X; rw [sum_filter]; apply sum_le_sum; intro j _; split_ifs; · by_cases v:w j=0; rw [v,zero_mul,zero_mul]; rw [zeroΩ (X j) (h j v)]; rfl
 rfl
lemma coverB {X:ι→leaf A}{p:leaf A}{T:Finset ι}(h:T∈slateF X p):T.biUnion (fun i=>(X i).val)=p.val:= (beats _ _).symm.trans ((congrArg Stilo.bay ((mem_filter.mp h).2)).trans (bay_beam _))
variable{X:ι→Y n}
lemma slate_s {T:Finset ι}{v:Y n}(h:T∈slateF X v): Ac.Spark (fun i=>(X i).val) T:= (break_h (fun i=>(X i).val) (fun i=>(X i).property) v T (mem_filter.mp h).2).1
lemma pactG {T:Finset ι}(g:∀ i∈T,Grove (terr _) (X i).val)(p:Y n)(he:T∈slateF X p): Grove (terr _) p.val:=by
 let V(i):=(X i).val; obtain ⟨x,u⟩:= p.property; let Z:=p.val; obtain ⟨i,t,w⟩:= mem_biUnion.mp (show x∈ T.biUnion V from (coverB he).symm ▸ u); have hu(j)(l:j∈T): (X j).val ⊆Z:= (show V j ⊆T.biUnion V from roof_atom l).trans_eq (coverB he)
 apply trunk (S:=p.val) u; intro y v; obtain ⟨j,l,s⟩:= mem_biUnion.mp (show y∈ T.biUnion V from (coverB he).symm ▸ v)
 have hf(c:ι)(e: Ac.chain V T i c): ∀ y∈ V c,Origin (terr _) Z x y:=by
    induction e with
    | refl=> exact fun y e=>orig_sub (rooted (g i t) x w y e) (hu i t)
    | @tail a b _ h ih=> obtain ⟨q,l,o,p,k⟩:=h; exact fun y e=>(ih o p).trans (orig_sub (rooted (g b l) o k y e) (hu b l))
 exact hf j ((slate_s he).2 i t j l) y s
lemma bigA (T:Finset ι){w:ι→ℝ}(g:∀ i,0≤w i) :0≤heavy w T:= prod_nonneg fun i _=>g i
abbrev CoinX (X:ι→Y n)(w:ι→ℝ)(l:Y n):ℝ:=∑ T∈slateF X l,heavy w T
lemma coin_heat(w:ι→ℝ)(p:∀ i, w i ≠0→Grove (terr _) (X i).val)(v:Y n)(g:CoinX X w v≠0): Grove (terr _) v.val:=by obtain ⟨T,t,h⟩:= exists_ne_zero_of_sum_ne_zero g; exact pactG (fun i t=>p i (fun e=> h (prod_eq_zero t e))) v t
lemma starts {r γ δ q:ℝ}{w:ι→ℝ}(p:∀ i, w i≠0→Grove (terr _) (X i).val)(h:Ready (fun i=>(X i).val) 0 w r γ δ q)(k:0≤r)(i:Site n): bill_X stern (CoinX X w) r i ≤ γ*(1-q)⁻¹:=by
 let V(j):=(X j).val; have hp:=h.2.2.2.2.1; let t:=touches V 0 w r i; have ht : (∑ j:Finset ι,t j) ≤ γ*(1-q)⁻¹ :=by simpa [t] using budget_sum (touch_tail V 0 h i 0) univ
 apply le_trans _ ht; unfold bill_X CoinX slateF; simp_rw [sum_filter,sum_mul,ite_mul]; rw [←sum_filter]; -- leaves inner sum-univ filtered
 rw [sum_comm]; apply sum_le_sum; intro j _; have he(l:Y n)(e:j∈slateF X l):j.biUnion V=l.val:=coverB e
 by_cases u': ∃ l:Y n,i∈l.val ∧ j∈slateF X l
 swap
 · rw [sum_eq_zero]; · exact (show 0≤t j from (by unfold t touches; split; exact prod_nonneg (fun i _=> mul_nonneg (hp _) (Real.exp_pos _).le); exact le_rfl)) -- tune touch namespace
   intro y a; rw [if_neg,zero_mul]; exact fun s=>u' ⟨y,(mem_filter.mp a).2,(mem_filter.mpr ⟨mem_univ _,s⟩)⟩
 obtain ⟨l,u,g⟩:= u'; rw [sum_eq_single l]; swap
 · intro z v a; rw [if_neg,zero_mul]; exact fun s=> a (Subtype.ext ((he z (mem_filter.mpr ⟨mem_univ _,s⟩)).symm.trans (he l g)))
 swap; · exact fun b=>False.elim (b (mem_filter.mpr ⟨mem_univ _,u⟩))
 rw [if_pos (mem_filter.mp g).2]; unfold t touches; rw [if_pos ⟨slate_s g,(he l g).symm ▸ u⟩, prod_mul_distrib]; by_cases p': heavy w j=0
 · rw [p',zero_mul,show ∏ i∈j,w i=0 from p',zero_mul]
 let B:=terr n; have hh(q)(t:q∈j): Grove B (V q):=p q (fun a=>p' (prod_eq_zero t a)); apply mul_le_mul_of_nonneg_left _ (bigA _ hp); unfold rent currency; rw [← Real.exp_sum,←Finset.mul_sum]; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ k; rw [show (stern l).card=coverNumber 0 l.val from (zeroΩ l.val (pactG hh l g)).symm, ←Nat.cast_sum]; exact_mod_cast ((he l g) ▸ Ac.cover V 0 (slate_s g)) -- tune
end YM.CF.Gas
