import YM.CF.Gas.Shop
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Lattice Branch Tenant Petal Palot Stilo Corona RG Push.AbsoluteSums Trees Ursell Relation Graph
open scoped Topology Classical BigOperators
variable {ι A D G E:Type}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][NormedCommRing E][NormOneClass E][NormedAlgebra ℝ E][CompleteSpace E][TopologicalSpace D]
variable {n:Side}
local notation "b" n=>terr n
abbrev creditS (X:Y n)(f:D→E)(w:ℝ)(L:Lodge (Site n) E D G):Prop := Token L X.val f w (Grove (b n))
variable {X:ι→Y n}
lemma armed (F:Finset ι→ E)(h:Yard X F){w:Y n→ℝ}(v:∀ i,‖bankB X F i‖ ≤ w i){a c γ δ:ℝ}(p:0 ≤a) (r: Ready stern 0 w a γ δ c): ∑ i:Finset ι,F i= exp (∑ i:Y n,jingle (bankB X F) i):=by
 rw [charT X F h]; let V:= bankB X F; change hGas ∅ V=_; rw [show hGas ∅ V=south ∅ V from by simp only [hGas,south,empty_subset,and_true,Finset.disjoint_empty_left],sung ∅ (W:=V) r p v]; simp [V] -- tune implicit
lemma κc(X:Clusters (Y n))(k:SongQ X.1): (X.2 k).val ⊆ (tideU X).val:=fun _ h=> mem_biUnion.mpr ⟨_,mem_univ _,h⟩
lemma ζlink (z:Clusters (Y n))(p:coefficient gRule z.2≠0)(h:∀ i,Grove (b n) (z.2 i).val): Grove (b n) (tideU z).val:=by
 obtain ⟨g,v,t⟩:= exists_ne_zero_of_sum_ne_zero (show (mass (pot gRule z.2))≠0 from p) -- tune
 obtain ⟨t,l⟩:=belongs.mp v; obtain ⟨i,u⟩:=(z.2 none).property; apply trunk (κc z none u); intro y p
 obtain ⟨j,hj,e⟩:=mem_biUnion.mp (show y∈ (tideU z).val from p); let L(a):=(z.2 a).val; let X':=(tideU z).val
 have ht(j)(s:ReflTransGen (Graph.link g) none j):∀ y∈ L j, Origin (b n) X' i y:=by
    induction s with
    | refl=> exact fun y p=>orig_sub (rooted (h none) i u y p) (κc z none)
    | @tail a c _ H ih=>
       have hv:¬ Disjoint (L a) (L c):=Ursell.allow gRule z.2 ⟨H.1,t H.2⟩; obtain ⟨x,g,p⟩:= not_disjoint_iff.mp hv; exact fun y e=>(ih x g).trans (orig_sub (rooted (h c) x p y e) (κc z c)) -- tune
 exact ht j (l none j) y e
abbrev wageA(z:Clusters (Y n))(i:Y n)(w:Y n→ℝ) := if i=tideU z then clusters gRule w z.2 else 0
abbrev strictX(z:Clusters (Y n))(i:Y n)(W:Y n→D→E)(x:D) := if i=tideU z then guava gRule (fun i=>W i x) z else 0
variable{w:Y n→ℝ}{W:Y n→ D→E}{a d γ δ:ℝ}{L:Lodge (Site n) E D G}
def sumTax(w:Y n→ℝ)(i:Y n) :=∑' z, wageA z i w
lemma τ_w(i:Y n) (t:Ready stern 0 w a γ δ d)(p:0≤a): Summable (fun z=>wageA z i w):=by
 obtain ⟨x,u⟩:=i.property; have ht:=Ursell.log_hit_tail _ _ _ testG t p 0 x
 refine ht.2.1.of_nonneg_of_le (fun j=>?_) (fun j=>?_); · unfold wageA; split; exact clusters_nonneg _ t.2.2.2.2.1 _; exact le_rfl
 unfold wageA; split; next h=>
   rw [if_pos ⟨Nat.zero_le _,show x∈ (tideU j).val from h ▸ u⟩]; exact le_mul_of_one_le_right (clusters_nonneg _ t.2.2.2.2.1 _) (Real.one_le_exp (mul_nonneg p (by positivity)))
 exact ht.1 _
lemma dues(i:Y n)(z:Clusters (Y n))(g:∀ i,creditS i (W i) (w i) L): creditS i (strictX z i W) (wageA z i w) L:=by
 by_cases t:i=tideU z; swap; · unfold wageA; rw [show strictX z i W= fun _=>0 from funext fun _=> if_neg t -- tune
                                                            ,if_neg t]; exact Token.nought
 subst i; let q:= tideU z; let C:= q.val
 let a(j):=(g (z.2 j)); let B(j):=W (z.2 j); let v(j):=w (z.2 j); let c:ℝ:= coefficient gRule z.2/(z.1+1).factorial
 have ht(P:Finset (SongQ z.1)): Token L (P.biUnion fun j=> (z.2 j).val) (fun x=>∏ j∈P,B j x) (∏ j∈P,v j) (fun _=>True):=by
    induction P using Finset.induction_on with | empty=> simp_rw [biUnion_empty,prod_empty]; exact Token.sole trivial|insert i P l ih=> rw [biUnion_insert]; simp_rw [prod_insert l]; exact Token.together (g (z.2 i)) ih (fun _ _=>trivial)
 have he:clusters gRule w z.2=‖c‖ * ∏ j:SongQ z.1,v j:=by unfold clusters c; rw [mul_div_right_comm,norm_div,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity)]
 have hX : Token L q.val (strictX z q W) (clusters gRule w z.2) (fun _=>True):=by
    rw [show strictX z q W=fun x=> c • ∏ j:SongQ z.1,B j x from funext fun x=> if_pos rfl,he]; exact Token.payT (ht univ) _
 rw [wageA,if_pos rfl]; refine {hX with shape:=fun p=>?_}
 rw [he] at p; apply ζlink; · intro v; apply p; simp [c,v]
 intro j; exact (a j).shape (fun u=> p (by rw [prod_eq_zero (mem_univ j) u,mul_zero]))
def Fiscal (W:Y n→D→E)(q:Y n)(x:D):=jingle (fun i=>W i x) q
lemma fiscal_g(t:Ready stern 0 w a γ δ d)(p:0≤a)(g:∀ i,creditS i (W i) (w i) L)(i:Y n): creditS i (Fiscal W i) (sumTax w i) L:=by
 let X(j:ℕ)(y:Tuple (Y n) j):= wageA ⟨j,y⟩ i w; let W'(j:ℕ)(x:Tuple (Y n) j):=strictX ⟨j,x⟩ i W; let M:Clusters (Y n)→ℝ:=fun i=> X i.1 i.2; have h:Summable M:=τ_w i t p; have hz(x:D):Summable (fun z:Clusters (Y n)=> W' z.1 z.2 x):=Summable.of_norm_bounded h (fun z=> (L.normF _).trans ((dues i z g).owns x))
 rw [show Fiscal W i=(fun x=>∑' j:ℕ,∑ y:Tuple (Y n) j,W' j y x) from funext fun x=>by
    change (∑' z:Clusters (Y n), W' z.1 z.2 x)=_; rw [(hz x).tsum_sigma]; simp_rw [tsum_fintype],show sumTax w i=∑' j:ℕ,∑ y:Tuple (Y n) j,X j y from (h.tsum_sigma.trans (tsum_congr fun _=> tsum_fintype ..))]
 exact Token.storeT _ _ (fun j=>Token.mass _ _ _ (fun s _=>dues i ⟨j,s⟩ g)) (by simpa [M] using h.sigma)
lemma taxesC(t:Ready stern 0 w a γ δ d)(p:0 ≤a)(o:Site n): bill_X stern (sumTax w) a o ≤ γ*(1-d)⁻¹:=by
 let Q(z:Clusters (Y n)):=if 0 ≤ z.1 ∧ o∈(tideU z).val then clusters gRule w z.2*currency 0 a (tideU z).val else 0
 have ht:= (Ursell.log_hit_tail _ _ _ testG t p 0 o); apply le_trans _ (show (∑' z,Q z) ≤ _ from (by simpa [Q,tideU] using ht.2.2)); unfold bill_X sumTax; simp_rw [←tsum_mul_right]; rw [←Summable.tsum_finsetSum]; swap; · exact fun i _=> (τ_w i t p).mul_right _
 apply Summable.tsum_le_tsum _ _ ht.2.1; swap; · exact summable_sum fun i _=>(τ_w i t p).mul_right _
 intro z; by_cases h:o∈ (tideU z).val
 · rw [sum_eq_single (tideU z)]; · unfold wageA; rw [if_pos rfl,if_pos ⟨Nat.zero_le _,h⟩]; apply mul_le_mul_of_nonneg_left _ (clusters_nonneg _ t.2.2.2.2.1 _); unfold rent currency; have hp:(stern (tideU z)).card≤coverNumber 0 (tideU z).val:= (by simpa using pays (tideU z).val 0); exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hp) p)
   exact fun i _ v=>by rw [wageA,if_neg v,zero_mul]
   exact fun v=> False.elim (v (mem_filter.mpr ⟨mem_univ _,h⟩)) -- indent
 rw [sum_eq_zero]; exact ht.1 _
 intro i l; rw [wageA,if_neg fun (jU : i=tideU z)=>h (show _ from jU ▸ (show o∈i.val from (mem_filter.mp l).2)),zero_mul]
end YM.CF.Gas
