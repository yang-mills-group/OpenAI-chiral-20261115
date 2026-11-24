import YM.CF.BPress.Ledger
import YM.CF.Support.Product
/-! `eq:B-enorm` real variant with predicates (S subset only); exact submultiplicativity. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson Branch Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {I Y: Type*}[Fintype I][Fintype Y][DecidableEq Y]
def state (S A B : Seal Y):Prop:=∀ p∈S,p∈ A↔p∈ B
def Zoned (S:Seal Y)(f:Seal Y→ℝ): Prop:= ∀ A B,state S A B→f A=f B
structure Centr (Y I:Type*) where
 home : I→Y
 trunkP : Finset Y→Prop
 perp [DecidableEq Y] {S T : Finset Y}{v}: trunkP S→trunkP T→v∈S→ v∈T→trunkP (S∪T)
variable (c:Centr Y I)
abbrev Collected (Y I : Type*) := Seal Y→ Matrix I I ℝ
abbrev bare (a k:Branch.Seal Y→Toll I):=a+k
structure Currency (S:Seal Y)(b:Toll I)(A:Collected Y I):Prop where
 trunk i j : b i j≠0→ (c.trunkP S ∧ c.home i∈ S∧ c.home j∈ S)
 sees (i j): Zoned S (fun T=>A T i j)
 pay (i j)(T:Seal Y): |A T i j| ≤ b i j
-- all coefficients may choose independently of T.
def Aura (a k:ℝ)(A:Collected Y I): Prop:= ∃ (f:Seal Y→Collected Y I)(b:Seal Y→Toll I), (∀ S,Currency c S (b S) (f S))∧Branch.Ledger a b k ∧∀ T,A T=∑ i,f i T
variable {S T : Seal Y}{b p : Toll I}{f g:Collected Y I}{a k t:ℝ}{c}
lemma Currency.nonn (h:Currency c S b f) (i j) : 0 ≤ b i j:= (abs_nonneg _).trans (h.pay i j ∅)
namespace Currency
lemma zero : Currency c S 0 (fun _=>0):=⟨ by simp,fun _ _ _ _ _=>rfl,by simp⟩
lemma add (v:Currency c S b f)(h:Currency c S p g): Currency c S (b+p) (fun T=> f T + g T) := by -- name collision
 refine ⟨fun i j t=>?_, fun i j a b t=>by dsimp only; rw [Matrix.add_apply,Matrix.add_apply]; exact congrArg₂ (·+·) (v.sees i j a b t) (h.sees i j a b t),fun i j T=>?_⟩
 · by_cases z:b i j=0; apply h.trunk; contrapose! t; simp only [t,z, Pi.add_apply, add_zero]; exact v.trunk i j z
 rw [Matrix.add_apply]; exact (abs_add_le ..).trans (add_le_add (v.pay ..) (h.pay ..))
lemma scale (h:Currency c S b f)(k:ℝ): Currency c S (fun i j=> |k| * b i j) (fun T=> k • f T):=⟨fun i j p=>h.trunk i j (right_ne_zero_of_mul p),fun i j A B v=>by dsimp only; rw [Matrix.smul_apply,Matrix.smul_apply]; exact congrArg (fun x:ℝ=> k • x) (h.sees i j A B v),fun i j T=>by rw [Matrix.smul_apply,smul_eq_mul,abs_mul]; exact mul_le_mul_of_nonneg_left (h.pay ..) (abs_nonneg _)⟩
lemma product (h:Currency c S b f)(g':Currency c T p g): Currency c (S∪T) (fun i j=> ∑ k,b i k*p k j) (fun V=> f V*g V):=by
 refine ⟨fun i j t=> ?_, fun i j A B u=>?_, fun i j V=>?_⟩
 · obtain ⟨k,_,t⟩:= exists_ne_zero_of_sum_ne_zero t; obtain ⟨p,q,u⟩:= h.trunk i k (left_ne_zero_of_mul t); obtain ⟨a,g,v⟩:= g'.trunk k j (right_ne_zero_of_mul t); exact ⟨c.perp p a u g,mem_union_left T q,mem_union_right S v⟩
 · dsimp only; rw [Matrix.mul_apply,Matrix.mul_apply]; apply sum_congr rfl; intro k _; exact congrArg₂ (·*·) (h.sees i k A B (fun i v=> u i (mem_union_left T v))) (g'.sees k j A B (fun i v=> u i (mem_union_right S v)))
 rw [Matrix.mul_apply]; refine (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun k _=>?_)); rw [abs_mul]; exact mul_le_mul (h.pay ..) (g'.pay ..) (abs_nonneg _) (h.nonn ..)
lemma sumT {J:Type*}(T:Finset J)(b:J→Toll I)(f:J→Collected Y I)(h:∀ j∈T,Currency c S (b j) (f j)):Currency c S (∑ j∈T,b j) (fun V=>∑ j∈T,f j V):=by induction T using Finset.induction_on with| empty=>simpa using (zero (S:=S))|@insert i T u ih=> simp_rw [Finset.sum_insert u]; exact (h i (mem_insert_self i T)).add (ih (fun i g=> h i (mem_insert_of_mem g)))
-- real entry tsum version: assume summable each entry via ledger.
lemma flow (H:ℕ→Toll I)(F:ℕ→Collected Y I)(w:∀ i, Currency c S (H i) (F i))(v:∀ i j,Summable fun k=>H k i j): Currency c S (fun i j=>∑' n:ℕ,H n i j) (fun A i j=> ∑' n:ℕ,F n A i j):=by -- eta Matrix issue
 refine ⟨fun i j t=>?_,fun i j A B u=>?_ ,fun i j T=>?_⟩
 · by_contra hj; apply t; change ∑' n:ℕ, H n i j=0; have he (k:ℕ): H k i j=0:= not_not.mp (fun v=> hj ((w k).trunk i j v)); simp_rw [he,tsum_zero] -- tune
 · exact tsum_congr fun k=>(w k).sees i j A B u
 have he := (v i j).of_nonneg_of_le (fun k:ℕ=> (abs_nonneg (F k T i j))) (fun k=> (w k).pay i j T); exact (norm_tsum_le_tsum_norm (f:=fun k:ℕ=> F k T i j) he).trans (he.tsum_le_tsum (fun k=>(w k).pay i j T) (v i j)) -- tune
end Currency

lemma Aura.pack {J:Type*}[Fintype J](w:J→ Seal Y)(H:J→ Toll I)(F:J→ Collected Y I)(p:∀ i,Currency c (w i) (H i) (F i))(q:0≤k)(u:∀ x,f x = ∑ i,F i x)(H₁:∀ i,∑ j:I,∑ l:J,rent a (w l)*H l i j≤ k)(H₂:∀ j:I,∑ i:I,∑ l:J,rent a (w l)*H l i j≤ k): Aura c a k f:=by
 let b:=fun S:Seal Y=>∑ i∈dest w S, H i; let g:= fun (S A : Seal Y)=>∑ i∈dest w S,F i A; have he (i j:I) : saleM a b i j= ∑ l:J,rent a (w l)*H l i j:=by
   rw [lump w (fun l=>_)]; unfold saleM b; apply sum_congr rfl; intro S _; simp_rw [Finset.sum_apply,mul_sum]; apply sum_congr rfl; intro l v; rw [show w l=S from (mem_filter.mp v).2] -- tune
 refine ⟨g,b,fun S=> Currency.sumT _ H F (fun i v=> (show w i=S from (mem_filter.mp v).2) ▸ p i),⟨q,?_,?_⟩,fun x=>?_⟩; simp_rw [he]; exact H₁; simp_rw [he]; exact H₂; rw [u]; exact lump w _
namespace Aura
lemma scale (h:Aura c a k f)(d:ℝ): Aura c a (|d| *k) (fun T=> d • f T):= by obtain ⟨b,F,p,q,h⟩:= h; exact ⟨_,_,fun S=>(p S).scale d,q.funds (abs_nonneg _),fun x=>by dsimp only; rw [h,smul_sum]⟩
lemma weaken (h:Aura c a k f)(d:k≤t): Aura c a t f:= by obtain ⟨b,F,p,q,h⟩:= h; exact ⟨b,F,p,q.book d,h⟩
variable [DecidableEq I]
lemma walk (h:Aura c a k f)(u:Aura c a t g)(p:0≤a): Aura c a (k*t) (fun S=> f S * g S):=by
 obtain ⟨F,M,b,H,h⟩:=h; obtain ⟨G,N,q,Q,u⟩:=u; let w(S:Seal Y×Seal Y):=S.1∪S.2; let K(S:Seal Y×Seal Y)(i j:I):=∑ l:I,M S.1 i l*N S.2 l j; refine pack w K _ (fun S=> (b S.1).product (q S.2)) (mul_nonneg H.posP Q.posP) (fun S=>?_) (fun i=>?_) (fun j=>?_) -- tune
 · rw [h,u,Fintype.sum_prod_type]; simp_rw [sum_mul,mul_sum]
 · have he:=slope_row (fun i=> (b i).nonn) (fun i=>(q i).nonn) H Q p i; apply le_of_mul_le_mul_left (a:=(2:ℝ)) ?_ (show (0:ℝ)<2 by norm_num); unfold w K; unfold charge at he; simp_rw [mul_sum, mul_left_comm (rent _ _) (2:ℝ)] at he; simp_rw [mul_sum]; convert! he using 1 -- tune simp loops
 have he:=slope_col (fun i=> (b i).nonn) (fun i=>(q i).nonn) H Q p j; apply le_of_mul_le_mul_left (a:=(2:ℝ)) ?_ (show (0:ℝ)<2 by norm_num); unfold w K; unfold charge at he; simp_rw [mul_sum,mul_left_comm (rent _ _) (2:ℝ)] at he; simp_rw [mul_sum]; convert! he using 1
end Aura
end YM.CF.BPress.Weave
