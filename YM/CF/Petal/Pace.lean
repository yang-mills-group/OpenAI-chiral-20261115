import YM.CF.Petal.Lodge
import YM.CF.Support.Hit

/-! Small support norms for log and inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open scoped BigOperators Topology
open Filter Branch Finset NormedSpace
variable {Y E D G : Type*} [DecidableEq Y] [Fintype Y] [NormedCommRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E] [TopologicalSpace D] {L : Lodge Y E D G} {f : D→E} {u v : ℝ} {p : Seal Y→Prop}
namespace Pool
lemma negative (h : Pool L u v p f) : Pool L u v p (fun x=> -f x) := by simpa using h.scaleW (-1)
lemma pows (h : Pool L u v p f) (e : 0≤u) (k : ∀ S T, p S→p T→p (S∪T)) (n : ℕ) : Pool L u (v^(n+1)) p (fun x=>f x^(n+1)) := by
  induction n with
  | zero=> simpa using h
  | succ n ih=> rw [pow_succ]; simp_rw [pow_succ (f _) (n+1)]; exact ih.combine h e k
lemma massP {E : Type*} [NormedRing E] [CompleteSpace E] [NormOneClass E] (x : E) (h : ‖x‖<1) : Ring.inverse (1+x)=1+∑' i:ℕ, (-x)^(i+1) := by
  have hv : ‖-x‖<1 := by rw [norm_neg]; exact h
  have hx : Ring.inverse (1- -x)=∑' i:ℕ,(-x)^i := NormedRing.inverse_one_sub _ hv -- tune
  rw [sub_neg_eq_add] at hx; rw [hx]
  simpa using ((summable_geometric_of_norm_lt_one hv).sum_add_tsum_nat_add 1).symm
lemma sized (v : ℝ) (h : 0≤v) (g : v<1) : Summable (fun n:ℕ=> v^(n+1)) ∧ ∑' i:ℕ, v^(i+1)=v/(1-v) := by
  refine ⟨(summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one h g),?_⟩
  simp_rw [pow_succ']; rw [tsum_mul_left,tsum_geometric_of_lt_one h g,div_eq_mul_inv]
def Plus (T : Seal Y) := p T ∨ T=∅ -- p unused name?
lemma room_name (h : Pool L u (1/4) p f) (e : 0≤u) (k : ∀ S T,p S→p T→p (S∪T)) (x:D) : IsUnit (1+f x) := by
  have ht := (L.normF _).trans (h.price e x)
  have he : ‖-f x‖<1 := by rw [norm_neg]; exact ht.trans_lt (by norm_num)
  have hx : IsUnit (1- -f x) := Units.isUnit (Units.oneSub _ he); rwa [sub_neg_eq_add] at hx
lemma steam_ticket (h : Pool L u (1/4) p f) (e : 0≤u) (k : ∀ S T,p S→p T→p (S∪T)) : Pool L u (1/3) p (fun x=>steam (f x)) ∧ ∀ x, exp (steam (f x))=1+f x := by
  refine ⟨?_,fun x=>steam_one ((L.normF _).trans_lt ((h.price e x).trans_lt (by norm_num)))⟩
  obtain ⟨w,W⟩ := sized (1/4) (by norm_num) (by norm_num)
  have ht n := h.pows e k n
  let F (n:ℕ) := (1/4:ℝ)^(n+1)
  have he : Pool L u (∑' n,F n) p (fun x=>steam (f x)) := ts _ F (fun i=> ((ht i).scaleW (bcoef i)).costUp ((mul_le_of_le_one_left (by positivity) (bc_norm i)))) w e
  unfold F at he; apply he.costUp; rw [W]; norm_num
lemma ounce (h : Pool L u (1/4) p f) (e : 0≤u) (k : ∀ S T,p S→p T→p (S∪T)) : Pool L u 2 (fun T=>p T ∨ T=∅) (fun x=> Ring.inverse (1+f x)) := by
  obtain ⟨w,W⟩ := sized (1/4) (by norm_num) (by norm_num)
  let r := fun T:Seal Y=>p T ∨ T=∅
  let F (n:ℕ) := (1/4:ℝ)^(n+1)
  have ht : Pool L u (∑' n,F n) p (fun x=>∑' i:ℕ, (-f x)^(i+1)) := ts _ F (fun n=> h.negative.pows e k n) w e
  have he := (oneF (L:=L) (a:=u) (show r ∅ from Or.inr rfl)).sumUp (ht.shift (fun _=>Or.inl))
  have hp x := massP (f x) ((L.normF _).trans_lt ((h.price e x).trans_lt (by norm_num)))
  unfold F at he; simp_rw [hp]; apply he.costUp; rw [W]; norm_num
end Pool
-- density conversion
structure Charge (L : Lodge Y E D G) (b : Branch.Field Y) (u K : ℝ) (F : Seal Y → D→E) (c : Seal Y→ℝ) : Prop where
  pledge S : Token L S (F S) (c S) (Grove b)
  rankV y : hitE u c y ≤ K
def bulk (u C : ℝ) := ∑' i:ℕ, (Real.exp (-u/2*(i:ℝ))*(C*((i:ℝ)+1)^4))
def Shell (B : Branch.Field Y) (y : Y) (S : Seal Y) := Grove B S ∧ y∈ S
lemma housing {C K : ℝ} {b : Branch.Field Y} {v : Y→D→E} (q : 0≤K) (p : 0≤C) (k : 0<u) (R : ∀ y m, ((bay b y m).card:ℝ) ≤ C*((m:ℝ)+1)^4) (h : ∀ y:Y, Pool L u K (Shell b y) (v y)) : ∃ (F : Seal Y→D→E) (c : Seal Y→ℝ), Charge L b (u/2) (bulk u C*K) F c ∧ ∀ x, (∑ y:Y, v y x)=∑ S, F S x := by
  choose P A g V U using h
  let f (S : Seal Y) (x:D) := ∑ y, P y S x
  let c (S:Seal Y) := ∑ y,A y S
  have he S : Token L S (f S) (c S) (Grove b) := Token.mass univ _ _ (fun i _=> (g i S).shift (fun p=>p.1))
  refine ⟨f,c,⟨he,fun y=>?_⟩,fun x=>by simp_rw [U]; exact sum_comm⟩
  let M : ℕ := Fintype.card Y; have hx : ∀ S:Seal Y, S.card∈range (M+1) := fun i=> mem_range.mpr (lt_of_le_of_lt (card_le_univ _) (by unfold M; omega))
  let s (i:ℕ) := (hit0 y).filter fun x=> x.card=i; let m (i:ℕ) := Real.exp (-u/2*i)
  have hk : hitE (u/2) c y= ∑ i∈range (M+1),∑ S∈s i,rent (u/2) S*c S := by simp_rw [s,sum_filter,sum_comm (s:=range (M+1))]; simp [hx,hitE]
  have hp i : ∑ S∈s i,rent (u/2) S*c S≤m i*(C*((i:ℝ)+1)^4)*K := by
    have hl S (p:S∈s i) : c S=∑ j∈bay b y i,A j S := by
      unfold c; rw [←sum_subset (subset_univ _)]; intro a _ v; by_contra q
      obtain ⟨hh,hs⟩ := (g a S).shape q
      apply v; rw [←(mem_filter.mp p).2]; exact hh.basin (mem_filter.mp (mem_filter.mp p).1).2 hs
    have hX S (p:S∈s i) : rent (u/2) S=m i*rent u S := by unfold rent m; rw [←Real.exp_add,(mem_filter.mp p).2]; congr 1; ring
    calc
      _ = m i * ∑ j∈bay b y i,∑ S∈s i,rent u S*A j S := by
        rw [sum_comm (s:=bay ..), mul_sum]; apply sum_congr rfl; intro S t; rw [hl _ t,hX _ t,mul_assoc]; congr 1; exact mul_sum ..
      _ ≤ m i * ∑ j∈bay b y i,K := mul_le_mul_of_nonneg_left (sum_le_sum (fun j _=> le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun S _ _=>mul_nonneg (rent_pos ..).le (g j S).price)) (V j))) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_assoc (m i), sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (R y i) q) (Real.exp_pos _).le
  rw [hk]; apply (sum_le_sum (fun i (_:i∈range (M+1))=>hp i)).trans; rw [←sum_mul]; apply mul_le_mul_of_nonneg_right _ q; exact (fund_hit u C k p).sum_le_tsum (range (M+1)) fun i _=>by positivity
end YM.CF.Petal
