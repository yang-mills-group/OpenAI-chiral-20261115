import YM.CF.Pastry.Bliss
import YM.CF.BProof.Garden.Green
import YM.CF.BProof.Wick.Quest
/-! Formal matching expansion for eq:B-PfC. Instead of introducing extra labelled
matchings and proving symmetry of graph signs, use Fock on the FORMAL Wick index
alphabet; pair overlaps/repeated-letter tests then enforce the signs for us. (This
Fock space is NOT the FiniteGaugeData physical state space.) -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]
def Nose(C:Op I)(l:List I):ℂ:= inner ℂ (pairWave (cc C)) (chime put (vacuum I) l)
theorem pfaffirm{C:Op I}(x:Cᵀ= -C): Scores C (Nose C):=by
 let V:= cc C; let A(i:I):=star (coupleRow V i); let p:=vacuum I; have ht:Vᵀ= -V:=by rw [show Vᵀ=cc (Cᵀ) from ?_,x,cc_neg]; ext i j; rfl
 have hh(i):A i=∑ j, C i j • takeF j:=by simp only [A,coupleRow,star_sum,star_smul,V,cc_apply,star_star]
 have he(i):acts (A i) p=0:=by rw [hh,act_sum]; apply sum_eq_zero; intro j _; unfold p; rw [act_smul,←remove_take,vacuum_take,smul_zero]
 have hg(i j:I): antiB (A i) (put j)= C i j • 1:=by rw [hh,antiB_sum]; simp_rw [antiB_smul, antiB,mixed]; simp
 refine ⟨?_,?_⟩; · unfold Nose; rw [emptyChime,←inner_conj_symm]; simp only [vacuum,basis_inner,paired_vac,map_one]
 intro i l; unfold Nose; rw [charm,← act_inner (put i),show star (put i)=takeF i from rfl,pull ht,← star_star (coupleRow _ i),act_inner,plume put A p C he hg i l]; generalize picks l=t; induction t with
 | nil=> simp
 | cons a b ih=> simp only [List.map_cons,List.sum_cons,inner_add_right,ih]; rw [seatsC,inner_smul_right]
-- Any such recursion gives Nose; comparison may only match pair values in forward direction
-- on the chosen ordering. Local order for here is a relation ℛ on indices.
lemma jut {l:List I}{z:Bout I} (h:z∈picks l) : List.Sublist z.back l ∧ z.back.length<l.length ∧ z.front ∈ l:=by
 induction l generalizing z with
 | nil=> simp [picks] at h
 | cons i l ih=>
    simp only [picks,List.mem_cons,List.mem_map] at h; rcases h with h |⟨t,f,rfl⟩; subst z; exact ⟨List.Sublist.cons i (List.Sublist.refl _),by simp,by simp⟩
    obtain ⟨a,b,c⟩:=ih f; exact ⟨a.cons₂ i,Nat.succ_lt_succ b,List.mem_cons_of_mem i c⟩ -- notation tune
lemma compatible{f:List I→ℂ}{d:I→I→ℂ}{R:I→I→Prop}{C:Op I}(x:Cᵀ= -C)(p:Scores d f)(h:∀ i j,R i j → d i j=C i j)(l:List I)(g:l.Pairwise R): f l=Nose C l:=by
 generalize hk:l.length=k; induction k using Nat.strong_induction_on generalizing l with
 | h k ih=>
   cases l with
   | nil=> rw [p.clear,(pfaffirm x).clear]
   | cons i l=>
     obtain ⟨a,b⟩:= List.pairwise_cons.mp g; rw [p.consist,(pfaffirm x).consist]; congr 1; apply List.map_congr_left; intro j u; obtain ⟨s,e,t⟩:=jut u; rw [h _ _ (a j.front t),ih _ (by rw [←hk]; exact lt_trans e (by simp)) _ (b.sublist s) rfl] -- tune
-- lettering APIs
abbrev word (l:List I) := rollC put l
lemma word_c(l:List I)(i:I): word (i::l)= put i*word l:= rfl
lemma word_ap (l t:List I): word (l++t)=word l*word t:=by unfold word rollC; simp
lemma word_pow (l:List I): ‖word l‖≤1:=by unfold word rollC; induction l with | nil=> simp | cons a b ih=> simp only [List.map_cons,List.prod_cons]; exact (norm_mul_le ..).trans (mul_le_one₀ (payPut _) (norm_nonneg _) ih)
lemma word_left (l:List I)(i:I)(f:i∈l) : put i * word l=0:=by induction l with
 | nil=> simp at f
 | cons j l ih=>
    rw [word_c]; rcases List.mem_cons.mp f with g|g; subst j; rw [←mul_assoc,put_sq,zero_mul]
    rw [←mul_assoc, eq_neg_of_add_eq_zero_left (put_put i j),neg_mul,mul_assoc,ih g,mul_zero,neg_zero]
lemma word_tug (l:List I)(i:I): ∃ c:ℂ, put i*word l=c • (word l*put i):=by
 induction l with
 | nil=> exact ⟨1,by simp [word,rollC]⟩
 | cons j l ih=> obtain ⟨c,g⟩:=ih; refine ⟨-c,?_⟩; simp only [word_c]; rw [←mul_assoc,eq_neg_of_add_eq_zero_left (put_put i j),neg_mul,mul_assoc,g, Algebra.mul_smul_comm, ←mul_assoc (put j),neg_smul] -- maybe unfold g
lemma word_blank (l t: List I)(i:I)(h:i∈l)(g:i∈t): word l*word t=0:=by
 induction l with
 | nil=> simp at h
 | cons j l ih=>
   rw [word_c,mul_assoc]; rcases List.mem_cons.mp h with v|v; subst j; -- need move i through rest inverse? word_tug only opposite. can prove using t_left and anticomm price tug inverse
   · obtain ⟨c,H⟩:=word_tug l i; rw [←mul_assoc,H, Algebra.smul_mul_assoc,mul_assoc,word_left t i g,mul_zero,smul_zero]
   rw [ih v,mul_zero]
lemma wordP (l:List I)(u:Even l.length){S:Finset I}(v:l.toFinset ⊆ S) : Flour S (word l) ∧ Sector S false (word l):=by
 induction l using List.twoStepInduction with
 | nil=> exact ⟨Flour.grainE,Sector.one⟩
 | singleton i=> simp at u
 | cons_cons i j l ih=>
   simp only [List.toFinset_cons,insert_subset_iff] at v; obtain ⟨a,b,d⟩:=v; obtain ⟨c,h⟩:= ih (by simpa only [List.length_cons,Nat.even_add_one,not_not] using u) d; unfold word rollC; simp only [List.map_cons,List.prod_cons,←mul_assoc]; exact ⟨(Flour.putPut S a b).mul c, ((Sector.up i a).mul (Sector.up j b)).mul h⟩
end YM.CF.BProof.Crystal
