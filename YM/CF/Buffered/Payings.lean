import YM.CF.Buffered.Changing
/-! Auxiliary Wick estimate, extensive in power, uniform in number of
extra letters apart from PER LETTER cost `a * contractionBound`. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Cache
open Function Filter Metric Fock Finset Flare
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n] [LinearOrder n]
variable {m:Type*}
private def repeat1 (x:m) (H:List (Cart m)) (b:Deal) := H.map (fun y=>(x,b)::y)
def script : List m→ List (Cart m) | []=>[[]] | x::l => repeat1 x (script l) .zero ++ repeat1 x (script l) .left ++ repeat1 x (script l) .right ++ repeat1 x (script l) .error
private lemma rp_property (x:m)(L:List m)(b:Deal)(h:∀ i∈script L,i.map Prod.fst=L)(i:Cart m) (p:i∈repeat1 x (script L) b): i.map Prod.fst=x::L:=by obtain ⟨y,t,rfl⟩:=List.mem_map.mp p; simp [h y t] -- defeq
lemma script_length (L:List m): (script L).length=4^L.length:=by induction L with | nil=>rfl| cons i L ih=> simp [script,repeat1,ih,pow_succ']; omega
lemma script_law (L:List m) (i: Cart m) (p:i∈script L): i.map Prod.fst=L:=by
 induction L generalizing i with
 | nil=>simp only [script,List.mem_singleton] at p; subst i; rfl
 | cons x l h=>rw [script] at p; simp only [List.mem_append] at p; rcases p with ((p|p)|p)|p <;> exact rp_property x l _ h i p
variable [Fintype m] [DecidableEq m]
variable {S:n→m}
variable (S) (W:Finset n)(A B:m→ FC n)
omit [Fintype m] in
private lemma rp_sum (x:m)(L:List (Cart m))(b:Deal): ((repeat1 x L b).map (story S W A B)).sum= crate S W A B (x,b)*(L.map (story S W A B)).sum:=by induction L with | nil=> simp [repeat1]| cons i L ih=> change story S W A B ((x,b)::i)+ _ = _; rw [List.map_cons,List.sum_cons,mul_add,←ih]; rfl
omit [Fintype m] in
lemma playwright (L:List m): ((script L).map (story S W A B)).sum=(L.map (fun x=> A x+B x)).prod:=by
 induction L with
 | nil=>simp [script,story] -- tune
 | cons x L ih=> rw [List.map_cons,List.prod_cons,←ih,← Deal.total S W _ _ x]; simp only [script,List.map_append,List.sum_append,rp_sum,add_mul,crate]
variable {S W A B} {j k:ℕ} {e a z:ℝ}
variable (p:∀ x,Sector (variety S x) false (A x))
variable (y:0 ≤ e) (v:1 ≤ a)
-- bound expanded costs
structure Pot (W:Finset n)(A B:m→FC n)(e a:ℝ)(j:ℕ) : Prop where
 small :∀ x, ‖A x W W‖≤ e
 localK :∀ x, ‖A x‖≤e*a
 far :∀ x, ‖B x‖≤e/a^j
include p
omit [Fintype m] in
private lemma eval_b (x:m)(D:Deal) (h:Pot W A B e a j) : ‖Deal.eval S W (A x) (B x) x D‖ ≤ e*a^(if D.costs then (1:ℕ) else 0)/a^(Deal.charge j D) := by
 have hp: ‖fixed S W x‖ ≤ 1:= (cutM_idp _).norm_le _
 have he: ‖1-fixed S W x‖ ≤ 1:= (cutM_idp _).one_sub.norm_le _
 cases D with
 | zero=> simp only [Deal.eval,Deal.costs,Bool.false_eq_true,ite_false,pow_zero,Deal.charge,mul_one,div_one]; rw [fix_middle S (p x),norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans (h.small x)
 | error=> simpa [Deal.eval,Deal.costs,Deal.charge] using h.far x
 | left=> simp only [Deal.eval,Deal.costs,ite_true,pow_one,pow_zero,Deal.charge,div_one]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) he).trans (h.localK x))
 | right=> simp only [Deal.eval,Deal.costs,ite_true,pow_one,pow_zero,Deal.charge,div_one]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) he).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hp).trans (h.localK x)))) -- tune include p
include v y
omit [Fintype m] in
lemma story_norm (L:Cart m)(h:Pot W A B e a j): ‖story S W A B L‖≤ e^L.length*(a^(live L).length/a^(xp L j)):=by
 have hp:0<a:=zero_lt_one.trans_le v
 induction L with
 | nil=> simp [story,xp,live]
 | cons t L ih=>
   rw [story,List.map_cons,List.prod_cons]; refine (norm_mul_le ..).trans ((mul_le_mul (eval_b (S:=S) p t.1 t.2 h) ih (norm_nonneg _) (by positivity)).trans_eq ?_); cases ht:t.2.costs <;> simp [live,xp,ht,pow_add,pow_succ'] <;> ring
variable {Z:FC n}

private lemma one_story (L:Cart m)(h:Pot W A B e a j)(u:∀ x,ChangeBill S j (B x))(k':ChangeBill S k Z)(w:‖Z‖≤z)(g:(L.map Prod.fst).Nodup) : ‖(story S W A B L*Z) W W‖ ≤ e^L.length*a^k*z:=by
 have hp:0<a:=zero_lt_one.trans_le v
 have hv:0 ≤ z:=(norm_nonneg Z).trans w
 by_cases U: (story S W A B L*Z) W W=0; · rw [U,norm_zero]; positivity
 apply (norm_entry ..).trans; apply (norm_mul_le ..).trans; refine mul_le_mul (le_trans (story_norm p y v L h) (mul_le_mul_of_nonneg_left ?_ (by positivity))) w (norm_nonneg _) (by positivity)
 rw [div_le_iff₀ (pow_pos hp _),←pow_add] -- tune
 exact pow_le_pow_right₀ v ((frequencies p u k' L g U).trans_eq (add_comm ..))
omit [Fintype m] p y v in
private lemma pay_script (L:List (Cart m)) (d:ℝ) (u:∀ i∈L, ‖(story S W A B i*Z) W W‖≤ d): ‖((L.map (story S W A B)).sum*Z) W W‖≤ L.length*d:=by
 induction L with
 | nil=> simp
 | cons i L ih=> rw [List.map_cons,List.sum_cons,add_mul,Matrix.add_apply]; apply (norm_add_le ..).trans; exact (add_le_add (u _ List.mem_cons_self) (ih (fun i h=> u i (List.mem_cons_of_mem _ h)))).trans_eq (by rw [List.length_cons]; push_cast; ring)
lemma royalties (L:List m) (l:L.Nodup)(h:Pot W A B e a j)(u:∀ x,ChangeBill S j (B x))(k':ChangeBill S k Z)(w:‖Z‖≤z) : ‖((L.map (fun x=> A x+B x)).prod*Z) W W‖ ≤ (4*e)^L.length*a^k*z:=by
 rw [← playwright S W]; refine (pay_script (L:=script L) (e^L.length*a^k*z) ?_).trans_eq (?_)
 -- tune
 swap; · rw [script_length,mul_pow]; push_cast; ring
 intro i h'; have hp := script_law L i h'; have hx: i.length=L.length:=by rw [←hp,List.length_map]
 rw [←hx]; exact one_story p y v i h u k' w (by rw [hp]; exact l)
#print axioms royalties
end YM.CF.Buffered.Cache
