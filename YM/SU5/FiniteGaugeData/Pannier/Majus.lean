import YM.CF.Fixed.Extensive
import YM.CF.Gall.Penn
/-!
# Letter costs with **normalized arbitrary vectors**, on finite lattice. Here just a device for pointwise pre-integral estimates. Develop the `Pays` argument from `YM.CF.Gall.Penn` in this language because don't need column costs on projector/lifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pannier.Damask
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{P Q R K:Op n}{p q f:Wave n}{k v C d b w:ℝ}{A B:FC n}
abbrev Token(n:Type*)[LinearOrder n][Fintype n]:= {x: Bool × Ket n // ‖creed x.1 x.2‖ ≤ 1}
def use (x:Token n) := creed x.val.1 x.val.2
def costs(k:ℝ)(u:List (Token n)):= k^u.length
def Yep (k:ℝ)(p:Wave n)(q:Wave n)(d:ℝ):Prop:=∀ u:List (Token n),‖inner ℂ p (acts (rollC use u) q)‖ ≤ d*costs k u
def Pays (k:ℝ)(A:FC n)(d:ℝ):Prop:= 0 ≤ d ∧ ∀ p q:Wave n,∀ w:ℝ,0 ≤ w→Yep k p q w→Yep k p (acts A q) (d*w)
lemma size_q (p:0 ≤k)(u:List (Token n)): 0 ≤ costs k u:=pow_nonneg p _
lemma Yep.weigh (p:Yep k f q b)(t:b≤d)(h:0≤k):Yep k f q d:=fun i=>(p i).trans (mul_le_mul_of_nonneg_right t (size_q h i))
lemma Pays.weigh (p:Pays k A b)(t:b≤d)(h:0≤k):Pays k A d:=⟨p.1.trans t,fun i j w v g=>(p.2 _ _ w v g).weigh (mul_le_mul_of_nonneg_right t v) h⟩
lemma Yep.join (h:Yep k f q d)(g:Yep k f p v): Yep k f (q+p) (d+v):=by intro i; rw [map_add,inner_add_right, add_mul]; exact (norm_add_le ..).trans (add_le_add (h _) (g _))
namespace Pays
lemma add (p:Pays k A d)(q:Pays k B v):Pays k (A+B) (d+v):=by refine ⟨add_nonneg p.1 q.1, fun i j w h u=>?_⟩; rw [act_add,add_mul]; exact (p.2 i j w h u).join (q.2 i j w h u)
lemma linear(p:Pays k A d)(c:ℂ): Pays k (c • A) (‖c‖*d):=by
 refine ⟨mul_nonneg (norm_nonneg _) p.1,fun i j w h u z=>?_⟩; rw [act_smul,map_smul,inner_smul_right, norm_mul]; exact (mul_le_mul_of_nonneg_left (p.2 i j w h u z) (norm_nonneg c)).trans_eq (by ring)
lemma mul (p:Pays k A d)(q:Pays k B v):Pays k (A*B) (d*v):=⟨mul_nonneg p.1 q.1,fun i j w e g=>by rw [act_mul,mul_assoc]; exact p.2 _ _ _ (mul_nonneg q.1 e) (q.2 _ _ _ e g)⟩
lemma uno:Pays k (1:FC n) 1:=⟨zero_le_one,fun i j w e h=>by rw [act_one,one_mul]; exact h⟩
lemma tone(u:Token n)(p:0 ≤k):Pays k (use u) k:=by
 refine ⟨p,fun i j w t H L=>?_⟩; rw [← act_mul,show rollC use L*use u=rollC use (L++[u]) by simp [rollC]]; refine (H (L++[u])).trans_eq ?_ -- tune lhs convert
 unfold costs; simp [pow_succ]; ring
lemma power(p:Pays k A d)(i:ℕ):Pays k (A^i) (d^i):=by induction i with| zero=>rw [pow_zero,pow_zero]; exact uno| succ i ih=>rw [pow_succ,pow_succ]; exact ih.mul p
lemma nil:Pays k (0:FC n) 0:=⟨le_rfl, fun p q a e g v=>by simp⟩
lemma sumT{I:Type*}(S:Finset I)(A:I→ FC n)(k:I→ℝ)(p:∀ i∈S,Pays b (A i) (k i)):Pays b (∑ i∈S,A i) (∑ i∈S,k i):=by
 classical
 induction S using Finset.induction_on with| empty=>rw [sum_empty,sum_empty]; exact nil| @insert i S e ih=>rw [sum_insert e,sum_insert e]; exact (p i (mem_insert_self ..)).add (ih fun i x=>p i (mem_insert_of_mem x))
lemma exp_sub (p:Pays k A C):Pays k (exp A-1) (Real.exp C-1):=by
 let V(n':ℕ):=(n'.factorial:ℂ)⁻¹ • A^n'; let S(n':ℕ):=(n'.factorial:ℝ)⁻¹*C^n'
 have hv := show Summable V from (norm_expSeries_summable' (𝕂:=ℂ) A).of_norm; have h:= (norm_expSeries_summable' (𝕂:=ℝ) C).of_norm; have H : Summable S:= h
 have hp:=p.1; have ht:HasSum (fun n:ℕ=>V (n+1)) (exp A-1):=by
    rw [congrFun (exp_eq_tsum ℂ),← hv.sum_add_tsum_nat_add 1]; simpa [V,sum_range_one] using ((summable_nat_add_iff 1).mpr hv).hasSum -- tune
 have hS: HasSum (fun n:ℕ=> S (n+1)) (Real.exp C-1):=by
    rw [Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]; change HasSum _ ( (∑' i,S i)-1); rw [← H.sum_add_tsum_nat_add 1]; simpa [S] using ((summable_nat_add_iff 1).mpr H).hasSum
 refine ⟨sub_nonneg.mpr (Real.one_le_exp hp),fun i j w p' g u=> ?_⟩
 let W(X:FC n):=‖inner ℂ i (acts (rollC use u) (acts X j))‖
 have hu:Continuous W:=(continuous_const.inner (ContinuousLinearMap.continuous (acts (rollC use u))|>.comp (acts_cont.clm_apply continuous_const))).norm
 refine le_of_tendsto_of_tendsto (hu.continuousAt.tendsto.comp (ht.tendsto_sum_nat)) ((hS.tendsto_sum_nat.mul_const w).mul_const (costs k u)) (Eventually.of_forall fun l:ℕ=> ((sumT _ _ (fun n=> S (n+1)) (fun i _=>?_)).2 _ _ w p' g u)) -- tune inference
 unfold S; have he:‖(((i+1).factorial:ℂ))⁻¹‖=((i+1).factorial:ℝ)⁻¹:=by simp; -- scope
 exact he ▸ ((p.power _).linear _)
lemma expo (p:Pays k A d) :Pays k (exp A) (Real.exp d):=by have hp:= p.exp_sub.add uno; rw [sub_add_cancel,sub_add_cancel] at hp; exact hp
lemma northern (p:Pays k A d): Pays k (-A) d:=by simpa only [norm_neg,norm_one,one_mul,neg_one_smul] using p.linear (-1)
lemma letter (p:0≤k)(v:‖A‖≤1) (x: ∃ (b:Bool)(y:Ket n),A=creed b y): Pays k A k:=by obtain ⟨b,y,rfl⟩:=x; exact tone ⟨(b,y),v⟩ p
open Fixed.Extensive
lemma dG (h:0≤k)(C P Q:Op n)(p:‖P‖≤1)(q:‖Q‖≤1): Pays k (dg (P*C*Q)) (absEntries C*k^2) := by
  let c:=basisKet (n:=n)
  have ht(A:Op n)(p:‖A‖≤1)(i): ‖acts A (c i)‖≤1:=(ContinuousLinearMap.le_opNorm ..).trans (by unfold acts; rw [Matrix.l2_opNorm_toEuclideanCLM,show ‖c i‖=(1:ℝ) by simp [c,basisKet],mul_one]; exact p)
  have he:= dyad_prong C P (cc (star Q)) put takeF; simp_rw [ccT,star_star] at he; change Pays k (dyad _ _ _) _; rw [← he]; unfold absEntries dyad
  simp_rw [sum_mul,prong_p,prong_t]; apply sumT; intro i hi; apply sumT; intro j hj
  apply Pays.linear (_ : Pays k _ (k^2)); rw [sq]
  have hp: ‖create (acts P (c i))‖≤1:= (Flare.cost_pe false (acts P (c i))).trans (ht P p i)
  have hq: ‖remove (acts (star Q) (c j))‖≤1:= (Flare.cost_pe true _).trans (ht (star Q) (by rwa [norm_star]) j)
  exact (letter h hp ⟨false,_,rfl⟩).mul (letter h hq ⟨true,_,rfl⟩)
lemma twist_c (h:0≤k)(U:UNI n)(C P Q:Op n)(p:‖P‖≤1)(q:‖Q‖≤1): Pays k (dg (P*(twist U C)*Q)) (absEntries C*k^2) := by
  rw [twist_formula]; simp only [←mul_assoc]; rw [mul_assoc _ (star _) Q]; apply dG h
  · exact (CStarRing.norm_mul_coe_unitary _ U).trans_le p
  exact (CStarRing.norm_coe_unitary_mul (star U) _).trans_le q
lemma jazzG (h:0≤k)(U:UNI n)(b:Bool)(C P Q:Op n)(p:‖P‖≤1)(q:‖Q‖≤1): Pays k (dg (P*Thera.jazz b (twist U C)*Q)) (absEntries C*k^2) := by
  unfold Thera.jazz; split; swap; · exact twist_c h U C P Q p q
  rw [mul_neg,neg_mul,←map_star (twist U),dg_neg,← entries_star C]
  exact (twist_c h U (star C) P Q p q).northern
lemma roll (h:0≤k) {ι:Type*}(F:ι → FC n)(u:List ι)(d:ℝ)(t:∀ i, Pays k (F i) d):Pays k ((u.map F).prod) (d^u.length):=by
 induction u with| nil=> simp only [List.map_nil,List.prod_nil,List.length_nil,pow_zero]; exact uno| cons i l ih=> rw [List.map_cons,List.prod_cons,List.length_cons,pow_succ']; exact (t i).mul ih
open Graph Pastry Fock Branch Scree
lemma sorted {ι:Type*} [LinearOrder ι] [Fintype ι](p:0≤k)(F:ι→FC n)(h:∀ i,Pays k (F i) d)(l:Finset ι): Pays k (Scree.column F l) (d^l.card):=by have ht:= roll p _ (l.sort (·≤·)) _ h; rw [length_sort] at ht; exact ht
lemma frameG (p:0≤k)(P:Op n)(S:ribbon n)(h:∀ i:LeanV n,Pays k (drawT P i) d): Pays k (tank P S) (tier d S.val):=by
 refine sumT _ _ _ fun i _=> ?_
 rw [mul_comm (d^_)]
 apply Pays.linear (A:=Scree.column _ _)
 exact sorted p _ h _
lemma boardH (N:Side)(R:GramM N)(X:Skye.Orbit N) (v u c d l:ℝ)(p:Graph.Ledger l v u d c R)(A:Op (Single N))(a:IsStarProjection A) (Z:0≤k)(w:k≤l): Pays k (tank A (R.board X)) (Real.exp ((v+v+u)*(Cube.More N).val^4)):=by
 have H(i):Pays k (drawT A i) l:=by
    apply (Pays.letter Z (Graph.vital A a i) ?_).weigh w Z
    unfold drawT; split
    · rw [seekF,prong_p]; exact ⟨false,_,rfl⟩
    rw [hideF,prong_t]; exact ⟨true,_,rfl⟩
 rw [GramM.board,Graph.shape _ _ _ a,add_mul,Real.exp_add]
 exact (((frameG Z A _ H).weigh (Graph.marks R X p.reg p.slip (Z.trans w)) Z).expo).mul ((frameG Z A _ H).weigh (Graph.toeF p.force (Z.trans w) X) Z)
end Pays
lemma Yep.pos0 (h:Yep k p f d):0≤d:= (norm_nonneg (inner ℂ p f)).trans (by simpa [rollC,costs] using h [])
lemma Yep.val (h:Yep k p f d):‖inner ℂ p f‖ ≤ d:= by simpa [rollC,costs] using h []
end YM.CF.Pannier.Damask
#print axioms YM.CF.Pannier.Damask.Pays.frameG
#print axioms YM.CF.Pannier.Damask.Pays.jazzG
