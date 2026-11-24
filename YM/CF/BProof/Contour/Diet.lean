import YM.CF.BProof.Contour.Recipe

/- lem:B-contour abstract integration, finish tally. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour
open Function Filter Moment RG MeasureTheory Finset Relation Push.AbsoluteSums
open scoped Topology BigOperators Classical ENNReal
variable {B I J E: Type*}{X:B→Type*} [Fintype B][DecidableEq B][∀ i,MeasurableSpace (X i)]
variable [Fintype I][DecidableEq I][Fintype J][DecidableEq J][∀ i,Nonempty (X i)] {K:GeomT B I}
variable (P:Pot X) (C:Course P K)(R:Spice X K J)
variable (u:I→ℝ)
structure Diet : Prop where
  small : Toll R.t R.w 4 (1/8)
  minor : ∀ i, (∫ x,‖C.G i x‖ ∂πμ X P.μ P.ν (K.S i))≤ u i
  minorT : Toll K.T u 4 (1/4)
variable {A:Type*}[MeasurableSpace A]
lemma env_mul(f g:A→ℂ)(p:Envelope f)(q:Envelope g): Envelope (fun x=>f x*g x):=by
 obtain ⟨t,l⟩:=p.cost; obtain ⟨u,v⟩:= q.cost; refine ⟨p.meas.mul q.meas,t*u,fun x=>?_⟩; rw [norm_mul]; exact mul_le_mul (l x) (v x) (norm_nonneg _) ((norm_nonneg _).trans (l x))
lemma env_prod{f:I→A→ℂ}(V:Finset I)(p:∀ i,Envelope (f i)): Envelope (fun x=> ∏ i∈ V,f i x):=by induction V using Finset.induction_on with|empty=> simp_rw [prod_empty]; exact ⟨measurable_const,‖(1:ℂ)‖,fun _=> le_rfl⟩|insert i s l ih=> simp_rw [prod_insert l]; exact env_mul _ _ (p _) ih
variable (D:Diet P C R u)
abbrev w(j:J):=2* R.w j
lemma pack_cap (h:Toll R.t R.w 4 (1/8))(i:J): R.w i ≤ 1:=by
 obtain ⟨x,p⟩:= R.pos i; refine le_trans ?_ (le_trans (show hit R.t R.w 4 x i ≤ 1/8 from by simpa only [sum_singleton] using budget_sum (h.pays x) {i}) (by norm_num)); unfold hit; rw [if_pos p]; exact le_mul_of_one_le_left (h.nonneg i) (Real.one_le_exp (by positivity)) -- tune
lemma easePay (h:Toll R.t R.w 4 (1/8))(i:J)(Q:Finset I)(p:flock K.T Q)(x:∀ i,X i): ‖ease R Q i x‖≤ w R i:=by
 have hh:= R.pay i Q p x; exact (Complex.norm_exp_sub_one_le (hh.trans (pack_cap R h i))).trans (mul_le_mul_of_nonneg_left hh (by norm_num))
lemma env_f (h:Toll R.t R.w 4 (1/8))(Q:Finset I)(U:Finset J)(p:flock K.T Q): Envelope (focus P C R Q U):= env_mul _ _ (env_prod Q C.bound) (env_prod U (fun i=>⟨(Complex.continuous_exp.measurable.comp (R.bill i Q p)).sub measurable_const,_,easePay R h i Q p⟩))
lemma many (h:Toll R.t R.w 4 (1/8))(Q:Finset I)(p:flock K.T Q): (∫ x,tunic P C R Q x ∂food P K Q)=∑ U:Finset J,work P C R Q U:=by
 have he := Complex.exp_sum (f:=fun j:ℂ=>j); unfold work; simp_rw [if_pos p]; rw [← integral_finsetSum]; swap; · exact fun i hi=> Law.pay (env_f P C R h Q i p)
 apply integral_congr_ae; refine Eventually.of_forall fun x=>?_; unfold tunic; rw [Complex.exp_sum]; unfold focus; simp only; rw [← mul_sum]; congr 1; let f:= fun i=>ease R Q i x; have hv(i:J): Complex.exp (R.A i Q x)=1+f i:= by unfold f ease; ring
 simp_rw [hv,prod_one_add]; -- tune Fintype prod_one_add over powerset
 simp only [powerset_univ]; rfl
lemma fare (h:Toll R.t R.w 4 (1/8)): contour P C R=∑ i:Finset (I⊕ J),dish P C R i:=by
 let e:(Finset I×Finset J)≃Finset (I⊕ J):=(Finset.sumEquiv).symm.toEquiv; rw [←Equiv.sum_comp e (dish P C R),Fintype.sum_prod_type,contour, sum_filter]; apply sum_congr rfl; intro i _; unfold dish; simp_rw [show ∀ (j:Finset J),e (i,j)=Finset.disjSum i j from fun _=>rfl,toLeft_disjSum,toRight_disjSum]; split; exact many P C R h i (by assumption)
 rename_i t; simp [work,t]
include D
lemma meal (Q:Finset I)(p:flock K.T Q): (∫ x,‖eye P C Q x‖ ∂food P K Q)≤ wage u Q:=by
 have hx(A:Finset I): reads X (fun x=> ‖eye P C A x‖) (hull K.T A):=fun x y p=>congrArg norm (prod_congr rfl fun i h=> C.obey i x y fun j g=>p j (hull_sub K.T _ i h g))
 induction Q using Finset.induction_on with
 | empty=> unfold food; simp [wage,hull,eye]
 | insert i Q l ih=>
    obtain ⟨b,t⟩:= (shrinkF K.T i l).1 p; have he: (fun x=>‖eye P C (insert i Q) x‖)=(fun x=>‖C.G i x‖*‖eye P C Q x‖):=funext fun x=>by unfold eye; rw [prod_insert l,norm_mul]
    unfold food; rw [he,hull,biUnion_insert,portion X P.μ P.ν (fun x=>‖C.G i x‖) (fun x=>‖eye P C Q x‖) (K.T i) (hull K.T Q) _ _ (K.sub i) (biUnion_mono (fun i _=> K.sub i)) (reads_comp X _ norm _ (C.obey i)) (hx Q) b, wage,prod_insert l]; exact mul_le_mul (D.minor i) (ih t) (integral_nonneg fun _=>norm_nonneg _) (D.minorT.nonneg i) -- tune hull
private lemma double_pos (i:J):0≤w R i:=mul_nonneg (by norm_num) (D.small.nonneg i)
lemma work_cost (Q:Finset I)(U:Finset J) : ‖work P C R Q U‖≤ wage u Q * wage (w R) U:=by
 have hv:0≤wage (w R) U:=wage_pos _ (double_pos P C R u D) _; unfold work; split; next H=>
    let f(x):= focus P C R Q U x; have hf(x): ‖f x‖≤ ‖eye P C Q x‖ * wage (w R) U :=by unfold f focus wage; rw [norm_mul,norm_prod]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> easePay R D.small i Q H x)
    apply (norm_integral_le_integral_norm _).trans; apply le_trans (integral_mono (Law.pay (env_f P C R D.small Q U H)).norm ((Law.pay (env_prod Q C.bound)).norm.mul_const (wage (w R) U)) hf); rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right (meal P C R u D Q H) hv -- tune
 next H=> rw [norm_zero]; exact mul_nonneg (wage_pos u D.minorT.nonneg _) hv
theorem diner : Real.exp (-(Fintype.card B:ℝ)) ≤ ‖contour P C R‖:=by
 let v:= Sum.elim u (w R); rw [fare P C R D.small]; apply linked (vision R) _ _ (yarnD P C R) v; swap; · intro i; apply (work_cost P C R u D i.toLeft i.toRight).trans_eq; unfold wage; exact (prod_sum_eq_prod_toLeft_mul_prod_toRight i v).symm -- tune
 swap; · intro i; cases i; exact (K.pos _).mono (K.sub _); exact R.pos _
 have he := Moment.Toll.sum _ _ D.minorT _ _ (Moment.Toll.scale _ _ D.small 2 (by norm_num)); convert he using 1 <;> first | rfl | norm_num
end YM.CF.BProof.Contour
