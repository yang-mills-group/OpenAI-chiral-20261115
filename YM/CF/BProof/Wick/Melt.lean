import YM.CF.BProof.Wick.Dyke
import YM.CF.BProof.Align.Board

/-! Diagonal scaling identity & limit at projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Thera Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]{p q:Finset I}{x: Wave I}
def offerP (p q:Finset I)(u:ℂ):= u⁻¹ • cutM p + u • cutM q + space (cutM p) (cutM q)
def grab (p q:Finset I)(u:ℂ) : FC I := Matrix.diagonal (fun s=>u^(p.card-(s∩p).card+(s∩q).card))
def permit (p q:Finset I): Finset (Finset I):= univ.filter (fun s=> p⊆s ∧ Disjoint q s)
def cabin (p q:Finset I):= cutM (permit p q)
lemma coals (p q:Finset I):Continuous (grab p q):=by apply continuous_matrix; intro i j; by_cases h:i=j <;> simp only [grab, Matrix.diagonal_apply,h,↓reduceIte] <;> fun_prop
@[simp] lemma permit_rule (p q s: Finset I): s∈permit p q ↔ p⊆s ∧ Disjoint q s:=by simp [permit]
lemma permit_spec (p q:Finset I): grab p q 0=cabin p q:=by
 unfold grab cabin cutM; apply congrArg; funext i; by_cases h:i∈permit p q
 · obtain ⟨x,y⟩:= (permit_rule ..).mp h; rw [if_pos h,inter_eq_right.mpr x, Nat.sub_self,disjoint_iff_inter_eq_empty.mp y.symm]; simp
 rw [if_neg h,zero_pow]; intro v; have hv:=Nat.add_eq_zero_iff.mp v; apply h; apply (permit_rule ..).mpr; refine ⟨?_, Disjoint.symm (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hv.2))⟩; exact (inter_eq_right.mp (eq_of_subset_of_card_le inter_subset_right (Nat.sub_eq_zero_iff_le.mp hv.1)))
lemma offer_spec (u:ℂ)(p q:Finset I)(h:Disjoint p q): offerP p q u=Matrix.diagonal (fun i=> if i∈p then u⁻¹ else if i∈q then u else 1):=by
 ext i j; by_cases g:i=j; subst j; by_cases g:i∈p; have ht:i∉q:= fun hq=>disjoint_left.mp h g hq; simp [grab,offerP,space,cutM,g,ht]; by_cases t:i∈q<;>simp [offerP,g,t,space,cutM]; simp [offerP,space,cutM,g]
lemma sellers (u:ℂ)(h:Disjoint p q)(X:Finset I): (∏ i∈X,(if i∈p then u⁻¹ else if i∈q then u else 1))= (u⁻¹)^(X∩p).card*u^(X∩q).card:=by
 induction X using Finset.induction_on with
 | empty=> simp
 | @insert i X e ih=>
   rw [prod_insert e,ih]; by_cases g:i∈p; have ht:i∉q:= fun x=> disjoint_left.mp h g x; simp [g,ht,e,pow_succ',mul_assoc]; by_cases ht:i∈q <;> simp [g,ht,e,pow_succ',mul_left_comm] -- tune
lemma contracts {u:ℂ}(h:u≠0)(H:Disjoint p q): u^p.card • quant (offerP p q u)=grab p q u:=by
 rw [offer_spec u p q H,quant_diag, grab,← Matrix.diagonal_smul]; apply congrArg; funext i; change u^p.card*_=_; dsimp only; rw [sellers u H i, ←mul_assoc, show u^p.card*u⁻¹^(i∩p).card=u^(p.card-(i∩p).card) from ?_, pow_add]; rw [inv_pow,← div_eq_mul_inv,div_eq_iff (pow_ne_zero _ h),←pow_add,Nat.sub_add_cancel (card_le_card inter_subset_right)]
lemma det_rank {P:Op I}{p: IsStarProjection P}(v:ℕ)(g:P.trace=(v:ℂ))(t:ℂ): (1+t • P).det=(1+t)^v:=by
 obtain ⟨U,s,hU⟩:= spot_projection P p; subst P; rw [trace_twist,trace_cut] at g; rw [← twist_scalar, ← (show twist U (1:Op I)=1 from map_one (twist U)),← map_add,det_twist]; have hp:s.card=v:= by exact_mod_cast g
 let F(i:I):= if i∈s then 1+t else 1
 rw [show 1+t • cutM s=Matrix.diagonal F from (by ext i j; by_cases h:i=j; subst j; by_cases h:i∈s <;> simp [h,F,cutM]; simp [h,F,cutM]), Matrix.det_diagonal, ← prod_subset (subset_univ s) (fun i _ g=> if_neg g), ← hp]; apply (prod_congr rfl fun i hi=> if_pos hi).trans (b:= ∏ i∈s,(1+t)); exact prod_const _
end YM.CF.BProof.Wick
