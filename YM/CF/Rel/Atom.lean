import YM.CF.Rel.Vail
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
-- cylinder budget used for producing accounting identities and qualities (analytic on plain represent near origin)
variable {x:Site n}{g f:SpaceX G n}{W:KitM G n m}{R:ℕ}
structure CakeF (f:SpaceX G n) (x:Site n)(M m:ℕ)(ε A:ℝ):Prop extends Atom f x M where
 ledger(z:InputZ G n):‖z‖<ε→Jet.Allows m (satX f) z A
namespace CakeF
variable (h:CakeF f x R m σ A)
include h
lemma under{σ':ℝ}(hp:σ'≤σ)(hl:R ≤ l)(t:A≤ C):CakeF f x l m σ' C:= -- σ'
 ⟨⟨h.fixed,fun i j hj=> h.reads i j fun d hd=> hj d (hd.trans hl)⟩,fun i hi=> (h.ledger i (hi.trans_le hp)).mono t⟩
lemma add(hp:CakeF g x R m σ C): CakeF (f+g) x R m σ (A+C):= ⟨⟨fun u v=>congr_arg₂ (·+·) (h.fixed u v) (hp.fixed u v),fun u v he=>congr_arg₂ (·+·) (h.reads u v he) (hp.reads u v he)⟩,fun i hi=>(h.ledger i hi).add (hp.ledger i hi)⟩
lemma pay(z:ℂ):CakeF (z • f) x R m σ (‖z‖*A):=by
 let L:= (ContinuousLinearMap.lsmul ℝ ℂ z: ℂ→L[ℝ]ℂ); have he:‖L‖ ≤ ‖z‖:=ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun i=> (norm_mul ..).le
 refine ⟨⟨fun u v=>congr_arg L (h.fixed u v),fun u v p=>congr_arg L (h.reads u v p)⟩,fun i hi=>(h.ledger i hi).linear L he⟩
lemma less(hp:CakeF g x R m σ C):CakeF (f-g) x R m σ (A+C):=by simpa only [neg_one_smul,norm_neg,norm_one,one_mul,← sub_eq_add_neg] using h.add (hp.pay (-1))
lemma rotate(y: Site n): CakeF (f ∘ Lattice.translate y) (x+y) R m σ A:=by
 constructor
 · refine ⟨fun i u=> ?_,fun i j he=> h.reads _ _ ?_⟩
   · change f (Lattice.translate _ _)=f _; rw [show Lattice.translate y (Lattice.gauge u i)= Lattice.gauge (fun p=> u (p+y)) (Lattice.translate y i) from ?_,h.fixed]; ext1 p; unfold Lattice.gauge Lattice.translate; dsimp only; rw [add_right_comm]
   intro p hp; exact he (p.1+y,p.2) (by rw [separation_translate]; exact hp)
 intro z he
 let L:=tagT G y; have hL : ‖L‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z=> by rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>norm_le_pi_norm z _
 have ht:‖L z‖ < σ:= lt_of_le_of_lt ((L.le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg _) hL)) he
 have hs:satX (f∘ Lattice.translate y)=satX f ∘ L:=by ext1; simp only [satX,Function.comp_apply,← trn]; rfl
 have hv:=h.ledger (L z) ht; rw [hs]; refine ⟨hv.smooth.comp _ L.contDiff.contDiffAt,fun i hi=>?_⟩
 rw [Push.Uniform.iter_lin_at (hv.smooth.of_le (Nat.cast_le.mpr hi))]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; simp only [Finset.prod_const,card_univ,Fintype.card_fin]; exact ((mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)).trans (hv.norm_le _ hi))
lemma widen(y:Site n): CakeF f y (separation y x+R) m σ A:= ⟨⟨h.fixed,fun i j he=> h.reads i j fun d hd=> he d ((separation_triangle y x d.1).trans (Nat.add_le_add_left hd _))⟩,h.ledger⟩
omit h in
lemma zeroP (he:0≤ A): CakeF (0:SpaceX G n) x R m σ A:= ⟨⟨fun _ _=> rfl,fun _ _ _=> rfl⟩,fun i _=>Jet.allows_const _ ((norm_zero).le.trans he)⟩
omit h in
lemma sigmaH {ι:Type}(s:Finset ι){P:ι→SpaceX G n}{a:ι→ℝ}(he:∀ i∈s,CakeF (P i) x R m σ (a i)):CakeF (∑ i∈s,P i) x R m σ (∑ i∈s,a i):=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact zeroP le_rfl
 | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (he _ (by simp)).add (ih fun i h=> he i (by simp [h]))
end CakeF
end YM.CF.Rel
