import YM.CF.Arena.Stitch
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open Jet Rel Stationary Push.Loops
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
variable {c f:Side}{S: RG.StepData c f}{p k:ℕ}
section chain
variable(α:Type)[Fintype α][DecidableEq α]
/-- one finite choice per side, can symmetrize additive adjustments AFTER. -/
lemma isthmus {M:Type}[AddCommGroup M](D:Finset α):∃ a:α→Finset α,∀ g: Finset α→M, (∑ i∈D,(g (insert i (a i))-g (a i)))=g D-g ∅:=by
 induction D using Finset.induction_on with
 | empty=> exact ⟨fun _=>∅,fun _=>by simp⟩
 | insert i s h ih=> obtain ⟨a,ha⟩:= ih
                     let P:=Function.update a i s; refine ⟨P,fun g=>?_⟩; rw [Finset.sum_insert h,show P i=s from Function.update_self ..,show (∑ x∈s,_)=(∑ x∈s,(g (insert x (a x))-g (a x))) from Finset.sum_congr rfl fun x p=>by rw [show P x=a x from Function.update_of_ne (show x ≠ i from fun k=>h (k ▸ p)) _ _], ha]; abel
end chain
section increments
variable(F:Tab S→FileM c G)(V P:Tab S)(D: Site c→Support c)
def twitch(p: Site c)(y:Site c): SpaceX G c:= F (unite S (insert p (D p)) V P) y-F (unite S (D p) V P) y
def imp(r:ℕ)(p:Site c): SpaceX G c:= ∑ j∈pavilion r p, twitch F V P D p j
variable {R:ℕ}(h: ∀ A B:Tab S,∀ k,Kind S A B (pavilion R k)→ F A k= F B k)
include h
lemma twitch_z (p y:Site c)(hp:y∉pavilion R p):twitch F V P D p y=0:=by
 unfold twitch; refine sub_eq_zero.mpr (h _ _ _ (sprayT fun i hi=>?_)); rw [mem_insert]; apply or_iff_right; intro t; rw [t] at hi; apply hp; exact (theatre ..).mpr ((separation_comm ..).trans_le ((theatre ..).mp hi))
lemma impU(i:Site c): imp F V P D R i= ∑ j:Site c,twitch F V P D i j:=Finset.sum_subset (subset_univ _) (fun _ _ p=> twitch_z _ _ _ _ h _ _ p)
lemma stitch_u(i:Site c)(V':Tab S)(p:Kind S V V' (pavilion (R+R) i)): imp F V P D R i=imp F V' P D R i:=by
 refine sum_congr rfl fun j hj=> ?_; have hp:pavilion R j ⊆ pavilion (R+R) i:=Forge.aroundBk _ (show Forge.Beat.shadows (o:=i) (pavilion (R+R) i) _ from Subset.refl _) (Nat.add_le_add_right ((theatre ..).mp hj) R)
 have hp':Kind S V V' (pavilion R j):=⟨fun i t=>p.up _ (hp t),fun i t=>p.ht _ (hp t),fun i t=>p.site _ (hp t),fun i t=>p.edge _ (hp t)⟩
 unfold twitch; rw [h (unite S _ V P) (unite S _ V' P) j (differT hp' P),h (unite S _ V P) (unite S _ V' P) j (differT hp' P)] -- tune metavars a
lemma merge_v(i:Site c)(ht:0<σ)(hp:k≤ m)(hx:∀ v:Tab S,∀ p:Site c,CakeF (F v p) p R m σ A ∧ cFoot k (satX (F v p)))(hQ:∀ v:Tab S, Prox (F v) l C)(hu:l ≤ m)(hg:0≤ C): let X:=imp F V P D R i
 CakeF X i (R+R) m σ (plot R*(A+A)) ∧ cFoot k (satX X) ∧ ‖cake l (satX X)‖ ≤ (plot (R+R)*Fintype.card (TypeFace 1× G.ColorIndex):ℕ)^l*(C+C):=by
 intro X; let Q:=unite S (D i) V P; let M:= unite S (insert i (D i)) V P; let p:= plot R; let v:= pavilion R i; have hσ: ‖(0:InputZ G c)‖<σ:=by rw [norm_zero]; exact ht
 have hX(j)(hp:j∈v): CakeF (twitch F V P D i j) i (R+R) m σ (A+A):= ((((hx M j).1.less (hx Q j).1).widen i).under le_rfl (Nat.add_le_add_right ((theatre _ _).mp hp) _) le_rfl)
 have he(t:Tab S): ContDiffAt ℝ (l:ℕ∞ω) (satX (∑ j,F t j)) 0:=by simp_rw [satX,Function.comp_def,Finset.sum_apply]; exact ContDiffAt.sum fun i _=> ((hx t i).1.ledger 0 hσ).smooth.of_le (by exact_mod_cast hu)
 have hK: CakeF X i (R+R) m σ (p*(A+A)):= by apply ((CakeF.sigmaH v hX).under le_rfl le_rfl); rw [sum_const,nsmul_eq_mul]; have ha:= ((hx V i).1.ledger _ hσ).nonneg; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (pay_v _)) (add_nonneg ha ha)
 have hz:X=(∑ j,F M j) - ∑ j,F Q j:=by unfold X; rw [impU F V P D h]; unfold twitch; rw [Finset.sum_sub_distrib]
 have hx':ContDiffAt ℝ (l:ℕ∞ω) (satX X) 0 := ((hK.ledger _ hσ).order hu).smooth
 refine ⟨hK,fun u t=>?_ ,basisK hK.toAtom hx' (add_nonneg hg hg) ?_⟩
 · have he (X:Tab S)(j:Site c): ContDiffAt ℝ (u:ℕ∞ω) (satX (F X j)) 0:= ((hx X j).1.ledger _ hσ).smooth.of_le (by exact_mod_cast t.le.trans hp)
   have hh(X:Tab S):satX (∑ j,F X j)= ∑ j,satX (F X j):=funext fun y=>by simp only [satX,Finset.sum_apply,Function.comp_apply]
   rw [hz,show satX ((∑ j,F M j)-∑ j,F Q j)=satX (∑ j,F M j)-satX (∑ j,F Q j) from rfl]; simp_rw [hh]; have h(t:Tab S):ContDiffAt ℝ (u:ℕ∞ω) (∑ j,satX (F t j)) 0:=by rw [← hh]; simp_rw [satX,Function.comp_def,Finset.sum_apply]; exact ContDiffAt.sum fun j _=> he t j
   rw [iteratedFDeriv_sub_apply (h M) (h Q),iteratedFDeriv_sum_apply (fun i _=> he M i),iteratedFDeriv_sum_apply (fun i _=>he Q i)]; simp_rw [fun (K:Tab S) i => (hx K i).2 u t]; simp
 intro u; let v(j):=flaw G (u j).1 (u j).2; have hw: cake l (satX X) v=cake l (satX (∑ i,F M i)) v - cake l (satX (∑ i,F Q i)) v:=by rw [hz]; unfold cake; rw [show satX ((∑ i,F M i)-∑ i,F Q i)=satX (∑ i,F M i)-satX (∑ i,F Q i) from rfl,iteratedFDeriv_sub_apply (he M) (he Q),smul_sub,_root_.sub_apply]
 rw [hw]; apply (norm_sub_le ..).trans; have hp(t:Tab S): ‖cake l (satX (∑ i,F t i)) v‖≤ C:=by rw [←sumF (F t) l _ (fun j=>((hx t j).1.ledger _ hσ).smooth.of_le (by exact_mod_cast hu))]; exact hQ t (fun i=>(u i).1) (fun i=>(u i).2)
 exact add_le_add (hp _) (hp _)
end increments
end YM.CF.Arena
