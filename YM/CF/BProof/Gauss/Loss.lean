import YM.CF.BProof.Gauss.Night

/- Jacobian cost split. Assign short pieces to individual severely priced columns with
compact neighborhoods and integrate into multiplier there; keep long pieces in weak book. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.Night.Design
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar Push.AbsoluteSums Prox Moment
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {A:Type}[Fintype A]{B: Prox.Base A}{d: Finset A→ℝ}{t C:ℝ}(D: Design B d t C)(S:Finset A)(k:ℕ)

def long (i: Finset A): ℝ := if k≤ i.card then D.slot i S else 0
def costs (i: Finset A) := if k≤ i.card then D.fare i else 0
-- deterministic on actual meet set (can assign first using a fixed order).
def first (t:Finset A) := (dite t.Nonempty (fun h=>some h.choose) (fun _=>none))
def issues (i: Finset A): Option A:= if i.card<k ∧ D.fare i≠0 then first (S∩i) else none
def short (i: A) := ∑ j with issues D S k j=some i,D.slot j S
lemma first_spec (r:Finset A)(i:A)(h:first r=some i): i∈r:= by unfold first at h; split at h; rename_i e;  rw [←Option.some.inj h]; exact e.choose_spec; contradiction
lemma episode {b:A}{i}(h:D.issues S k i= some b) : b∈ S ∧ b∈ i ∧ B.C i ∧ i.card < k := by
 unfold issues at h; split at h; swap; · contradiction
 rename_i e; obtain ⟨l,v⟩:= mem_inter.mp (first_spec _ _ h); exact ⟨l,v,(D.nont i e.2).1,e.1⟩
lemma site_line (i:Finset A): (∑ j∈S, if issues D S k i=some j then D.slot i S else 0)= if i.card<k then D.slot i S else 0:= by
 by_cases h: D.fare i=0; · have he:=D.bounds i S; rw [h,norm_le_zero_iff] at he; simp [he]
 split; next hl=>
   rcases (S∩i).eq_empty_or_nonempty with hv|hv; · have hp:Disjoint i S:= Disjoint.symm (disjoint_iff_inter_eq_empty.mpr hv); simp_rw [D.vacant i S hp, ite_self,sum_const_zero]
   have he:issues D S k i = some hv.choose:=by rw [issues,if_pos (And.intro hl h),first,dif_pos hv];
   simp_rw [he]; simp [Finset.sum_ite_irrel, (mem_inter.mp hv.choose_spec).1] -- tune
 next hl=> apply sum_eq_zero; intro j hj; apply if_neg; intro p; exact hl (D.episode S k p).2.2.2
lemma ledger : d S=(∑ i,D.long S k i)+∑ b∈ S,short D S k b:=by
 rw [D.exp_price]; unfold short; simp_rw [sum_filter]; rw [sum_comm (s:=S) (t:=univ)]; simp_rw [D.site_line]; rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; unfold long; split_ifs <;> first | omega | rw [zero_add] | rw [add_zero]
lemma flee (ht:0≤t) (x:A) : |D.short S k x| ≤ C:= by
 let X:= univ.filter (fun i:Finset A=>D.issues S k i=some x); refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (sum_le_sum (g:=fun i=> hit id D.fare t x i) (s:=X) (fun i h=>?_)) (budget_sum (D.cost.pays x) _))
 obtain ⟨-,l,u⟩:=D.episode S k (mem_filter.mp h).2; apply (D.bounds i S).trans; unfold hit; rw [if_pos (show x∈id i from l)]; exact le_mul_of_one_le_left (D.cost.nonneg _) (Real.one_le_exp (by positivity))
lemma fares_part {W:Finset A}(b:A)(p:(Scope.flags A).upon (B.ball b k) S W) : D.short S k b=D.short W k b:=by
 have he(i:Finset A)(e:i⊆B.ball b k): S∩i=W∩i:=by
   ext x; by_cases h:x∈i; · simp [h,p x (e h)]
   simp [h]
 have h(i:Finset A) : issues D S k i=some b ∨ issues D W k i=some b → i⊆ B.ball b k:=by
    intro g; have u:b∈i ∧ B.C i ∧ i.card<k:=g.elim (fun g=>(D.episode S k g).2) (fun g=>(D.episode W k g).2); exact Subset.trans (B.pair b u.2.1 u.1) (B.ball_le _ _ _ u.2.2.le)
 unfold short; simp_rw [sum_filter]; refine sum_congr rfl fun i _=>?_ ; by_cases hv:issues D S k i=some b∨issues D W k i=some b
 · specialize h i hv; simp only [issues,he i h,D.part ((Scope.flags A).mono h p)]; congr!
 rw [if_neg (not_or.mp hv).1,if_neg (not_or.mp hv).2]
lemma costs_price (S: Finset A)(x:Finset A): ‖D.long S k x‖≤ D.costs k x:=by unfold long costs; split; exact D.bounds ..; simp
lemma tail_pay (ht:0≤t): Moment.Toll id (D.costs k) (t/2) (Real.exp (-t/2*k)*C):=by
 refine ⟨fun i=> by unfold costs; split; exact D.cost.nonneg _; exact le_rfl,fun i=> budget_mono (budget_scale (Real.exp_pos _).le (D.cost.pays i)) (fun j=>?_) (fun j=>?_)⟩
 · unfold Moment.hit costs; split_ifs <;> first| exact mul_nonneg (Real.exp_pos _).le (D.cost.nonneg _) | simp
 unfold Moment.hit costs; split; swap; · simp
 split; rename_i e; rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (D.cost.nonneg _); apply Real.exp_monotone; dsimp only [id_eq]; nlinarith only [mul_le_mul_of_nonneg_left (show (k:ℝ)≤j.card by exact_mod_cast e) ht]
 simp only [mul_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (D.cost.nonneg _))
end YM.CF.BProof.Gauss.Night.Design
