import YM.CF.Rel.Ip
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
abbrev Disk(n:Side)(m:ℕ):= Fin m→ Body 2 n
abbrev Dike(n:Side)(m:ℕ):= Fin m→ Blip n
abbrev Delph(G:Gauge)(m:ℕ):= ContinuousMultilinearMap ℝ (fun _:Fin m=>G.Color) ℂ
def pavilion (K:ℕ)(x:Site n):= halo K ({x}: Support n)
def plot(K:ℕ):ℕ:= (K+K+1)^4
lemma pay_v(x:Site n): (pavilion r x).card≤plot r:= by simpa only [pavilion,plot,card_singleton,mul_one,one_mul] using (Lattice.Corona.halo_size ({x}:Support n) r)
lemma theatre (x y:Site n): y∈pavilion r x ↔ separation x y ≤ r:=by simp only [pavilion,halo_spec,mem_singleton, exists_eq_left]
def spoke(x:Site n)(r:ℕ): Finset (Blip n):= pavilion r x ×ˢ univ
def scope(n:Side){α:Type}[DecidableEq α](p:Finset α)(m:ℕ):Finset (Fin m→α):= Fintype.piFinset (fun _:Fin m=>p)
lemma vapour(x:Site n)(i:Blip n): i∈spoke x r ↔ separation x i.1≤ r:=by cases i; simp [spoke,theatre]
lemma stalk(x:Site n): (spoke x r).card ≤ plot r*Fintype.card Axis:= by unfold spoke; rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ (pay_v x)
lemma careC (α:Type)[DecidableEq α](p:Finset α)(m:ℕ): (scope n p m).card=p.card^m:=by simp [scope] -- tune
-- Ward to ordinary linking compression
lemma baseF(x:Blip n)(a:G.Color): ‖Nacre.put G n x a‖ ≤ ‖a‖:=by apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; change ‖Pi.single (M:=fun _=> G.Color) _ _ _‖≤_; rw [Pi.single_apply]; split <;> simp
lemma put_cost(x:Blip n): ‖Nacre.put G n x‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> (baseF x i).trans_eq (one_mul _).symm
lemma tick(P:Nacre.AimX m G n ℂ)(v:Dike n m): ‖timeA P v‖ ≤ ‖P‖:= (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ((prod_le_prod (g:=fun _=>1) (fun _ _=> norm_nonneg _) (fun i _=>put_cost (v i))).trans (by simp)))
variable {f:SpaceX G n} {o:Site n}
lemma sum_cost (h:Atom f o r)(he:ContDiffAt ℝ m (satX f) 0)(hp:‖cake m (satX f)‖≤C) : (∑ i:Dike n m,‖timeA (cake m (satX f)) i‖) ≤ ↑((plot r* Fintype.card Axis)^m)*C:=by
 let I:=scope n (spoke o r) m; have ht:I.card≤(plot r*Fintype.card Axis)^m:=by unfold I; rw [careC]; exact pow_le_pow_left₀ (Nat.zero_le _) (stalk o) _
 have hq :0 ≤ C:= (norm_nonneg _).trans hp
 calc
    _=∑ i∈I,‖timeA (cake m (satX f)) i‖:=by symm; apply sum_subset (subset_univ _) fun i _ hi=>?_ ; simp only [I,scope,Fintype.mem_piFinset, vapour,not_forall,not_le] at hi; obtain ⟨j,hj⟩:=hi; rw [spelt h he _ hj,norm_zero]
    _≤_:= (sum_le_sum (g:=fun _=>C) fun i _=> (tick _ _).trans hp).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) hq)
abbrev sumH(G:Gauge){n:Side}(j:InputZ G n)(a:Body 2 n):= dColor G n 1 j a
def payG(r:ℕ):ℕ:=9*(r+1)+1
def payF(r:ℕ):ℝ:=4*(payG r:ℝ)^2
lemma repayB(h: r<n.val)(hp:payG r < n.val) (x:Site n): ∃ P: Blip n→Body 2 n→ℝ,∀ v∈spoke x r,(∑ i, |P v i|)≤ payF r ∧ (∀ i,P v i ≠0→separation x i.1 ≤ payG r) ∧ ∀ X:InputZ G n, collect G (fullG x X) v= ∑ i,P v i • sumH G X i :=by
 choose A ha hx hX using funnel G.Color x
 let E:=ŧ n; let K:=fun (v:Blip n)(b:Body 2 n)=> A v (.inl (E.symm b)); refine ⟨K,fun v hv=>?_⟩
 have hv:= (vapour ..).mp hv; have hR :Font.slope x v+1 ≤ payG r:=by unfold Font.slope payG; omega
 have hg(i:Axis): A v (.inr i)=0:=by
    by_contra H; exact (not_lt_of_ge ((hx v _ H).trans hR)) hp
 refine ⟨?_,fun i he=> ?_,fun p=> ?_⟩
 · have he:= ha v; simp_rw [Wind,Fintype.sum_sum_type,hg,abs_zero,sum_const_zero,add_zero] at he; rw [← E.sum_comp]; unfold K; simp_rw [Equiv.symm_apply_apply]; refine he.trans ?_; unfold payF; gcongr; exact_mod_cast hR
 · obtain ⟨i,rfl⟩:= E.surjective i
   unfold K at he; rw [E.symm_apply_apply] at he; exact (hx v _ he).trans hR
 rw [sampleX,hX, ← E.sum_comp]; unfold K; simp_rw [E.symm_apply_apply,Wind,Fintype.sum_sum_type,hg,zero_smul,sum_const_zero,add_zero]; exact sum_congr rfl fun ⟨i,b⟩ _=> by rw [show heat x (collect G p) (.inl (i,b)) =_ from (fundamental G p i b)]; rfl
end YM.CF.Rel
