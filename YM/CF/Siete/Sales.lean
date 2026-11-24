/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Scree.Locus
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Ray
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Next.Foundations
open MultiNext.SignedSource Lyre Banjo Analysis
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n:Side}{a b r C d:ℝ}{k p j:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{F: Pane n→ℂ}
lemma seals {N:Type*}[NormedAddCommGroup N][NormedSpace ℝ N]{F:tangD n→N}(h:Signs B o F C)(v:Fin k→ tangD n)(a:Fin k→ℝ)(u:k ≤ B.order)(p:∀ i,Sized (a i) (v i) B o): ‖iteratedFDeriv ℝ k F 0 v‖ ≤ (∏ i,a i)*C:=by
 let f(i:Fin k):=(a i)⁻¹ • v i; have he(i): v i = a i • f i:=by
    rcases eq_or_lt_of_le (p i).1 with g|g; · rw [←g,zero_smul]; funext q; exact norm_le_zero_iff.mp (by have hx:=(p i).2 q; simpa [←g] using hx)
    exact (smul_inv_smul₀ g.ne' _).symm
 have hf(i): B.dirBound o (f i):=by
    intro x; change ‖f i x‖≤Lyre.width B o x
    rcases eq_or_lt_of_le (p i).1 with g|g
    · unfold f; rw [←g, inv_zero,zero_smul,Pi.zero_apply,norm_zero]; exact (Lyre.width_pos ..).le
    change ‖(a i)⁻¹ • (v i x)‖≤_; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr g).le,inv_mul_le_iff₀ g]; exact (p i).2 x
 have hx :0≤∏ i,a i:= prod_nonneg fun i _=> (p i).1
 rw [funext he,ContinuousMultilinearMap.map_smul_univ,norm_smul, Real.norm_of_nonneg hx]; exact mul_le_mul_of_nonneg_left (h.token k u _ hf) hx
-- boiling transitions for individual entries (Budgets Canvas Shapes). uses baseline surge
lemma stirring (U:Pane n)(x: tangD n)(t:LocalOn X F)(V:ℝ)(hs: Signs B o (F ∘ increment (increment U x)) V):ContDiffAt ℝ (B.order:ℕ∞) (F∘ increment U) x:=by
 let s:=surge X x
 obtain ⟨ha,hp⟩:= arisen X x; let f:=F ∘ increment U; have hh:ContDiffAt ℝ (B.order:ℕ∞) (fun v=> f (x+v)) 0:= (((show s 0=0 from ha).symm ▸ hs.paid).comp (f:=s) 0 (hp.of_le le_top)).congr_of_eventuallyEq (flowing X x U t)
 have hx := (show ContDiffAt ℝ (B.order:ℕ∞) (fun v=>f (x+v)) (x-x) from (sub_self x).symm ▸ hh).comp (f:=fun v=>v-x) x (contDiffAt_id.sub (contDiffAt_const (c:=x)))
 rw [show (fun v=> f (x+v)) ∘ (fun v=> v-x)=f from funext fun v=> congrArg f (add_sub_cancel ..)] at hx; exact hx
lemma steward(k:ℕ): ∃ C:ℝ,1≤ C∧∀ (n:Side)(X:Support (More n))(U: Pane n)(P:RG.BudgetPoint)(o:Seat n)(V:tangD n)(F:Pane n→ℂ), LocalOn X F→ ∀ (a:ℝ)(K: Fin k→ℝ)(x:Fin k→tangD n), Signs P o (F ∘ increment (increment U V)) a→ k≤P.order →(∀ i,Mom.needed X i→‖V i‖≤1∧ width P o i≤1)→(∀ i,Sized (K i) (x i) P o)→ ‖iteratedFDeriv ℝ k (F ∘ increment U) V x‖ ≤ C*(∏ i,K i)*a:=by
 choose b hb h using fun i=>Lyre.bore group i 1
 let Q(i:OrderedFinpartition k):=∏ j,b (i.partSize j-1); refine ⟨1+∑ i,Q i,le_add_of_nonneg_right (sum_nonneg fun i _=> prod_nonneg fun j _=> zero_le_one.trans (hb _)),?_⟩ -- nonneg tune
 intro n X U P o V F e a K x hs v ht g; let H:=surge X V; let f:= F ∘ increment U; let Y:=increment U V; let A:=F ∘ increment Y
 obtain ⟨ha,hp⟩:= arisen X V; have hx:= ((flowing X V U e).iteratedFDeriv (𝕜:=ℝ) k).eq_of_nhds; change iteratedFDeriv ℝ k (fun y=>f (V+y)) 0=iteratedFDeriv ℝ k (A ∘ H) 0 at hx
 have hP : ContDiffAt ℝ (P.order:WithTop ℕ∞) A (H 0):=by rw [show H 0=0 from ha]; exact hs.paid
 rw [iteratedFDeriv_comp_add_left,add_zero,iteratedFDeriv_comp hP (hp.of_le le_top) (Nat.cast_le.mpr v)] at hx
 change ‖iteratedFDeriv ℝ k f _ x‖≤_; rw [hx, FormalMultilinearSeries.taylorComp,_root_.sum_apply]; simp_rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
 let t:= ∏ i,K i; have he:0≤ t:=prod_nonneg fun i _=> (g i).1
 rw [show H 0=0 from ha]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> Q i*t*a) fun i _=> ?_).trans ?_)
 · let Λ j := iteratedFDeriv ℝ (i.partSize j) H 0 (x ∘ i.emb j)
   let Ψ j:= ∏ w,K (i.emb j w)
   have hz j:Sized (b (i.partSize j-1)*Ψ j) (Λ j) P o:=by
      have hi (m : ℕ) (hk:m=i.partSize j)(v:Fin m→ Directions group (More n))(c:Fin m→ℝ)(g:∀ k,Sized (c k) (v k) P o): Sized (b (m-1)*∏ i,c i) (iteratedFDeriv ℝ m H 0 v) P o:=by cases m; have he:=i.partSize_pos j; omega; simpa only [Nat.add_sub_cancel] using h _ (More n) X P o V v c ht g
      exact hi _ rfl _ _ (fun j=>g _)
   change ‖iteratedFDeriv ℝ i.length A 0 Λ‖ ≤ _; refine (seals hs _ (fun j=>b (i.partSize j-1)*Ψ j) (i.length_le.trans v) hz).trans_eq ?_; unfold Q Ψ t; rw [prod_mul_distrib,i.prod_sigma_eq_prod]
 rw [← Finset.sum_mul,← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) he) hs.grade
lemma multip(k:ℕ) :∃ C:ℝ,1≤C∧∀ (n:Side)(X:Support (More n))(U:Pane n)(P: BudgetPoint)(o:Seat n)(v:tangD n)(F:Pane n→ℂ),LocalOn X F→∀ a:ℝ, Signs P o (F ∘ increment (increment U v)) a→(∀ i,Mom.needed X i→‖v i‖≤1∧Lyre.width P o i≤1) →∀ m:ℕ,m≤k→m≤P.order→∀ (y:Fin m→ tangD n) (A:Fin m→ℝ),(∀ i,Sized (A i) (y i) P o)→ ‖iteratedFDeriv ℝ m (F∘ increment U) v y‖ ≤ C*(∏ i,A i)*a:=by
 choose C h H using steward
 let B:=∑ i∈range (k+1),C i; have ht(i)(l:i ≤ k):C i≤B:=single_le_sum (f:=C) (fun j _=> zero_le_one.trans (h j)) (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr l)); refine ⟨B,(h 0).trans (ht 0 (by omega)),fun N X V P x p W t a w g m hm hb y A hA=>(H m N X V P x p W t a A y w hb g hA).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ht m hm) (prod_nonneg fun i _=> (hA i).1)) w.grade)⟩ -- tune pattern
end YM.CF.Siete
