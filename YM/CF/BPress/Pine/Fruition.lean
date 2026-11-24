import YM.CF.BPress.Pine.Root
/- Eq:B-PfC sum over decorated labels. Group with Palmer, fits contour-free theorem part. Pairing *sign* and zero of non-matches/repeats implemented through genuine Pfaffian tested on exterior strings, only geometry projection for power. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J] {Y:Type}[DecidableEq Y][Fintype Y]{F:Branch.Field Y}
namespace Story
variable {D:EdgeD I B Y F}(S:Story J D)(b:B→ℝ)(w:J→ℝ)
variable {C a μ τ :ℝ}
structure Enorm (D:EdgeD I B Y F)(a C:ℝ)(b:B→ℝ):Prop where
 c:0<C
 f:∀ i,0≤ b i
 pays (i:I): ∑ x∈ D.holds i, rent a (look D x)*b x ≤ C
-- decorated cost no factorial. combine startup after. Mint(a0/2) call
abbrev livesB(i:I) (f:Option (D.Prec i)) := f.elim (1:ℝ) (fun b'=> b b'.val)
abbrev eco (x:J)(p: D.Net (S.word x)):= ∏ i:EdgeD.Permits (S.word x), livesB (D:=D) b i.val (p i)
def blue (p:S.Drone):= w p.1 * eco S b p.1 p.2
def stiff(e:ℝ)(x:S.Drone):= eco S b x.1 x.2 * ∏ i:EdgeD.Permits (S.word x.1), rent e (lit D _ (x.2 i))
abbrev ahead (w : ℝ) (x:J)(t:ℝ):= w*t^(S.word x).length
lemma green_pos (b₀:∀ i,0 ≤ b i) : ∀ (i:I)(u:Option (D.Prec i)),0≤ livesB b i u:= by intro i u; cases u; exact zero_le_one; apply b₀
lemma blue_pos (x:S.Drone)(h:∀ i,0≤ w i)(p:∀ i,0≤b i):0≤ blue S b w x:=mul_nonneg (h _) (prod_nonneg (fun i _=>green_pos b p i.val _))
lemma op_norm (A B:Dough I) : ‖grap A B‖≤‖A‖*‖B‖:=by
 let U(X:Dough I):= acts X.val (vacuum I); have he(X:Dough I):‖U X‖≤‖X‖:= (Spin.Eye.norm_act ..).trans (by simp only [show ‖Fock.vacuum I‖=1 from (by simp [Fock.vacuum,basisKet]),mul_one]; rfl); exact (norm_inner_le_norm ..).trans (mul_le_mul (he _) (he _) (norm_nonneg _) (norm_nonneg _))
lemma b_card (x:J) : Fintype.card (Permits (S.word x))=(S.word x).length:=by simp only [Permits,Fintype.card_coe]; exact List.toFinset_card_of_nodup (S.n x) -- tune
lemma grueP(K:B→ℂ)(u:J→ℂ)(f:∀ i,‖K i‖ ≤ b i)(g:∀ i,‖u i‖ ≤ w i)(p: Finset S.Drone): ‖totalW S K u p‖ ≤ ∏ i∈p,blue S b w i:=by
 unfold totalW blue; have hu(i):0≤b i:=(norm_nonneg _).trans (f i); have he(x:S.Drone):‖cairn S K x‖≤eco S b x.1 x.2:=by
    apply (Finset.norm_prod_le ..).trans; apply Finset.prod_le_prod; exact fun i _=> norm_nonneg _; intro i _; unfold livesB green; cases t:x.2 i; exact norm_one.le; next v=> exact (twig_k D K v.val).trans (f _)
 have ht:‖allStem S p‖≤1:=by apply (Finset.norm_prod_le p _).trans; exact prod_le_one (fun i _=>norm_nonneg _) (fun i _=> cost_raw _)
 split; next t=>
    rw [norm_mul,norm_prod, prod_mul_distrib]; apply mul_le_mul (Finset.prod_le_prod (fun i _=> norm_nonneg (u _)) (fun i v=>g _)) ((op_norm ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ht).trans ((Finset.norm_prod_le ..).trans (Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> he i))))) (norm_nonneg _) (prod_nonneg (fun i _=> (norm_nonneg _).trans (g _))) -- tune
 next t=> rw [norm_zero]; exact prod_nonneg (fun i _=>blue_pos S b w i (fun i=> (norm_nonneg _).trans (g _)) hu)
lemma stif_s (x:S.Drone)(e:ℝ)(t:∀ i, 0≤ b i): 0≤ stiff S b e x:=mul_nonneg (prod_nonneg fun i _=> green_pos b t i.val _) (prod_nonneg fun i _=> (rent_pos _ _).le)
lemma prenatal (p: Enorm D a C b) (x:J): ∑ y:D.Net (S.word x),stiff S b a ⟨x,y⟩ ≤ (1+C)^(S.word x).length := by
 let B(i:I)(e:Option (D.Prec i)):= livesB b i e*rent a (lit D i e); have he(i):∑ e:Option (D.Prec i),B i e≤1+C:=by
   rw [Fintype.sum_option]; have hp:B i none=1:=by simp [B,livesB,rent,lit]
   rw [hp]; apply add_le_add le_rfl; convert! p.pays i using 1; nth_rw 2 [← sum_attach]; unfold B livesB lit; simp only [Finset.univ_eq_attach, Option.elim_some, mul_comm]
 let P:= univ (α:= Permits (S.word x)); have ht(y:D.Net (S.word x)) : stiff S b a ⟨x,y⟩=∏ i:Permits (S.word x), B i.val (y i):=(prod_mul_distrib ..).symm; simp_rw [ht]; rw [← Fintype.prod_sum]; refine (Finset.prod_le_prod (g:=fun _=>(1+C)) (fun i _=> sum_nonneg (fun t _=> mul_nonneg (green_pos b p.f _ _) (rent_pos ..|>.le))) (fun i _=> he _)).trans ?_; rw [prod_const, card_univ,b_card]
-- charge ray.X distance. integer block growth lower.Stated for all F but paid specialized with kernel.Y.Pay to HANDLE from point valuation all products.
def hasSpot (F:Branch.Field Y)(s:ℝ)(c:ℝ): Prop:=∀ x, ∑ y,Real.exp (-(s*(F.span x y:ℝ))) ≤ c
private def nearestX (k:J)(o:Y):= (S.base k).inf' (Grid.inhabited_grove (S.landed _)) (F.span o)
noncomputable def own (k:J)(o:Y):= (exists_mem_eq_inf' (Grid.inhabited_grove (S.landed k)) (F.span o)).choose
lemma owner (k:J)(o:Y): own S k o ∈ S.base k∧∀ a∈S.base k,F.span o (own S k o) ≤ F.span o a:=by
 let p:= (exists_mem_eq_inf' (Grid.inhabited_grove (S.landed k)) (F.span o)); obtain ⟨q,v⟩:= p.choose_spec; refine ⟨q,fun a h=>?_⟩; unfold own; change F.span o p.choose ≤ _; rw [←v]; exact inf'_le _ h
lemma magnify (e:S.Drone) (o:Y)(v:o∈S.fort e) : F.span o (own S e.1 o) ≤ ∑ i:Permits (S.word e.1), (lit D _ (e.2 i)).card:=by
 rcases mem_union.mp v with h|h; · apply ((owner S e.1 o).2 o h).trans; rw [F.reflex]; omega
 obtain ⟨i,q,p⟩:= mem_biUnion.mp h; let c(q :Permits (S.word e.1)) := lit D _ (e.2 q); refine le_trans ?_ (single_le_sum (f:=fun i=>(c i).card) (fun i _=> Nat.zero_le _) (mem_univ i)); change o ∈ c i at p; unfold c lit at p ⊢; cases f:e.2 i with|none=> rw [f] at p; exact False.elim (notMem_empty _ p)| some x=> obtain ⟨y,t⟩:=S.frag e i f; rw [f] at p; exact ((owner S e.1 o).2 y ((mem_inter.mp t).2)).trans ((D.paints x.val).lim o p y (mem_inter.mp t).1 |>.le)
lemma elongated (x:S.Drone): (fort S x).card ≤ (S.base x.1).card + ∑ i:Permits (S.word x.1),(lit D i.val (x.2 i)).card:= (card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le ((S.base x.1).card))
lemma temperature (x:S.Drone)(u:0≤ μ)(b:0≤a)(e:μ ≤ a)(y:Y)(p:y∈fort S x): Real.exp (a*F.span y (own S x.1 y))*rent μ (fort S x) ≤ rent μ (S.base x.1) * ∏ i:Permits (S.word x.1), rent (a+a) (lit D i.val (x.2 i)):=by
 unfold rent; let z:=x.1; have he:= magnify S x y p; -- tune
 rw [← Real.exp_add,←Real.exp_sum, ← Real.exp_add,←Finset.mul_sum]; apply Real.exp_monotone; have hz: ((fort S x).card:ℝ)≤ (S.base x.1).card+ ∑ i:Permits (S.word x.1), ((lit D i.val (x.2 i)).card:ℝ):= by exact_mod_cast elongated S x
 let w:= (∑ i:Permits (S.word x.1), ((lit D i.val (x.2 i)).card:ℝ)); have hw:(F.span y (own S x.1 y):ℝ)≤ w:=(by unfold w; exact_mod_cast he)
 unfold w at hw; nlinarith only [mul_le_mul_of_nonneg_left hz u, mul_le_mul_of_nonneg_left hw b, mul_le_mul_of_nonneg_right e ((Nat.cast_nonneg _).trans hw)] -- tune
end Story
end YM.CF.BPress.Pine
