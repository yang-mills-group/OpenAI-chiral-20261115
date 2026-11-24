import YM.CF.Siete.Pole
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Next.Foundations
open MultiNext.SignedSource Lyre Banjo Analysis Push.Local AnalyticBridge.VerifiedReset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
variable {n:Side}{a b r C d:ℝ}{k p j m:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{F: Pane n→ℂ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma advances {E D H:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup H][NormedSpace ℝ H] (k:ℕ) (Q:D → H)(R:E → D)(x:E){h:D →  Prop} (v:ContDiffAt ℝ ((k:ℕ):WithTop ℕ∞) Q (R x))(p:ContDiffAt ℝ ((k:ℕ):WithTop ℕ∞) R x)(u:∀ (m:ℕ), m ≤ k → ∀ i:Fin m → D,(∀ j,h (i j)) → ‖iteratedFDeriv ℝ m Q (R x) i‖≤ C)(a':E → Prop)(y: ∀ (i:ℕ), 1 ≤ i → i ≤ k → ∀ q:Fin i → E,(∀ j,a' (q j)) →  h (iteratedFDeriv ℝ i R x q)) (m:ℕ)(ht:m≤k)(A:Fin m → E)(H':∀ j,a' (A j)) : ‖iteratedFDeriv ℝ m (Q ∘ R) x A‖ ≤ (Fintype.card (OrderedFinpartition m):ℝ)*C:=by
 rw [iteratedFDeriv_comp v p (Nat.cast_le.mpr ht),FormalMultilinearSeries.taylorComp,_root_.sum_apply]
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> C) (fun i _=>?_)).trans_eq (by simp))
 simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]; apply u _ (i.length_le.trans ht); exact fun j=> y _ (i.partSize_pos j) ((i.partSize_le j).trans ht) _ fun j=> H' _ -- tune
lemma factorial (k:ℕ):∃ C:ℝ,1≤C∧∀ i:ℕ,i≤k → (Fintype.card (OrderedFinpartition i):ℝ)≤ C:=by
 let a(j:ℕ):= (Fintype.card (OrderedFinpartition j):ℝ); let C:=1+∑ i∈range (k+1), a i; have ha(i):0≤a i:=by unfold a; positivity
 refine ⟨C,le_add_of_nonneg_right (sum_nonneg fun i _=>ha i),fun i t=>?_⟩; exact (single_le_sum (fun i _=>ha i) (mem_range.mpr (Nat.lt_add_one_iff.mpr t))).trans (le_add_of_nonneg_left one_pos.le)
structure Proofs (B:BudgetPoint)(X:Support (More n))(o:Seat n)(R:E→tangD n)(x:E)(a:E→Prop)(k:ℕ)(C r:ℝ):Prop where
 grade(k':ℕ) (v:k'≤k)(y:Fin k'→E)(p:∀ i,a (y i)): Promise 2 C r B o X (iteratedFDeriv ℝ k' R x y)
 flow:ContDiffAt ℝ (k:ℕ∞ω) R x
 mark(i):Mom.needed X i → ‖R x i‖≤1∧ width B o i≤1
 sails(t:ℝ):t∈Set.Icc (0:ℝ) 1 → pingS B.threshold X (increment 1 (t • R x))
lemma christen (k:ℕ)(hp:5≤k)(u:ℝ)(p:1≤u): ∃ C:ℝ,1≤C∧∀ {n:Side}(B: BudgetPoint)(X:Support (More n))(o:Seat n)(v:E→tangD n)(F:Pane n→ℂ)(c r:ℝ)(R:E→Prop)(x:E), Nonwrapping X o → k ≤ B.order → 4 ≤ (More n).val → Acceptance B X o F c → 0 ≤ r → r ≤ 1 → Proofs B X o v x R k u r → ContDiffAt ℝ k (F ∘ (increment 1 ∘ v)) x∧∀ m:ℕ,m ≤ k → ∀ l: Fin m → E, (∀ i,R (l i)) → ‖iteratedFDeriv ℝ m (F∘ (increment 1 ∘ v)) x l‖ ≤ C*r^5*c:=by
 obtain ⟨A,g,h⟩:= storm k hp u p; obtain ⟨T,w,hT⟩:=factorial k; refine ⟨T*A,one_le_mul_of_one_le_of_one_le w g,@fun n B X o v F c r R x z y q e f t l=>?_⟩
 have ht:pingS B.threshold X (increment 1 (v x)):=by simpa using l.sails 1 (by simp)
 have hz:Proofs B X o v x R k u r:=l; have hg : ContDiffAt ℝ (k:ℕ∞ω) (F ∘ increment 1) (v x):=(stirring (1:Pane n) (v x) e.depends c (e.track _ ht)).of_le (Nat.cast_le.mpr y)
 refine ⟨hg.comp x l.flow,fun m hv L hl=>?_⟩; let f0: Fin 0→E:=fun i=> Fin.elim0 i
 have hh : Promise 2 u r B o X (v x):=by simpa using l.grade 0 (by omega) f0 (fun i=>Fin.elim0 i)
 have he:0≤c:=(e.track _ ht).grade
 refine (advances k _ _ _ hg l.flow (h n X B o (v x) F c r z y q e hh f t l.mark l.sails) R (fun i _ h=> l.grade i h) m hv L hl).trans ?_
 rw [show T*A*r^5*c=T*(A*r^5*c) by ring]; exact mul_le_mul_of_nonneg_right (hT m hv) (by positivity)
lemma coal {v w:tangD n}(h:Promise p C r B o X v) (ht: Sized (d*r^(p+1)) w B o) (g:0≤d)(q:0≤r):Promise p (C+d) r B o X (v+w):=by
 classical
 obtain ⟨s,hx,y,z⟩:=h; let t: Fin (p+1) → tangD n:= Pi.single (Fin.last p) w; refine ⟨fun i=>s i+t i,by rw [sum_add_distrib,hx]; simp [t],fun i=>?_,fun i hi=>?_⟩
 · dsimp only; have hl:=y i; by_cases v:i=Fin.last p
   · rw [v,show t (Fin.last p)=w from Pi.single_eq_same ..]; unfold Sized; rw [add_mul]; have hu:=y (Fin.last p)
     exact ⟨add_nonneg hu.1 ht.1,fun i=>(norm_add_le ..).trans ((add_le_add (hu.2 i) (ht.2 i)).trans_eq (add_mul ..).symm)⟩
   rw [show t i=0 from Pi.single_eq_of_ne v _,add_zero,add_mul]; refine ⟨add_nonneg hl.1 (by positivity),fun e=>(hl.2 e).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (Lyre.width_pos ..).le)⟩
 dsimp only; rw [show t i=0 from Pi.single_eq_of_ne (fun (v:i=Fin.last _) => by subst i; simp at hi) _,add_zero]; exact z i hi
end YM.CF.Siete
