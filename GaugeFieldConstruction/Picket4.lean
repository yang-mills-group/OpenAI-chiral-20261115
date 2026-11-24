import GaugeFieldConstruction.LayerQ4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I:Type}{n:Side}[Fintype I][LinearOrder I]
section
variable {M E A:Type}[Fintype M][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable (X:Cornea M A E n)(σ:I→ Site n)
variable {F G:Finset I→ M→ A→ E}{B:ℕ}{l r a s t T' C:ℝ}{S:Finset (Finset I)}
lemma book_up(p:BookT X F B S a r l)(v:0 ≤ s)(u:t≤a)(w:s ≤ r)(vg:l≤T') : BookT X F B S t s T':=by
 obtain ⟨H,p,k⟩:= p; refine ⟨H,p,fun i=>le_trans ?_ ((k i).trans vg)⟩; apply Finset.sum_le_sum; intro j b; refine mul_le_mul (pow_le_pow_left₀ v w _) ?_ ?_ (pow_nonneg (v.trans w) _)
 · apply Finset.sum_le_sum; intro i _; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right u (Nat.cast_nonneg _))) (X.posG _ _ _ (p j b _))
 exact sum_nonneg (fun i _=>mul_nonneg (Real.exp_pos _).le (X.posG _ _ _ (p j b i)))
lemma book_plus (p:BookT X F B S a r l)(q:BookT X G B S a r T'): BookT X (F+G) B S a r (l+T'):=by
 obtain ⟨H,u,v⟩:=p; obtain ⟨J,g,b⟩:=q; refine ⟨H+J,fun i p j=>X.add _ _ _ _ _ (u i p j) (g i p j), fun i=>?_⟩ -- works signs
 simp only [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add (v i) (b i)
lemma Ledge_add (p:Ledges X σ F)(q:Ledges X σ G): Ledges X σ (F+G):=by
 intro x y w i t; by_cases h:F i x y=0
 · apply q _ _ w; intro g; apply t; beta_reduce at *; rw [Pi.add_apply, Pi.add_apply, Pi.add_apply,h,g,zero_add]
 exact p _ _ w i h
-- certificate transform journal
lemma BookUnit(p: BookT X F B S a 1 l)(i:Finset I)(e:i∈S): ShelfK X (F i) B a l :=by
 obtain ⟨F',u,q⟩:= p; refine ⟨F' i,u i e,fun j=>?_⟩
 apply le_trans _ (q j); have g:= single_le_sum (s:=S) (f:=fun i=> (1:ℝ)^i.card * (∑ x∈ univ.filter (fun y=> j∈X.Φ y), dra_k B a (X.Φ x)*F' i x)) (fun i v=> mul_nonneg (by positivity) (sum_nonneg fun y _=> mul_nonneg (Real.exp_pos _).le (X.posG _ _ _ (u _ v _)))) e; simpa only[one_pow,one_mul] using g
end
section
variable (U:BudgetPoint)(h r:ℝ)(u:0<h)(v:ℕ)(σ:I→Seat n)(F:XE I (InkD n) n)(K:KK I (Copy n) n)(T:PI I n→ℝ)(Y:KI I n→ℝ)(L:List (Seat n)) (b:ℕ)
open Py Py.Riant Nor Pail
lemma Horn4.bigRadius {r w D w' s y:ℝ}(p:Horn4 σ F K U h u r w D v)(x:w' ≤ w)(t:0 ≤ s)(d:s ≤ r)(q:D≤y):Horn4 σ F K U h u s w' y v:=⟨p.core,p.holdK, book_up _ p.paw t x d q, book_up _ p.crowd t x d q,p.haloT⟩
lemma Horn4.merge {G:XE I (InkD n) n}{H:KK I (Copy n) n}{t d l:ℝ}(p:Horn4 σ F K U h u r t d v)(q:Horn4 σ G H U h u r t l v):Horn4 σ (F+G) (K+H) U h u r t (d+l) v:=by
 refine ⟨Ledge_add _ _ p.core q.core,Ledge_add _ _ p.holdK q.holdK,book_plus _ p.paw q.paw,book_plus _ p.crowd q.crowd,fun i t=>?_⟩
 by_cases h:K i=0
 · apply q.haloT; intro e; exact t (by simp[h,e])
 exact p.haloT _ h
private lemma marchLe {v r:ℝ}{p:ℕ}{X:Support (More n)}(h:v≤r):March p v X≤ March p r X:= Real.exp_monotone (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))
section
variable (bp:0<r) (A:Rio I n)(V:CashI I n)(m:ℕ)(q :Weighted U σ r h (Rill.cipherK m) A V)
include q bp u
lemma deliver (T:Ids n)(a l η X Y W:ℝ)(p:l ≤ a)(hY: reserveT (KeyUp U).power U.order U.B ζd*(X+Y)≤ W)(hp: reserveT U.power U.order U.B ζd*Y ≤ W) (w:∀ i:Seat n,Paw U.B a η V [] i≤X∧ Rio.Band U.B a η V [] i ≤ Y): Horn4 σ (pureX A) A.B U h u r l W m:=by
 have t:=ReefX.registry_plus σ cloudP (T:=PitR U h r) ReefxR q.white q.active
 refine ⟨fun i x _ k e=> t.pin _ (fun j=> e (congrFun j x)),fun i x _ j h=>q.bank.pin _ (fun t=> h (congrFun t x)), ?_, ?_,?_ ⟩
 · refine book_up _ (pawBook U σ r h u.le bp l _ T _ (V.W+V.M) t ?_) bp.le le_rfl le_rfl hY -- order tune
   intro i; rw[pointX_add]; refine add_le_add (le_trans ?_ (w i).1) (le_trans ?_ (w i).2); -- T requires spent
   · apply pointX_up cloudP _ q.white.gist; intro x; unfold RedB tempI; rw[Bonus_nil,Real.exp_zero,mul_one]; apply marchLe; linarith only [p,ζdp]
   apply le_trans _ (le_add_of_nonneg_right (pointX_gene cloudK _ q.bank.gist _ (fun _=>Temp_p ..|>.le) _)); apply pointX_up cloudP _ q.active.gist _ (RedB U.B a η []); intro X; unfold RedB tempI; rw[Bonus_nil,Real.exp_zero,mul_one]; apply marchLe; linarith only [p,ζdp]
 · refine book_up _ (forceBook U σ r h u.le bp l Y m A.B V.F q.bank ?_) bp.le le_rfl le_rfl hp
   intro i; apply le_trans _ (w i).2; apply le_trans _ (le_add_of_nonneg_left (pointX_gene cloudP _ q.active.gist _ (fun _=>Temp_p ..|>.le) _)); apply pointX_up cloudK _ q.bank.gist _ (ColdB U.B a η []); intro X; unfold ColdB tempI; rw [Bonus_nil,Real.exp_zero,mul_one]; apply marchLe; linarith only [p,ζdp]
 intro i g; have h:∃ x:Orbit n,A.B i x≠0:=by by_contra! h; exact g (funext h)
 obtain ⟨x,b⟩:=h; exact ((q.bank.lit i).2 x b).2
#print axioms deliver
end
end
end Iona
end YM.CF.Scree.Ing
end
