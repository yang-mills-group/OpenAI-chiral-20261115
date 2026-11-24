import YM.CF.Rel.Star
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
def listH(u: DialT n m)(k:Site n):DialT n (m+1):= Fin.cons (k-∑ i,u i) u
lemma tipH(u: DialT n m)(k:Site n): ∑ i,listH u k i=k:=by rw [Fin.sum_univ_succ]; simp [listH]
private lemma cSH (u d:DialT n m)(k X p:Site n)(A: CurRun (m+1)): pulseP k X*(∏ i, cell (listH u k i) ((diskP p d A i).1+X))= cell k p*cMul u d:=by
 let a:=listH u k
 change pulseP k X*_=_; simp_rw [cell_add, Finset.prod_mul_distrib, ← cwrap,tipH]; let K:= cell k X; change K⁻¹ * (_*K)= _ ; rw [mul_left_comm K⁻¹,inv_mul_cancel₀ (show K≠0 from cell_ne _ _),mul_one] -- tune
 conv_lhs=> rw [Fin.prod_univ_succ]
 have he: cell k p= cell (a 0) p* (∏ i: Fin m,cell (u i) p):= by nth_rw 1 [←tipH u k]; rw [cwrap, Fin.prod_univ_succ]; rfl -- tune
 simp only [diskP,Fin.cons_zero,Fin.cons_succ]; rw [he]; change cell (a 0) p * (∏ i: Fin m,cell (u i) (p+d i))=_; simp_rw [cell_add,Finset.prod_mul_distrib]; rw [←mul_assoc]; rfl
lemma asks {F: FileM n G}(k:Site n)(h:shapeV k F)(he:ContDiffAt ℝ (↑(m+1:ℕ):WithTop ℕ∞) (satX (F 0)) 0)(W:KitM G n (m+1))(hw:∀ V,cake (m+1) (satX (F 0)) V= ∑ p, engages W p V)(v:Axis→ℝ)(u: DialT n m)(hp:Push.Loops.Matches (axes v) k)(X:Site n)(a:Run (m+1))(b:SpotG G (m+1)) :
 (∑ x:DialT n (m+1), cMul (listH u k) x*cake (m+1) (satX (F X)) (fun i=>flaw G (x i,a i) (b i)))= Braid.clipP (breathL W k b) v a (tollX u):=by
 rw [run_tp k h he W hw _ (listH u k) (vars hp u).2 X a b,d_sum]; unfold clipP fromCurl
 simp_rw [coins_r,grabG,mul_sum];
 -- reorder
 let T (p: Site n)(d:DialT n m)(i:CurRun (m+1)):= (∏ j,symbol 1 (cardR v (tollX u) j) (i j) (a j))* (cMul u d * (cell k p*W (diskP p d i) (fun i=> jewelG G (b i))))
 calc
    _=∑ p:Site n,∑ d:DialT n m,∑ i:CurRun (m+1), T p d i:=by
       refine sum_congr rfl fun i _=>sum_congr rfl fun z _=>sum_congr rfl fun x _=>?_ ; rw [Finset.prod_mul_distrib, ←mul_assoc,←mul_assoc,cSH]; unfold T; have he(t:Fin (m+1)): (diskP i z x t).2=x t:=by induction t using Fin.cases <;>simp [diskP]
       simp_rw [he]; ring
    _= _:= by
       rw [sum_comm]; change _=∑ i,∑ j,∑ k,T k j i; conv_rhs=> rw [sum_comm]
       exact sum_congr rfl fun a _=>sum_comm
end YM.CF.Rel
