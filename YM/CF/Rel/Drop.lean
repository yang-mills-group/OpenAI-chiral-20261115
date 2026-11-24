import YM.CF.Rel.Burr
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
abbrev reedU(i:Fin (m+1))(a:Axis):DialT n m:= Fin.cases (fun _=>-Lattice.step a) (fun i=> Pi.single i (Lattice.step a)) i
abbrev sting(k:Site n)(i:Fin (m+1))(a:Axis):ℂ:= if i=0 then cell k (Lattice.step a) else 1
lemma shaw (k:Site n)(v:Axis→ℝ)(h:Push.Loops.Matches (axes v) k)(b:DialT n m) (i:Fin (m+1))(a:Axis) : Complex.exp (Complex.I * cardR v (tollX b) i a)=sting k i a*cMul b (reedU i a):=by
 have hh:=vars h b; induction i using Fin.cases with
 | zero=> rw [←(hh.2 0).step]; unfold sting cMul reedU; simp only [↓reduceIte,Fin.cons_zero,Fin.cases_zero]; rw [cell_sub, cwrap]; simp_rw [cell_inverse, Finset.prod_inv_distrib]
 | succ i=>
    rw [←(hh.2 i.succ).step]; unfold sting reedU cMul; simp only [Fin.succ_ne_zero, ↓reduceIte,one_mul,Fin.cons_succ,Fin.cases_succ]; rw [Fintype.prod_eq_single i]; · rw [Pi.single_eq_same]
    intro j hj; rw [Pi.single_eq_of_ne hj, cell_origin]
lemma symLeftR (a:Axis)(i:TypeFace (m+1))(j:TypeFace m):left ℂ m a i j= (left ℝ m a i j:ℝ):=by unfold left; simp only [Matrix.of_apply]; split_ifs <;> simp [parity]
lemma shaw_k (k:Site n)(v:Axis→ℝ)(h:Push.Loops.Matches (axes v) k)(b:DialT n m)(i:Fin (m+1))(j:TypeFace 3)(p:TypeFace 2): symbol 2 (cardR v (tollX b) i) j p= ∑ a:Axis,(sting k i a * cMul b (reedU i a)-1)*left ℂ 2 a j p:=by unfold symbol wedge; simp_rw [Matrix.sum_apply, Matrix.smul_apply, Exterior.q,shaw _ _ h]; rfl
-- Ca identities exact
abbrev arc_t {m:ℕ}:=Space m→ℂ
lemma cac (f g:arc_t (m:=m))(d:DialT n m)(h:∀ i:DialT n m, f (tollX i)=g (tollX i)): Ca f d= Ca g d:=by unfold Ca; simp_rw [h]
lemma ca_sub(f g:arc_t (m:=m))(d:DialT n m):Ca (fun i=> f i-g i) d=Ca f d-Ca g d:=by unfold Ca; simp_rw [mul_sub,sum_sub_distrib]; rw [mul_sub]
lemma ca_mul (f:arc_t (m:=m))(c:ℂ)(d:DialT n m):Ca (fun i=>c*f i) d=c*Ca f d:=by unfold Ca; simp_rw [mul_left_comm (_⁻¹) c,← mul_sum]; rw [mul_left_comm]
lemma ca_sum {α:Type}[Fintype α](F:α→arc_t (m:=m))(d: DialT n m): Ca (fun y=>∑ i,F i y) d= ∑ i,Ca (F i) d:=by unfold Ca; simp_rw [mul_sum]; exact sum_comm
lemma ca_m (f:arc_t (m:=m))(d b:DialT n m): Ca (fun i=> Laurent.mode i (spanW b)*f i) d= Ca f (d-b):=by
 unfold Ca; simp_rw [cord,coil_W]; congr 1; refine sum_congr rfl fun i _=> ?_; simp_rw [sub_eq_add_neg,cnorm,cneg,_root_.mul_inv_rev,inv_inv]; ring
lemma accuse (k:Site n)(v:Axis→ℝ)(h:Push.Loops.Matches (axes v) k)(X:Shed (Keys m) (m+1))(i:Fin (m+1))(p:CurRun (m+1))(d:DialT n m) : Ca (fun y=> nullL (cardR v y) i (X y) p) d=∑ b:TypeFace 3,∑ a:Axis,left ℂ 2 a b (p i)*(sting k i a*Ca (fun y=> X y b p) (d-reedU i a)-Ca (fun y=>X y b p) d):=by
 let F(b a)(y:Space m):= left ℂ 2 a b (p i)*(sting k i a*(Laurent.mode y (spanW (reedU (n:=n) i a))*X y b p)-X y b p)
 calc
    _=Ca (fun y=>∑ b:TypeFace 3,∑ a:Axis,F b a y) d:= cac _ _ _ (by intro j; unfold nullL; simp_rw [shaw_k k v h,Finset.sum_mul,F,cord,coil_W]; refine sum_congr rfl (fun b _=> sum_congr rfl fun a _=>?_); ring)
    _= _:= by rw [ca_sum (fun b y=> ∑ a,F b a y)]; simp_rw [ca_sum]; unfold F; apply sum_congr rfl; intro b _; apply sum_congr rfl; intro a _; rw [ca_mul,ca_sub,ca_mul,ca_m]
-- toll axes equality
abbrev zoneU (i:Fin m→Site n): Corn (Keys m):=fun j=> (tollX i j).re
lemma toll_unt (i:DialT n m): tollX i=axes (zoneU i):=by
 funext p; have he:=congr_fun (real_frequency (i p.1)) p.2; apply Complex.ext
 · simp [axes,zoneU]
 unfold zoneU axes; rw [Complex.ofReal_im]; unfold tollX; have he:=congr_arg Complex.im he; simp only [Pi.star_apply,Complex.star_def,Complex.conj_im] at he; linarith only [he] -- tune
end YM.CF.Rel
