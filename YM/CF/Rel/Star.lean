import YM.CF.Rel.Touch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
def flaw (G:Gauge)(i:Body 1 n) (a : G.ColorIndex):InputZ G n:= Pi.single i (jewelG G a)
lemma part_i(i:Body 2 n)(j:Body 1 n)(a:G.ColorIndex):sumH G (flaw G j a) i= (Exterior.d 1 n i j) • jewelG G a:=by
 ext v; change (∑ k, Exterior.d 1 n i k * ((flaw G j a k) v)) = _; rw [sum_eq_single j]
 · simp_rw [flaw,Pi.single_eq_same]; rfl
 · intro b _ h; rw [flaw,Pi.single_eq_of_ne h]; change _ * 0=0; rw [mul_zero]
 simp
lemma on_plane {u:Momentum}{k:Site n}(h:Push.Loops.Matches u k)(i: TypeFace 1)(b:Body 2 n): (∑ x:Site n, cell k x* (Exterior.d 1 n b (x,i):ℝ))= cell k b.1 * symbol 1 u b.2 i:=by
 have he: Routed (Equiv.refl _) (Equiv.refl _) k k (cmat (Exterior.d 1 n)) (symbol 1 u):= reading u 1 ▸ acts_routed _ (cobound_safe 1) h
 have hp := congr_fun (congr_fun he b) i; rw [plane_mul] at hp; simp only [Matrix.mul_apply] at hp
 unfold Co at hp; rw [Fintype.sum_prod_type] at hp; refine Eq.trans ?_ hp; exact sum_congr rfl fun j _=> by simp [cmat_apply,approached,plane,mul_ite,mul_comm] -- tune
lemma run_tp {F: FileM n G}(k:Site n)(h:shapeV k F)(he:ContDiffAt ℝ m (satX (F 0)) 0)(W:KitM G n m)(hw:∀ V,cake m (satX (F 0)) V= ∑ p, engages W p V)(v:Fin m→Momentum)(d: DialT n m)(hp:∀ j,Push.Loops.Matches (v j) (d j))(X:Site n)(a:Run m)(b:SpotG G m) :
 (∑ x:DialT n m, cMul d x*cake m (satX (F X)) (fun i=>flaw G (x i,a i) (b i)))= pulseP k X * ∑ p:Disk n m,(∏ i, cell (d i) ((p i).1+X)*symbol 1 (v i) (p i).2 (a i))*W p (fun i=> jewelG G (b i)):=by
 simp_rw [Nth F k h he X, hw, mul_sum]; rw [sum_comm (s:=(univ:Finset (DialT n m)))]; apply sum_congr rfl; intro i _; unfold engages; simp_rw [sumHt,part_i,ContinuousMultilinearMap.map_smul_univ,Complex.real_smul, Complex.ofReal_prod,cMul]; calc
    _ = pulseP k X*(∑ p:DialT n m, (∏ j,cell (d j) (p j) * (Exterior.d 1 n ((i j).1+X,(i j).2) (p j,a j) : ℝ)))*W i (fun j=>jewelG G (b j)):=by rw [mul_sum,sum_mul]; apply sum_congr rfl; intro j _; rw [Finset.prod_mul_distrib]; ring
    _= _:=by
        let L:=fun j:Fin m=> fun x:Site n=> cell (d j) x * ↑(Exterior.d 1 n ((i j).1+X,(i j).2) (x,a j))
        rw [← Fintype.prod_sum L]; simp only [L]; simp_rw [on_plane (hp _)]; ring
lemma cwrap(V:DialT n m)(x:Site n): cell (∑ i,V i) x=∏ i,cell (V i) x:=by
 have he (v w:Site n):cell (v+w) x=cell v x*cell w x:=by rw [cell_duality (v+w),cell_add,cell_duality x v,cell_duality x w]
 suffices h:∀ s:Finset (Fin m), cell (∑ i∈s,V i) x= ∏ i∈s,cell (V i) x from h _
 intro s; induction s using Finset.induction_on with
 | empty=>simp only [sum_empty,prod_empty]; rw [cell_duality,cell_origin]
 | @insert i S hi ih=>rw [sum_insert hi,prod_insert hi, he,ih]
lemma vars {v:Axis→ℝ}{k:Site n}(h: Push.Loops.Matches (axes v) k)(u:DialT n m):
 let d:= Fin.cons (k-∑ i,u i) u
 (∑ i,d i)=k ∧ (∀ i,Push.Loops.Matches (cardR v (tollX u) i) (d i)):=by
 intro d; constructor; rw [Fin.sum_univ_succ]; simp [d]
 intro i; induction i using Fin.cases with
 | zero=>
    let X:=fun i:Fin m=> (mon (u i)); have he(s:Finset (Fin m)): Push.Loops.Matches (∑ i∈s,X i) (∑ i∈s,u i):=by induction s using Finset.induction_on with
      | empty=> simp only [sum_empty]; simpa using mon_matches (0:Site n)
      | @insert i s hp ih=> rw [sum_insert hp,sum_insert hp]; exact (mon_matches ..).add ih
    unfold cardR d; rw [Fin.cons_zero,Fin.cons_zero,Braid.twist,missing,add_comm, sub_eq_add_neg]; exact h.add (he _).neg
 | succ i=>simp only [cardR,d,Fin.cons_succ,Fin.cons_succ]; exact mon_matches (u i)
end YM.CF.Rel
