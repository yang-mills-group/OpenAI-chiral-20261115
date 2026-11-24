import YM.CF.Rel.Seam
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
open Cube
section earlier
variable {F:FileM (More n) G}(p:LayerP n F)
private lemma tr_add(x y:Site n)(v:Config G n): Lattice.translate x (Lattice.translate y v)=Lattice.translate (x+y) v:=by ext1 i; change v (_,_)= v (_,_); rw [add_assoc]
include p
def pose (F:FileM (More n) G)(x y:Site (More n)): SpaceX G (More n):= F (x+y) ∘ Lattice.translate (-y)
lemma pose_h (x y:Site (More n))(u:Site n): pose F x y=pose F x (y+(assembly n).embed u):=by
 unfold pose; rw [←add_assoc,p]; ext1 v; simp only [Function.comp_apply,tr_add]; congr 2; abel
lemma pose_t(x:Site (More n)): F x ∘ Lattice.translate (-x) = F (logo n ((assembly n).residue x)) ∘ Lattice.translate (-logo n ((assembly n).residue x)) :=by
 let o:=logo n ((assembly n).residue x); have h:=pose_h p 0 o ((assembly n).parent x); rw [show o+(assembly n).embed ((assembly n).parent x)=x from (add_comm ..).trans ((assembly n).unpack_at x)] at h; simpa [pose] using h.symm
lemma restoreX (d:Charm)(x:Site (More n)) : laidC d n F x= massX⁻¹ • ∑ i:Charm, cell d i • pose F x (logo n i):=by
 ext1 y; unfold laidC Sean reel; simp only [Pi.smul_apply,Finset.sum_apply,Function.comp_apply,smul_eq_mul]; let V: Charm:= (assembly n).residue x; change _ * (massX⁻¹*∑ i,cell d i* (F (logo _ i) ∘ Lattice.translate (-logo n i)) (Lattice.translate x y))=_
 rw [mul_left_comm (pulseP _ _),mul_sum]; congr 1; rw [← Equiv.sum_comp (Equiv.addLeft (V:Charm)) (fun i=>pulseP (gammaT n d) x * (cell d i * (F (logo n i) ∘ Lattice.translate (-logo n i)) (Lattice.translate x y)))]; apply sum_congr rfl; intro i _; let j:= x+logo n i
 have hj: V+i=(assembly n).residue j:=by unfold V j; rw [map_add,show (assembly n).residue (logo n i)= i from ((assembly n).residue_wrap _).trans (wrap_lift _)]; rfl
 have hp : pulseP (gammaT n d) x*cell d (V+i)=cell d i:=by rw [pulseP,gamma_pay,cell_add]; exact inv_mul_cancel_left₀ (cell_ne _ _) _
 rw [←mul_assoc (pulseP _ _), show Equiv.addLeft (V: Charm) i= V+i from rfl,hp,hj,← pose_t p j]; simp only [Function.comp_apply,tr_add,pose]; change _ * F j _= _ * F j _; rw [show -j+x= -(logo n i) from by unfold j; abel]
end earlier
-- Prox under moving
variable {F:FileM n G}
def loanX (f: SpaceX G n)(i:Site n):= f ∘ Lattice.translate i
lemma shape_m(y:Site n)(x: Fin m→ InputZ G n)(f:SpaceX G n)(h:ContDiffAt ℝ m (satX f) 0): cake m (satX (loanX f y)) x=cake m (satX f) (fun i=> te (x i) y):=by
 let L:=tagT G y; rw [show satX (loanX f y)=(satX f) ∘ L from funext fun i=>congr_arg f (trn y i).symm,cake,Push.Uniform.iter_lin_at (L:=L) ((map_zero L).symm ▸ h),map_zero]; unfold cake; rfl
end YM.CF.Rel
