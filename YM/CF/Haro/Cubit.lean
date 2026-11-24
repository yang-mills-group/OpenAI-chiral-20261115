import YM.CF.Haro.Cargo
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
variable {i:Type*}[LinearOrder i][Fintype i]
def orbitPH(F: Pastry.ribbon i):Op i:= Matrix.of fun x y=>Prism.portB F.val (true,x) (false,y)
open Pastry
lemma ort(i':FC i)(x y:i): Prism.portB i' x y= -(Prism.portB i' y x):=by unfold Prism.portB; rw [eq_neg_of_add_eq_zero_left (put_put x y), act_neg, inner_neg_left]; -- tune
private lemma c_age(z:Bool)(x:ℂ): cSignX (!z) (-x)= -star (cSignX z x):=by cases z <;>simp [cSignX]
abbrev seaK (U:UNI i)(r:Bool)(b:Bool):= if r then thread (invFilm U) b else thread U b
private lemma harp(U:UNI i)(r b:Bool)(x:i)(F: LeanV i→ℂ):(∑ j:LeanV i,(Scree.spice U r).val (b,x) j*F j)=∑ j:i,(seaK U r b).val x j*F (b.xor r,j):=by
 rw [Fintype.sum_prod_type, sum_eq_single (b.xor r)]; apply sum_congr rfl; intro j _; cases b <;>cases r <;> simp [Scree.spice,seaK, ↓reduceIte, Scree.opBool,Pastry.closeV,jump_apply] -- tune
 intro a _ h; refine sum_eq_zero (fun i' _=>?_); cases a <;>cases r<;>cases b <;> first|exfalso; apply h; rfl|simp [Scree.spice, seaK,Scree.opBool, closeV, jump_apply]
 simp
lemma paral (T:Pastry.ribbon i)(q v:Bool)(U:UNI i): orbitPH (paintR q v U T)= Thera.jazz v (sings q U (orbitPH T)):=by
 ext x y; change Prism.portB _ _ _=_; rw [Prism.drawn]; let Z:= orbitPH T
 have hp(a):∑ l:LeanV i,(Scree.spice U v).val (false,y) l * cSignX (q.xor v) (Prism.portB T.val a l) = ∑ l:i,(seaK U v false).val y l *cSignX (q.xor v) (Prism.portB T.val a (false.xor v,l)):= harp U v false y _
 simp_rw [←Finset.mul_sum,hp]
 rw [harp]; cases v; swap
 · change (∑ j:i,(invFilm U).val x j*(∑ l:i,(ccU (invFilm U)).val y l * cSignX (q.xor true) (Prism.portB T.val (false,j) (true,l))))=(-star (sings q U Z)) x y
   have he(j l:i) : cSignX (q.xor true) (Prism.portB T.val (false,j) (true,l))= -star (cSignX q (Z l j)):=by rw [ort]; cases q <;>simp [Z,cSignX,orbitPH]

   have hi: (invFilm U).val=Complex.I • U.val:= Urn.filmG .. -- oops changed
   rw [singT,show star (twist U _)=twist U (star (windX q Z)) from (map_star ..).symm,twist_formula, Matrix.neg_apply,mul_assoc,Matrix.mul_apply]; simp only [Matrix.mul_apply, mul_sum,← Finset.sum_neg_distrib, he, ccU]; -- tune
   apply sum_congr rfl; intro j _; apply sum_congr rfl; intro b _; rw [hi]; change Complex.I*U.val x j * (star (Complex.I*U.val y b)*_) = -(U.val x j * (star (windX q Z b j)*star (U.val y b))); rw [show windX q Z b j= cSignX q (Z b j) from (by cases q <;> rfl),star_mul,show star Complex.I= -Complex.I from Complex.conj_I]; ring_nf; simp
 change (∑ j:i,U.val x j*(∑ l:i,(ccU U).val y l * cSignX (q.xor false) (Prism.portB T.val (true,j) (false,l))))= twist U _ x y
 rw [twist_formula,mul_assoc,Matrix.mul_apply]; simp_rw [Matrix.mul_apply]; apply sum_congr rfl; intro j _; congr 1; apply sum_congr rfl; intro l _; cases q <;> exact mul_comm ..
end YM.CF.Haro
