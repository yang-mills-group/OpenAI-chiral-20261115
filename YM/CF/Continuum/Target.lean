import YM.CF.Continuum.Flags

/-!
# A test that distinguishes the free Weyl chiralities

Select three different spatial components, all points along axis 3 (the time
axis). These will be honest onsite bosonic bilinears, including *all* colors in
a generation/species choice. For one or two currents the free comparison at
temporal separation cannot tell the two Weyl hands by these tests. Three
(spatial) can: for a comparator replacing min by plus in the propagator and
exchanging the two Spin-sets in everything, it changes sign. `dexPrice_*` below
computes that template. This is a Wick-window computation, not a chirality
proof in interacting continuum.
-/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter Metric Finset Fock Lattice Lat Rush Cube SU Scroll Spire Tulip Mir Mir.Trip Phase RP
open Onyx Flare Emu Dial Ember Kea Jill Fir
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
open YM.Stationary (Gaia)

abbrev corner (t : ℝ) : Gaia := EuclideanSpace.single (3:Axis) t
abbrev kernel (t : ℝ) : ℂ := (((Real.pi^2*|t|^4)⁻¹*t:ℝ):ℂ)
lemma kernel_pos {t : ℝ} (h : 0<t) : 0<(kernel t).re := by unfold kernel; rw [Complex.ofReal_re]; positivity
lemma kernel_real (t : ℝ) : star (kernel t)=kernel t :=by simp [kernel]
lemma kernel_neg (t : ℝ) : kernel (-t) = -kernel t := by simp [kernel]

lemma corner_sub (t u : ℝ) : corner t-corner u=corner (t-u) := by ext j; by_cases h:j=3; subst j; simp [corner]; simp [corner,h]

private lemma corner_clifford (t : ℝ) : (∑ i:Axis,((corner t) i:ℂ) • gammaOp i)=(t:ℂ) • gammaOp 3 :=by
  rw [sum_eq_single (3:Axis)]; · simp [corner]
  · intro i _ h; simp [corner,h]
  simp

abbrev upSpin (i : Fin 2):SpinIdx:= i.castAdd 2
abbrev dnSpin (i : Fin 2):SpinIdx:= i.natAdd 2
lemma up_half (i : Fin 2): upSpin i ∈ plusHalf := by fin_cases i <;> decide
lemma dn_half (i : Fin 2): dnSpin i ∉ plusHalf := by fin_cases i <;> decide

def index (x : Family)(i j : Fin 2) : Component := ⟨x,upSpin i,dnSpin j,up_half i,dn_half j⟩
abbrev alpha (m : Axis) (i j : Fin 2) := gammaOp m (upSpin i) (dnSpin j)

private lemma time_block (i j : Fin 2) : gammaOp 3 (upSpin i) (dnSpin j)=(if i=j then 1 else 0) := by fin_cases i<;>fin_cases j<;>norm_num [gammaOp,dnSpin,upSpin] <;> rfl
private lemma block_time (i j : Fin 2) : gammaOp 3 (dnSpin i) (upSpin j)=(if i=j then 1 else 0) := by fin_cases i<;>fin_cases j<;>norm_num [gammaOp,dnSpin,upSpin] <;> rfl
private lemma weight_select : Aop = cutM plusHalf := Adef.trans raising.symm

lemma pencil_time (t : ℝ)(i j : Fin 2) : pencil (corner t) (dnSpin i) (upSpin j)=if i=j then kernel t else 0 := by
  rw [pencil,gleamV,corner_clifford]; have h : (minA * gammaOp 3) (dnSpin i) (upSpin j)=if i=j then 1 else 0 := by rw [minA, weight_select,sub_mul,one_mul, Matrix.sub_apply, cutM,Matrix.diagonal_mul, if_neg (dn_half i),zero_mul,sub_zero]; exact block_time ..
  rw [Matrix.mul_smul, Matrix.smul_apply,Matrix.smul_apply,h]; split_ifs <;> simp [corner,kernel, Complex.real_smul, mul_assoc, Real.norm_eq_abs]

private lemma sPrice(x:Family)(t u v:ℝ)(i j i' j' i'' j'':Fin 2):sixM (corner t) (corner u) (corner v) (index x i j) (index x i' j') (index x i'' j'') =
    ((if j=i' ∧ j'=i'' ∧ j''=i then 1 else 0)-(if j=i'' ∧ j'=i ∧ j''=i' then 1 else 0))*kernel (t-u)*kernel (u-v)*kernel (v-t) := by
  simp only [sixM,index,corner_sub,pencil_time];
  rw [show t-v= -(v-t) from (neg_sub ..).symm,show u-t= -(t-u) from (neg_sub ..).symm,show v-u= -(u-v) from (neg_sub ..).symm]; simp_rw [kernel_neg]; 
  let X := kernel (t-u); let Y := kernel (u-v); let Z := kernel (v-t)
  rw [sub_mul,sub_mul,sub_mul]; have he : (if j=i' then X else 0)*(if j'=i'' then Y else 0)*(if j''=i then Z else 0)=(if j=i' ∧ j'=i'' ∧ j''=i then 1 else 0)*X*Y*Z := by simp only [ite_and]; split_ifs <;> ring
  have he' : (if j=i'' then -Z else 0)*(if j'=i then -X else 0)*(if j''=i' then -Y else 0)= -((if j=i'' ∧ j'=i ∧ j''=i' then 1 else 0)*X*Y*Z):=by simp only [ite_and]; split_ifs <;> ring
  rw [he,he']; rfl -- tune add-sub

def wedgeThree (m n s : Axis)(x : Family)(f : Component → Component → Component → ℂ) :=
  ∑ i:Fin 2,∑ j:Fin 2,∑ k:Fin 2,∑ l:Fin 2,∑ p:Fin 2,∑ q:Fin 2, (alpha m i j*alpha n k l*alpha s p q)*f (index x i j) (index x k l) (index x p q)

private lemma a0(i j):alpha 0 i j=if i=j then 0 else -Complex.I:=by fin_cases i<;>fin_cases j<;>norm_num [alpha,dnSpin,upSpin,gammaOp]<;> rfl
private lemma a1(i j):alpha 1 i j=if i=j then 0 else if i=0 then -1 else 1:=by fin_cases i<;>fin_cases j<;>norm_num [alpha,dnSpin,upSpin,gammaOp]<;> rfl
private lemma a2(i j):alpha 2 i j=if i=j then (if i=0 then -Complex.I else Complex.I) else 0:=by fin_cases i<;>fin_cases j<;>norm_num [alpha,dnSpin,upSpin,gammaOp]<;> rfl
lemma axis_budget (x : Family) (v : ℂ) (t u w : ℝ) : wedgeThree 0 1 2 x (fun i j k=>v*sixM (corner t) (corner u) (corner w) i j k) = -4 * v * kernel (t-u) * kernel (u-w)*kernel (w-t) := by
  unfold wedgeThree; simp_rw [sPrice,a0,a1,a2]
  norm_num [Fin.sum_univ_succ]
  ring
-- comparator is a template *not added to the FiniteGaugeData algebra*.
private def dexD (t : Gaia) : Op SpinIdx := ( (Real.pi^2*‖t‖^4)⁻¹:ℝ) • (Aop*∑ m:Axis,(t m:ℂ) • gammaOp m)
private abbrev per(i j : Fin 2)(u : Gaia):ℂ:=dexD u (upSpin i) (dnSpin j)
private lemma dex_time (t : ℝ)(i j : Fin 2) : per i j (corner t)=pencil (corner t) (dnSpin i) (upSpin j) := by
  unfold per dexD; have hx : (Aop*gammaOp 3) (upSpin i) (dnSpin j) = (if i=j then 1 else 0) := by rw [weight_select,cutM, Matrix.diagonal_mul,if_pos (up_half i),one_mul,time_block]
  rw [pencil_time,corner_clifford, Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply,hx]; split_ifs <;> simp [corner,kernel, Complex.real_smul,mul_assoc,Real.norm_eq_abs]
private abbrev alpR (m : Axis) (i j : Fin 2) := gammaOp m (dnSpin i) (upSpin j)
private lemma mars(m : Axis)(h : m≠3)(i j : Fin 2): alpR m i j= -alpha m i j :=by
  fin_cases m <;> try contradiction
  all_goals fin_cases i <;> fin_cases j<;> norm_num [alpha,gammaOp,alpR,dnSpin,upSpin] <;> first | rfl | exact (neg_neg Complex.I).symm | exact (neg_neg (1:ℂ)).symm | exact (neg_zero).symm -- tune
private def tDex (x y z : Gaia)(i j k l p q : Fin 2) := per j k (x-y)*per l p (y-z)*per q i (z-x)+per j p (x-z)*per l i (y-x)*per q k (z-y)
private lemma tDex_eq (a : Family)(i j k l p q : Fin 2)(x y z : ℝ): tDex (corner x) (corner y) (corner z) i j k l p q=sixM (corner x) (corner y) (corner z) (index a i j) (index a k l) (index a p q) :=by
   unfold tDex sixM index; simp only [corner_sub,dex_time]
/-- Opposite hand six-leg Wick price, including reversed alpha convention. -/
def dexPrice (x y z : Gaia)(v : ℂ)(m n s : Axis) :=
  ∑ i:Fin 2,∑ j:Fin 2,∑ k:Fin 2,∑ l:Fin 2,∑ p:Fin 2,∑ q:Fin 2, (alpR m i j*alpR n k l*alpR s p q)*(v*tDex x y z i j k l p q)
lemma dexPrice_flip (F : Family)(m n r : Axis)(h : m≠3)(g : n≠3)(p : r≠3)(v : ℂ)(x y z : ℝ): dexPrice (corner x) (corner y) (corner z) v m n r = -wedgeThree m n r F (fun a b c=>v*sixM (corner x) (corner y) (corner z) a b c) :=by
  unfold dexPrice wedgeThree
  simp only [mars m h,mars n g,mars r p,tDex_eq F, neg_mul,mul_neg,neg_neg,sum_neg_distrib]
lemma dexPrice_cost (v : ℂ)(x y z : ℝ): dexPrice (corner x) (corner y) (corner z) v 0 1 2=4*v*kernel (x-y)*kernel (y-z)*kernel (z-x):=by
  rw [dexPrice_flip (0,false) _ _ _ (by decide) (by decide) (by decide),axis_budget]; ring

def signedCost (x : Family)(t u v : ℝ):ℝ:=4 *dimf x * (kernel (u-t)).re*(kernel (v-u)).re*(kernel (v-t)).re
lemma dimf_pos (x : Family) : 0<dimf x:=by unfold dimf; split_ifs <;> omega
lemma cost_pos (x : Family){t u v : ℝ}(h : t<u)(w : u<v) : 0<signedCost x t u v := by unfold signedCost; have hx:=kernel_pos (sub_pos.mpr h); have hz:=kernel_pos (sub_pos.mpr w); have hw:=kernel_pos (sub_pos.mpr (h.trans w)); have ht:=dimf_pos x; positivity
lemma dexPrice_sign (x : Family) (t u v : ℝ) : dexPrice (corner t) (corner u) (corner v) (dimf x:ℂ) 0 1 2=signedCost x t u v := by rw [dexPrice_cost,show kernel (t-u)=-(kernel (u-t)) from (neg_sub u t) ▸ (kernel_neg (u-t)), show kernel (u-v)=-(kernel (v-u)) from (neg_sub v u) ▸ (kernel_neg (v-u)), signedCost]; simp only [kernel, Complex.ofReal_re]; push_cast; simp
lemma left_price (x : Family)(t u v : ℝ) : wedgeThree 0 1 2 x (fun a b c=>(dimf x:ℂ)*sixM (corner t) (corner u) (corner v) a b c)=-↑(signedCost x t u v) :=by
  rw [←dexPrice_sign, dexPrice_flip x _ _ _ (by decide) (by decide) (by decide)]; exact (neg_neg _).symm
end YM.CF.Window
