import YM.SU5.Voyager.Flint
import YM.Heat.Duration
/-! # Pocket of coordinates. SNAG on THIS orbit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Caino
open Function Filter Set Metric Complex Finset LinearMap MeasureTheory Measure
open Boundary Boundary.Probe Spectral Orbit
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators Classical
variable {I:Type*}[Fintype I](L:I↪Axis)
abbrev Terrain (I:Type*):= EuclideanSpace ℝ I
def terrain (x:E4):Terrain I:=WithLp.toLp 2 (fun i:I=> x (L i))
def vast (r:Terrain I): E4:= ∑ i:I,(r i) • YM.basis (L i)
lemma terrain_cont : Continuous (terrain L):= by unfold terrain; fun_prop
lemma vast_cont : Continuous (vast L):=by unfold vast; fun_prop
lemma vast_assoc (A B:Terrain I): vast L (A+B)=vast L A + vast L B:= by unfold vast; simp only [PiLp.add_apply, add_smul,sum_add_distrib]
lemma bridge_bill (r:Terrain I)(x:E4): inner ℝ (vast L r) x=inner ℝ r (terrain L x):=by unfold vast terrain; simp [sum_inner, real_inner_smul_left, PiLp.inner_apply]
lemma optic (r:Terrain I)(i:Axis): (vast L r) i= ∑ k:I, r k * if i=L k then 1 else 0:=by
 rw [← YM.basis_inner, vast, inner_sum]; apply sum_congr rfl; intro a _
 rw [real_inner_smul_right, YM.basis_inner]; simp only [YM.basis_eq]
lemma reach (r:Terrain I)(i:I): (vast L r) (L i)= r i:=by rw [optic, Finset.sum_eq_single i]; simp; intro j _ p; simp [show L i ≠ L j from fun e=>p (L.injective e.symm)]; simp -- tune
variable [DecidableEq I]
abbrev sight (p:ℝ)(i:I):= EuclideanSpace.single i p
lemma shine_s (t:ℝ)(i:I)(k:I): sight t i k= if i=k then t else 0:=by simp [sight,PiLp.single_apply,eq_comm]
lemma sole_column (u:ℝ)(i:I): vast L (sight u i)=u • YM.basis (L i):=by
 rw [vast, Finset.sum_eq_single i]; simp; intro j _ p; simp [shine_s u i j,p,Ne.symm p]; simp -- tune
-- charge brightest angle
lemma shinAngle_bound [Nonempty I] (r:Terrain I): ∃ k:I, ‖r‖ ≤ Fintype.card I* |r k|:=by
 obtain ⟨i,h,g⟩:=Finset.exists_max_image univ (fun i=>|r i|) Finset.univ_nonempty; refine ⟨i,?_⟩
 have hx:r=∑ i:I,sight (r i) i:=by apply ext_inner_right ℝ; intro x; rw [sum_inner]; simp [sight,EuclideanSpace.inner_single_left,PiLp.inner_apply];
 have hs(i:I): ‖sight (r i) i‖=|r i|:=by simp [sight,Real.norm_eq_abs]
 conv_lhs=>rw [hx]
 refine (norm_sum_le _ _).trans (le_trans (sum_le_sum (g:=fun j=>|r i|) (fun j hj=>(hs j).trans_le (g _ hj))) ?_); simp
omit [DecidableEq I]
variable {H:Hilbert} (T:Orbit H E4)
def bars : Orbit H (Terrain I) where
 translation r:=T.translation (vast L r)
 origin:= by rw [show vast L 0=0 from (by simp [vast]), T.origin]
 sends a b:=by rw [T.sends,vast_assoc]
 unitary _ := T.unitary _
 moves x:=(T.moves x).comp (vast_cont L)
def sails(P:PVM H E4) : PVM H (Terrain I):= P.route (terrain L) (terrain_cont L).measurable
lemma barSpecs(P:PVM H E4)(p:T.Spectrum P): (bars L T).Spectrum (sails L P):=by
 intro x r; change charFun (map (terrain L) _) r = _; rw [charFun_apply, integral_map (terrain_cont L|>.aemeasurable) (by fun_prop)]; change _=inner ℂ x (T.translation (vast L r) x); rw [← p,charFun_apply]; exact integral_congr_ae (ae_of_all _ fun x'=>by dsimp only; rw [real_inner_comm r (terrain L x'), ← bridge_bill,real_inner_comm (vast L r) x'])
end YM.Caino
#print axioms YM.Caino.barSpecs
