import Anomaly.Ward.Masked
import Zephyr.Chern.Bends
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
/-!
Witness of the vector in **constant** linear curl tests. Identify it with
locally probed quadratic. Crafted determinant projection handled elsewhere.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
open Nacre Next.Rank.Spindle LampP Exterior Precision Wilson _root_.Zephyr.Chern
namespace SpectrumQ
open SU
section fro
open scoped Matrix.Norms.Frobenius
-- exact exp stripe without assumption of lying in an arbitrarily small chart even off germ.
def fluteQ : SU.group.Mat:=Matrix.diagonal (fun i=>Complex.I * (dye.val i:ℂ))
lemma flute_exp (t:ℝ): exp (t • fluteQ)=group.mat (arc t):=by
 unfold fluteQ
 rw [← Matrix.diagonal_smul,Matrix.exp_diagonal]; change Matrix.diagonal _= Matrix.diagonal _; congr 1; funext i
 -- Normalize phase α via project P
 simp [Complex.exp_eq_exp_ℂ] -- tune
 rw [←Complex.exp_eq_exp_ℂ]
 change Complex.exp _=Complex.exp _; congr 1; change _=((t*dye.val i:ℝ):ℂ) * _; push_cast; ring
lemma flute_mem: fluteQ∈ SU.group.lie:=(SU.group.mem_lie).mpr fun i=> ⟨arc i, Eq.symm (flute_exp i)⟩
def rayC : SU.group.Color := group.projectColor fluteQ
lemma face_ray(t:ℝ): SU.group.lieExp (t • rayC)=arc t := group.mat_injective (by rw [group.mat_lieExp,map_smul,show group.colorMat rayC=fluteQ from group.colorMat_project_self flute_mem,flute_exp])
end fro
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
-- helpers for pressure. constant metric pricing convention.
def translateℓ (p: RG.Directions group N) : fieldDir group N 1:= fun i=>p (i.1, axisEquiv.symm i.2)
lemma translate_collect(p: RG.Directions group N): collect group (translateℓ p)=p := by funext i; unfold collect translateℓ; rw [show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _]
abbrev pattern (A: Angles N):= translateℓ (fun i=> A i • rayC)
lemma march (A:Angles N)(t:ℝ): represent (t • pattern A)= petals A t:=by
 rw [LampP.survey]; unfold pattern; rw [translate_collect]; funext j; simp only [increment,Pi.one_apply,Pi.smul_apply,mul_one,smul_smul,mul_comm t,face_ray,_root_.Zephyr.Chern.petals]

-- κ(F) vector ∈ determinant. explicit constant value on pricing path.
def letter (i: PlaqAxes): SU.group.Color:= flux (step i.val.1) (step i.val.2) • rayC
local notation "U" => pattern (stream N)
lemma agreesSD {b:ℕ}(p:4*b+4 < N.val)(x: Seat N)(hx:x∈ halo b {node (0:Site N)})(i:PlaqAxes) : Work.F03.faceCurl (x,i) U= letter i:=by
 change dColor _ _ _ _ _=_; rw [← fundamental]; simp only [pattern, translate_collect, square, linkSum, Lattice.Step.used, Lattice.Step.vec, negDir, posDir,Bool.false_eq_true,↓reduceIte,add_zero,stream]
 let a:=i.val.1; let b':=i.val.2
 have ht:x+step a+step b'-step a=x+step b':=by abel
 have hv:x+step a+step b'+-step a=x+step b':=by abel
 rw [ht,hv,add_sub_cancel_right]
 have hs(z:Axis): Zephyr.Chern.rel (x+step z) = Zephyr.Chern.rel x+step z:=by
    rw [←wrap_step (More N) z]; apply rel_add (m:=b); rw [step_size]; omega
    rw [separation_comm]; exact doors _|>.1 (show x∈ Next.Rank.Spindle.patch b 1 from by rw [node,map_zero,zero_add] at hx; exact hx) -- tune
 -- omega
 rw [hs,hs]; simp only [twistAt,flux_left, neg_smul, letter]; rw [flux_switch (step b') (step a)] -- tune negative smul
 -- tune
 module
variable {b k m:ℕ}{d s α C M w:ℝ}{P:BudgetPoint}{K:Loom N}{X:SOp N}{T:tableQ group (More N) ℂ} (R:Knit X (node (0:Site N)) b d α M C w m T) (L:mintQ α C d m) (H:Roof N s d k K)(hb:b+k+10 ≤ P.B)(hp:P.threshold ≤ s)
include R L H hb hp
lemma hears (A:StemA N)(r:2 ≤ m) : let Y:=pattern A; bud (traceMeter P K 0 X ∘ petals A) 2=tariff T (receipt Y):=by
 intro W; let f:=stepQ X; let V:= collect group W; let Q(t:ℝ):= t • V
 have ht:Tendsto Q (𝓝 0) (𝓝 0):=by unfold Q; simpa using! (show Continuous (fun t:ℝ=>t • V) from by fun_prop).tendsto 0
 have hk := ((R.circle 0 (norm_zero.trans_lt L.1)).order r).smooth
 have hP:traceMeter P K (0:Site N) X ∘ petals A =ᶠ[𝓝 0] fun i=> f (Q i)+rawQ X 1:=by
    have hl:∀ᶠ z in 𝓝 0,pingS P.threshold (halo P.B {node (0:Site N)}) (petals A z):=by
       have h: {U':Pane N|pingS P.threshold (halo P.B {node (0:Site N)}) U'}∈ 𝓝 (petals A 0):=ping_o.mem_nhds (by rw [petal_idle]; exact ping_f P _)
       exact (cont_petal A).continuousAt.eventually h -- uRef remove
    filter_upwards [hl,ht.norm.eventually (gt_mem_nhds (by rw [norm_zero]; exact L.1))] with i hu hx
    have he:petals A i=increment 1 (Q i):=by rw [← march A i,LampP.survey]
    exact (brightEq R H hb hp hu (fun u p j=> congrFun he u) (L.2.2.2.1 _ hx)).trans (sub_add_cancel ..).symm
 have hh:bud (traceMeter P K (0:Site N) X ∘ petals A)=_:= bud_congr hP; have h2:ContDiffAt ℝ (2:ℕ) (f ∘ Q) 0:=by apply (show ContDiffAt ℝ (2:ℕ) f (Q 0) from by rw [show Q 0=0 from zero_smul ..]; exact hk).comp 0; unfold Q; fun_prop
 rw [hh,R.poses, trim, cake]; let F(t:ℝ):= f (Q t)+rawQ X 1
 change deriv (deriv F) _ / 2= _; rw [←iteratedDeriv_one (f:=F),← iteratedDeriv_succ]; rw [show F=(f ∘ Q)+(fun _=>rawQ X 1) from rfl,iteratedDeriv_add h2 contDiffAt_const]; unfold Tensor.diagonal; simp only [_root_.smul_apply]; change _= (Nat.factorial 2:ℝ)⁻¹ • ((iteratedFDeriv ℝ 2 f 0) (fun _=>V)); rw [show iteratedFDeriv ℝ 2 f 0 (fun _=>V)=iteratedDeriv 2 (f ∘ Q) 0 from (?_)] -- may need unfold f V
 · norm_num [Complex.real_smul, iteratedDeriv_const, Nat.factorial,_root_.smul_apply,div_eq_mul_inv]; ring
 exact (upon V f _ hk).symm
def frameμ (q: TrackKey SU.group (More N)) := letter q.1.2 q.2
omit L H hb hp
lemma linearized (p: 4*b+4 < N.val): tariff T (receipt U)= tariff T frameμ:=by
 apply sum_congr rfl; intro i _; by_cases h:T i=0
 · rw [h,smul_zero,smul_zero]
 apply congrArg (· • T i); apply prod_congr rfl; intro j _; exact congr_arg (fun z:SU.group.Color=> z (i j).2) (agreesSD p _ (R.inHall i h j) _)
end SpectrumQ
end YM.CF.Swell.Sonar
