/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Summit.Crews
import YM.Next.STATIONARY.Shape.ClassicalMatch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior Finset MeasureTheory
  Push Push.Uniform
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {c f:Side} {d k n l:ℕ}{q:Clip}{R:PathData G}{σ C a:ℝ}
def dimA(T:Atom G k):Atom G k:={T with coeff:= fun _=>0}
lemma dimB (T: Atom G k): (dimA T).budget σ=0:=by simp [dimA,Atom.budget,Atom.magnitude]
lemma dimU(T: Atom G k)(U:Config G f)(x:Site f): (dimA T).unmasked U x=0:=by simp [dimA,Atom.unmasked,Atom.poly]
def grainA(R:PathData G)(l:ℕ):PathData G:=⟨fun p i=> (if (R.row p i).2.length≤l then (R.row p i).1 else 0,(R.row p i).2),R.loop,fun i=> if (R.cubic i).length≤l then R.cubic i else dimA (R.cubic i),fun i=>if (R.quartic i).length≤l then R.quartic i else dimA (R.quartic i)⟩
variable {ι:Type}
def farther (p:ι→ Prop)(A:ι→ Atom G k):ι→Atom G k:=fun i=>by classical exact if p i then dimA (A i) else A i
lemma farm {p:ι→ Prop}{A:ι→ Atom G k}(h: ∀ i, ¬p i→n≤ (A i).length)(hs:SumBudget (fun i=>(A i).budget σ) C)(hv:0 ≤ σ):
 SumBudget (fun i=>(farther p A i).budget (σ/2)) (Real.exp (-(σ/2)*n)*C):=by
 let u i:=(farther p A i).budget (σ/2); let g:=Real.exp (-(σ/2)*n); let Z i:=(A i).budget σ
 have hp i :0≤u i:=by unfold u Atom.budget Atom.magnitude; positivity
 have he i:u i ≤ g*Z i:=by
    unfold u farther; split
    next hx=> rw [dimB]; exact mul_nonneg (Real.exp_pos _).le (hs.1 _)
    next hx=>
      have hi : (n:ℝ)≤(A i).length:= by exact_mod_cast h i hx
      unfold Z Atom.budget g; rw [mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by unfold Atom.magnitude; positivity); nlinarith only [mul_le_mul_of_nonneg_left hi hv]
 have hb:= hs.2.1.mul_left g; have hf : Summable u:=Summable.of_nonneg_of_le hp he hb
 exact ⟨hp,hf,(hf.tsum_le_tsum he hb).trans ((tsum_mul_left).trans_le (mul_le_mul_of_nonneg_left hs.2.2 (Real.exp_pos _).le))⟩
def wink (R:PathData G)(l:ℕ)(j:Stationary.PairsIndex):Prop:= (R.row j.1 j.2.1).2.length≤l∧(R.row j.1 j.2.2).2.length≤l
lemma amo (h:R.Bounds q σ C a)(l:ℕ): Stationary.BankRows (grainA R l) σ C:=by
 intro i
 let Z j:= |(R.row i j).1| * Real.exp (σ*(R.row i j).2.length); let B k:=|( (grainA R l).row i k).1| * Real.exp (σ*((grainA R l).row i k).2.length)
 have ht k: B k≤Z k:=by unfold Z B grainA; dsimp only; split; rfl; simp; positivity
 have hs:= (h.rows i); have he k:0≤B k:=by unfold B; positivity
 have hu: Summable B:=Summable.of_nonneg_of_le he ht hs.2.1
 exact ⟨he,hu,(hu.tsum_le_tsum ht hs.2.1).trans hs.2.2⟩
lemma asume {α:Type}(R:α→ Atom G k)(p:0<σ)(h:SumBudget (fun i=>(R i).budget σ) C)(x:Site f)(U:Config G f): Summable fun i=> (R i).unmasked U x:= .of_norm_bounded (h.2.1.mul_right (2^k)) fun i=> ((R i).unmasked_bound U x).trans (mul_le_mul_of_nonneg_right ((R i).lower_budget σ p) (by positivity))
lemma aimed (p:Stationary.BankRows R σ C)(h:0<σ)(x:Site f)(U:Config G f): (∑' i,(Stationary.gramPath R i).unmasked U x)=∑ j,‖R.ell U (x,j)‖^2/2:=by
 let H i:=(Stationary.gramPath R i).unmasked U x; change (∑' i,H i) = _
 have hh : Summable H:= asume _ h (Stationary.gram_budget R p) x U
 rw [hh.tsum_prod,tsum_fintype]; refine Finset.sum_congr rfl fun i _=> ?_
 let F j:=R.ellTerms (x,i) j U; have hf : Summable F:= by
    apply Summable.of_norm_bounded ((p i).2.1.mul_right 2); intro j; unfold F PathData.ellTerms; rw [norm_smul]
    calc
      _ ≤ |(R.row i j).1| * 2 :=mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)
      _ ≤ _ :=by apply mul_le_mul_of_nonneg_right _ (by positivity); exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))
 have he j v: H (i,j,v)=inner ℝ (F j) (F v)/2:=Stationary.gram_eval R _ x U
 rw [(hh.prod_factor _).tsum_prod]; simp_rw [he,tsum_div_const]
 rw [← real_inner_self_eq_norm_sq]; simp_rw [show ∀ a, ∑' j, inner ℝ (F a) (F j)=inner ℝ (F a) (R.ell U (x,i)) from fun a=> ((innerSL ℝ (F a)).map_tsum hf).symm]
 congr 1; conv_lhs=> arg 1; intro i; rw [real_inner_comm]; skip
 exact ((innerSL ℝ (R.ell U (x,i))).map_tsum hf).symm
end YM.CF.Newt
