import YM.CF.Rue.Coin
import YM.CF.Hake.Hula
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
attribute [local instance] opCStarAlgebra
open Hake Stilo Jet
variable {n : Type*} [LinearOrder n] [Fintype n]
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{K u: Raid n}{X X':E→↥(Dough n)}{k:ℕ}
def bottles(c:Raid n):ℕ→Raid n
 | 0=> Pi.single ∅ 1
 | i+1=>skirt (bottles c i) c
abbrev Rigid(f:E→↥(Dough n))(k:ℕ)(x:E)(c:Raid n):= Woody k (fun x=>(f x).val) x c
lemma boats(p:Rigid X k x u)(m:ℕ):Rigid (fun x=>X x^m) k x (bottles u m):=by
 induction m with | zero=> simp only [pow_zero,bottles]; exact Woody.uniV _
                  | succ i ih=> simp_rw [pow_succ,bottles]; exact ih.pairP p
lemma b_nn(p:0≤u)(m:ℕ):0≤bottles u m:=by
 induction m with | zero=> intro i; rw [bottles,Pi.single_apply]; split_ifs <;> simp
                  | succ m ih=> exact skirtPos _ _ ih p
lemma brew_p(h:Turner K)(hp:0≤u)(m:ℕ): joinV K (bottles u m)≤(joinV K u)^m:=by
 induction m with | zero=> rw [pow_zero,bottles, joinVone h]; exact h.red
                  | succ m ih=> rw [pow_succ,bottles]; exact (turnS h _ _ (b_nn hp m) hp).trans (mul_le_mul_of_nonneg_right ih (sum_nonneg fun i _=> mul_nonneg (h.fee i) (hp i)))
abbrev beat(m:ℕ){n':Type*}[NormedRing n'][NormedAlgebra ℝ n'](A:n'):= (m.factorial:ℝ)⁻¹ • A^m
abbrev bait(m:ℕ)(u:Raid n): Raid n:= (m.factorial:ℝ)⁻¹ • bottles u m
lemma covering (c:ℝ)(h:Rigid X k x u):Rigid (fun t=> c • X t) k x (‖c‖ • u):=by
 refine ⟨?_,fun j=> ?_⟩; exact Eventually.of_forall fun x=> (fineShape _).allP
 have hp:= (h.haveP j).σ (↑c); simp only [Complex.norm_real] at hp; apply hp.germ; filter_upwards with y; exact Eq.symm (show Pastry.crumb (c • (X y).val) j= _ from (Pastry.crumb_scaleR ..).trans (Complex.coe_smul c _).symm)
-- field canon
lemma rung(u:Raid n)(k:ℕ)(s:ℕ)(p:Rigid X k x u):Rigid (fun i=> beat s (X i)) k x (bait s u):=by
 unfold bait; convert! covering _ (boats p s) using 1; rw [Real.norm_of_nonneg (by positivity)]
lemma worths(h:Turner K)(p:0≤u)(i:ℕ):joinV K (bait i u)≤ beat i (joinV K u):=by
 rw [bait]; unfold joinV; simp only [Pi.smul_apply,smul_eq_mul, mul_left_comm _ ((i.factorial:ℝ)⁻¹),←mul_sum]; exact mul_le_mul_of_nonneg_left (brew_p h p i) (by positivity)
lemma showK : Turner (n:=n) (fun _=>1):=⟨fun _=>zero_le_one,le_rfl,fun _ _ _=>by norm_num⟩
lemma sheen {L:Raid n}(g:0 ≤ L)(i:Finset n): L i≤ joinV (fun _=>1) L:=by unfold joinV; simp only [one_mul]; exact single_le_sum (f:=L) (fun i _=>g i) (mem_univ _)
def saber (u:Raid n)(l:ℕ):Raid n:= ∑' m,bait (m+l) u
lemma bait_p(p:0 ≤ u)(m:ℕ):0 ≤ bait m u:=fun i=>mul_nonneg (by positivity : 0 ≤ (m.factorial:ℝ)⁻¹) (b_nn p m i)
lemma bait_s(p:0 ≤ u): Summable (fun i=>bait i u):= by
 rw [Pi.summable]; intro i; exact Summable.of_norm_bounded (NormedSpace.expSeries_summable' (𝕂:=ℝ) (joinV (fun _=>1) u)) fun j=> by rw [Real.norm_of_nonneg (bait_p p j i)]; exact (sheen (bait_p p j) i).trans (worths showK p j)
lemma saber_r(l:ℕ)(p:0 ≤ u)(B:Raid n)(g: Turner B): (∀ i,0 ≤ saber u l i) ∧ joinV B (saber u l)≤ ∑' m, beat (m+l) (joinV B u):=by
 have hg := (summable_nat_add_iff l).mpr (bait_s p)
 let L': Raid n →ₗ[ℝ] ℝ:= ⟨⟨joinV B,fun _ _=>joinVadd _ _ ⟩,fun v w=> by simp [joinV,smul_eq_mul,Finset.mul_sum,mul_left_comm]⟩
 let L:=L'.toContinuousLinearMap; have ht:= L.hasSum hg.hasSum; refine ⟨fun i=>?_ ,?_⟩
 · have hx:= ht; unfold saber; rw [tsum_apply hg]; exact tsum_nonneg (fun i'=>bait_p p _ i)
 exact hasSum_le (fun i=> worths g p (i+l)) ht (((summable_nat_add_iff l).mpr (NormedSpace.expSeries_summable' (𝕂:=ℝ) (joinV B u))).hasSum)
end YM.CF.Rue
