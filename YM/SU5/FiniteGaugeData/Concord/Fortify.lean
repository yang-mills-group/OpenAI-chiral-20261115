import YM.SU5.FiniteGaugeData.Concord.Cosponsor
/-! # Uniform mixed-scale estimates, support and evaluation on one Course (FiniteGaugeData election)

Compare ANY native palettes on a list of support boxes at contributing levels 0..s.
Factor includes the norm product (not on infinite tensor!, choose any presentation and sum
bounds, get also projective inf for the represented classes). Estimates include bounds for these
supplied palettes, their support & embeddings into actual Choreo at s (not just for total
read), and convergence of reader. Off guard placeholders useless; specify Ready etc. and validity
on row & period along Cone; scope is all actors on these boxes at these observing levels,
no claim about watching arbitrarily high levels s→∞. Sharp signed regulator, not its positive
heat comparison substitute, at exact (Λ.x) history. Use alignment separately for PSD.

Cost `spread` tracks cumulative support incl caps on aux mergings. For actual microscopic quote
(which can be reached when the horizon is paid) need NOT fit all enlarged supports at top;
torus `region`s use mod and locality back at the chosen observing resolution accounts for the
identification. Further evaluate if physical footprint at top is of interest. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale

namespace Meet
variable (Λ:Preparation)(l:ℕ)
section spread
variable (S:ℕ→Finset Cover)
-- stages cumulative
@[reducible] def spread : ℕ→ Finset Cover
  | 0=> S 0
  | n+1=>swept Λ l (spread n) ∪ S (n+1)
lemma spread_has (i:ℕ) : S i ⊆ spread Λ l S i := match i with
 | 0=> Subset.rfl
 | _+1=> Finset.subset_union_right
lemma spread_pays (i:ℕ): swept Λ l (spread Λ l S i) ⊆ spread Λ l S (i+1) := Finset.subset_union_left
-- notation
local notation "S'"=> spread Λ l S
variable (K:Calibration)
private def ascend (i:ℕ)(x : Palette (swept Λ l (spread Λ l S i)))(y:Palette (S (i+1))) : Palette (spread Λ l S (i+1)):= chorusMul K ((S') (i+1)) (featuring K _ (spread_pays Λ l S i) x) (featuring K _ (spread_has Λ l S (i+1)) y)

variable (f:∀ i, Palette (S i)) (Q: (i:ℕ)→Method Λ l (spread Λ l S i))

def stock : (i:ℕ)→ Palette (spread Λ l S i)
 | 0=> f 0
 | i+1=> ascend Λ l S K i (Q i (stock i)) (f (i+1))

variable (s:ℕ)
local notation "F"=> fun j=> music K (S j) (f j)
lemma stock_begin : music K ((S') 0) (stock Λ l S K f Q 0) = music K (S 0) (f 0) := rfl
lemma stock_next : music K (spread Λ l S (s+1)) (stock Λ l S K f Q (s+1))= music K (swept Λ l ((S') s)) (Q s (stock Λ l S K f Q s)) * music K (S (s+1)) (f (s+1)):= by
 rw [stock, ascend, con_join,stow,stow]

def arch (i:ℕ):ℝ:= (count (spread Λ l S (i+1)))^2 * count (swept Λ l (spread Λ l S i)) * count (S (i+1))
lemma arch_size : 0 ≤ arch Λ l S s:=mul_nonneg (mul_nonneg (sq_nonneg _) (count_nonneg _)) (count_nonneg _)
private lemma ascend_cost (x y): ‖ascend Λ l S K s x y‖≤ arch Λ l S s * ‖x‖ * ‖y‖ := by
  let g:ℝ:= count ((S') (s+1))^2; let v:= featuring K _ (spread_pays Λ l S s); let w:=featuring K _ (spread_has Λ l S (s+1)); change ‖chorusMul K _ (v x) (w y)‖ ≤ _
  exact (join_cost ..).trans ((mul_le_mul (mul_le_mul_of_nonneg_left (v.le_of_opNorm_le (featuring_cost ..) x) (sq_nonneg _)) (w.le_of_opNorm_le (featuring_cost ..) _) (norm_nonneg _) (mul_nonneg (sq_nonneg _) (mul_nonneg (count_nonneg _) (norm_nonneg _)))).trans_eq (by unfold arch; ring))

private lemma ascend_diff (x y z): ascend Λ l S K s (x-y) z = ascend Λ l S K s x z - ascend Λ l S K s y z:= by
 simp_rw [ascend,map_sub]; rfl

def purse (i:ℕ):ℝ:= ∏ j ∈ range (i+1), ‖f j‖
lemma purse_size : 0 ≤ purse S f s:= Finset.prod_nonneg (fun _ _=> norm_nonneg _)
lemma purse_begin : purse S f 0= ‖f 0‖:= by rw [purse, prod_range_succ]; simp
lemma purse_next:purse S f (s+1)=purse S f s*‖f (s+1)‖:= prod_range_succ ..

-- estimate when operator sizes of all stages through are bounded by b:
-- mixed cost = ∏arch b. For distance replace b by at least 1, obtain s*d*same product.
variable (b:ℕ→ℝ)(h:∀ i,1 ≤ b i)
def facia :ℝ:= ∏ i∈ range s,(arch Λ l S i * b i)

lemma facia_step (n:ℕ): facia Λ l S (n+1) b= facia Λ l S n b* (arch Λ l S n*b n):=prod_range_succ ..
include h
lemma facia_size:0 ≤ facia Λ l S s b:= prod_nonneg (fun i _ =>mul_nonneg (arch_size ..) (zero_le_one.trans (h i)))
lemma bound (p:∀ i<s,‖Q i‖ ≤ b i) : ‖stock Λ l S K f Q s‖ ≤ facia Λ l S s b*purse S f s:=by
 induction s with
 | zero => rw [purse_begin, facia, range_zero, prod_empty,one_mul]; exact le_rfl
 | succ s ih=>
   let Z:= stock Λ l S K f Q
   have ht: ‖Q s (Z s)‖ ≤ b s * (facia Λ l S s b*purse S f s):= ((Q s).le_of_opNorm_le (p s (lt_add_one _)) _).trans (mul_le_mul_of_nonneg_left (ih fun i d=> p i (by omega)) (zero_le_one.trans (h s)))
   rw [stock]; apply le_trans (ascend_cost Λ l S K s (Q s (Z s)) _); exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (arch_size ..)) (norm_nonneg _)).trans_eq (by rw [facia_step,purse_next]; ring)

private lemma door (Q R:Method Λ l (spread Λ l S s))(a u:Palette (spread Λ l S s))(d B C:ℝ)(p:‖R‖≤ b s)(e:0 ≤ d) (r:dist Q R≤d)(x:‖a‖ ≤ B)(y:‖a-u‖ ≤ C) : ‖Q a-R u‖ ≤ d*B+b s*C := by
  have he: ‖(Q-R) a‖ ≤ d*B:= ((Q-R).le_of_opNorm_le (by rw [dist_eq_norm (E:=Method Λ l ((S') s))] at r; exact r) a).trans (mul_le_mul_of_nonneg_left x e)
  have ht: ‖R (a-u)‖ ≤ b s*C:= (R.le_of_opNorm_le p _).trans (mul_le_mul_of_nonneg_left y (zero_le_one.trans (h s)))
  exact calc
    _ = ‖(Q-R) a+R (a-u)‖:=by rw [ContinuousLinearMap.sub_apply,map_sub]; congr 1; abel
    _ ≤ _ := (norm_add_le ..).trans (add_le_add he ht)

theorem price (p:∀ i<s,‖Q i‖≤ b i)(R:∀ i, Method Λ l (spread Λ l S i))(q:∀ i<s,‖R i‖≤ b i)(d:ℝ)(e:0 ≤ d)(a:∀ i<s,dist (Q i) (R i)≤d) : ‖stock Λ l S K f Q s - stock Λ l S K f R s‖ ≤ s*d*(facia Λ l S s b*purse S f s):=by
 induction s with
 | zero => rw [stock,stock,sub_self,norm_zero]; simp -- dependent stock
 | succ s ih=>
   let Fq:= stock Λ l S K f Q s; let Fr:= stock Λ l S K f R s; let C:= facia Λ l S s b*purse S f s; let i:s<s+1:=lt_add_one _
   have t:= fun (j:ℕ) (v:j<s)=> lt_trans v i; have P:= fun (j:ℕ) (k:j<s)=> p j (t j k)
   have HC:0 ≤ C:=mul_nonneg (facia_size Λ l S s b h) (purse_size S f s)
   have he: ‖Q s Fq - R s Fr‖ ≤ b s*((s+1)*d*C):=(door Λ l S s b h (Q s) (R s) Fq Fr d C (s*d*C) (q s i) e (a s i) (bound Λ l S K f Q s b h P) (ih P (fun j k=> q j (t j k)) (fun j k=> a j (t j k)))).trans (by
     calc
       _ ≤ b s*(d*C)+b s*(s*d*C):= add_le_add_left (le_mul_of_one_le_left (mul_nonneg e HC) (h s)) _ -- direction Lean add_left
       _=b s*((s+1)*d*C):=by ring)
   rw [stock, stock, ←ascend_diff]; apply le_trans (ascend_cost Λ l S K s (Q s Fq-R s Fr) _); exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (arch_size ..)) (norm_nonneg _)).trans_eq (by unfold C; rw [purse_next,facia_step,Nat.cast_add,Nat.cast_one]; ring)
end spread
end Meet
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.Meet.price
