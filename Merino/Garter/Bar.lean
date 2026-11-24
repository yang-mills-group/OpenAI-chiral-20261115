import YM.SU5.Regis.Breeze
import Merino.Garter.Guard
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Garter
open Cuff Finset Function
open scoped BigOperators ContDiff

open ProbabilityTheory MeasureTheory Filter
open scoped BigOperators Topology 

section Algebra

def bar (x:ℝ):=Real.exp (6*x)+Real.exp (-6*x)
def slab (x y z w):=bar x+bar y + (bar z+bar w)
lemma bar_thick (x:ℝ): (max 1 |x|)^6 ≤ bar x:=by
 have h: max 1 |x| ≤ Real.exp |x| := max_le (Real.one_le_exp (abs_nonneg _)) (by linarith [Real.add_one_le_exp |x|])
 calc
   _ ≤ (Real.exp |x|)^6:=pow_le_pow_left₀ ((abs_nonneg x).trans (le_max_right ..)) h _
   _ = Real.exp (6*|x|):=by simpa using (Real.exp_nat_mul |x| 6).symm
   _ ≤ _:=by
      rcases abs_choice x with e|e
      · rw [e]; exact le_add_of_nonneg_right (Real.exp_pos _).le
      rw [e,show 6 * -x= -6*x from by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le

def lung(x y z w:ℝ):=max (max |x| |y|) (max 1 (max |z| |w|))
lemma lung_pos(x y z w):1 ≤ lung x y z w :=(le_max_left ..).trans (le_max_right ..)
lemma lung_fit(x y z w):
 let R:=lung x y z w
 |x|≤R ∧ |y|≤R ∧ |z|≤R ∧ |w|≤R:= by unfold lung; dsimp only; grind


lemma lung_bar (x:ℝ) : |x|^6≤bar x:=le_trans (pow_le_pow_left₀ (abs_nonneg _) (le_max_right 1 _) _) (bar_thick x)
lemma lung_6(x y z w):lung x y z w^6≤slab x y z w:= by
 have hx:1≤bar x:=le_trans (one_le_pow₀ (le_max_left 1 |x|)) (bar_thick x)
 have hv(a):0≤bar a:=by unfold bar; positivity
 have go: lung x y z w∈({1,|x|,|y|,|z|,|w|}:Finset ℝ):=by unfold lung; grind
 unfold slab
 simp at go
 rcases go with g|g|g|g|g <;> rw [g] <;>
    linarith only [hx,hv x,hv y,hv z,hv w,lung_bar x,lung_bar y,lung_bar z,lung_bar w]

def dish(d x y z w:ℝ):= (bite d x*bite d y)*(bite d z*bite d w)
lemma pair_thick (d:ℝ){x y R}(h:|x|≤R)(t:|y|≤R): |bite d x*bite d y|≤R^2:= by
 rw [abs_mul,pow_two]; exact mul_le_mul ((chew_small ..).trans h)
   ((chew_small ..).trans t) (abs_nonneg _) ((abs_nonneg _).trans h)


lemma dish_thick (d x y z w:ℝ):
  |dish d x y z w|≤slab x y z w:=by
 obtain ⟨a,b,c,e⟩:=lung_fit x y z w
 unfold dish; rw [abs_mul]
 refine (mul_le_mul (pair_thick d a b) (pair_thick d c e) (abs_nonneg _) (sq_nonneg _)).trans ?_
 rw [←pow_add]
 exact le_trans (pow_le_pow_right₀ (lung_pos x y z w) (m:=2+2) (n:=6) (by decide)) (lung_6 x y z w)
lemma pair_gap(d:ℝ){x y R:ℝ}(h:|x|≤R)(t:|y|≤R):
 |bite d x*bite d y-bite 0 x*bite 0 y|≤ d^2*2*R^4:=by
 simp only [show bite 0=id from by ext u; simp [bite],id_eq]
 have r:0≤R:=(abs_nonneg _).trans h
 have go(u)(e:|u|≤R): |bite d u-u|≤d^2*R^3:=by apply (chew_loss ..).trans; gcongr
 refine (bleary ((chew_small ..).trans h) t).trans ((mul_le_mul_of_nonneg_left
   (add_le_add (go _ t) (go _ h)) r).trans_eq ?_)
 ring


lemma dish_gap (d x y z w:ℝ):
 |dish d x y z w-dish 0 x y z w| ≤ (4*d^2)*slab x y z w:=by
 let R:= lung x y z w
 obtain ⟨a,b,c,e⟩:=lung_fit x y z w
 refine (bleary (pair_thick d a b) (pair_thick 0 c e)).trans ((mul_le_mul_of_nonneg_left
    (add_le_add (pair_gap d c e) (pair_gap d a b)) (sq_nonneg _)).trans ?_)
 calc
   _ = (4*d^2)*R^6:= by unfold R; ring
   _ ≤ _ :=mul_le_mul_of_nonneg_left (lung_6 ..) (by positivity)
end Algebra

section Aisle
variable {E:Type}[NormedAddCommGroup E][InnerProductSpace ℝ E]
 [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
local notation "L"=> E→L[ℝ] ℝ
local notation "μ"=>stdGaussian E

lemma payB (t: E→L[ℝ] ℝ) : Integrable (fun x=> bar (t x)) (stdGaussian E) :=by
 apply Integrable.add <;>
   [apply (mgf_pos_iff (X:=⇑t) (t:=(6:ℝ))).1; apply (mgf_pos_iff (X:=⇑t) (t:=(-6:ℝ))).1]
 all_goals rw [Regis.exp_linear]; exact Real.exp_pos _



abbrev tile(t:ℝ):=Real.exp (18*t^2)
lemma sumB(t:L){C:ℝ}(h:‖t‖≤C): (∫ x,bar (t x)∂μ) ≤ tile C+tile C:=by
 have k(s:ℝ)(p:s^2=36):(∫ x,Real.exp (s*t x)∂μ)≤tile C:=by
    change mgf _ (stdGaussian E) _ ≤_
    rw [Regis.exp_linear,p]
    apply Real.exp_le_exp_of_le
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) h 2]
 have hz(s):Integrable (fun x=>Real.exp (s*t x)) μ:=by
    apply (mgf_pos_iff (X:=⇑t) (t:=s)).1
    rw [Regis.exp_linear]; exact Real.exp_pos _
 unfold bar
 rw [integral_add (hz _) (hz _)]
 exact add_le_add (k _ (by norm_num)) (k _ (by norm_num))

abbrev slabX (a b c e:L)(x:E):=slab (a x) (b x) (c x) (e x)
abbrev dishX (a b c e:L)(d:ℝ)(x:E):=dish d (a x) (b x) (c x) (e x)
lemma islab(a b c e:L):Integrable (slabX a b c e) μ:= ((payB a).add (payB b)).add ((payB c).add (payB e))


lemma idish(a b c e:L)(d:ℝ):Integrable (dishX a b c e d) μ :=
 (islab ..).mono' ((show Continuous (dishX a b c e d) from by
    unfold dishX dish
    have t:= (chew_smooth d).continuous
    exact ((t.comp a.continuous).mul (t.comp b.continuous)).mul
       ((t.comp c.continuous).mul (t.comp e.continuous))).aestronglyMeasurable)
   (ae_of_all _ (fun i=>by rw [Real.norm_eq_abs]; exact dish_thick ..))

abbrev noodlePrice (t):= 8*tile t
variable (a b c e:E→L[ℝ] ℝ){C:ℝ} (h:‖a‖≤C)(q:‖b‖≤C)(f:‖c‖≤C)(l:‖e‖≤C)
include h q f l
lemma billB:(∫ x,slabX a b c e x∂μ)≤noodlePrice C:=by
 unfold slabX slab
 have hb (a b:L) : Integrable (fun x=>bar (a x)+bar (b x)) μ:=(payB a).add (payB b)
 rw [integral_add (hb a b) (hb c e),
     integral_add (payB _) (payB _),integral_add (payB _) (payB _)]
 apply (add_le_add (add_le_add (sumB _ h) (sumB _ q))
     (add_le_add (sumB _ f) (sumB _ l))).trans_eq
 unfold noodlePrice
 ring


abbrev noodle(a b c e:L)(d:ℝ):=∫ x,dishX a b c e d x∂μ
lemma noodle_sup(d): |noodle a b c e d| ≤ noodlePrice C:=by
 unfold noodle
 rw [←Real.norm_eq_abs]
 exact (norm_integral_le_of_norm_le (islab a b c e)
    (ae_of_all _ (fun i=>by rw [Real.norm_eq_abs]; exact dish_thick ..))).trans
    (billB a b c e h q f l)
lemma noodle_gap(d): |noodle a b c e d-noodle a b c e 0| ≤ 4*d^2*noodlePrice C:= by
 unfold noodle
 rw [←integral_sub (idish ..) (idish ..),←Real.norm_eq_abs]
 refine (norm_integral_le_of_norm_le ((islab a b c e).const_mul (4*d^2))
   (ae_of_all _ (fun i=>by rw [Real.norm_eq_abs]; exact dish_gap ..))).trans ?_
 rw [integral_const_mul]
 exact mul_le_mul_of_nonneg_left (billB a b c e h q f l) (by positivity)
end Aisle
end YM.CF.Merino.Garter
