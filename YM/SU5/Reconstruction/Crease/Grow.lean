import YM.SU5.Reconstruction.Crease.Pollen
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Moth
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame Opera Multiplier
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H: Hilbert} {X:Type*}[MeasurableSpace X] (P:PVM H X)
abbrev envelope (b:Bool)(x:ℝ):ℂ:= if b then pole x else gap x
lemma gSelf (b:Bool)(x:ℝ) :star (envelope b x)= envelope b x:= by cases b <;> simp [envelope,pole,gap,Complex.star_def]
@[fun_prop] lemma pom (b:Bool): Continuous (envelope b):= by cases b <;> unfold envelope pole gap pole <;> simp <;> fun_prop -- tune
abbrev cash (b:Bool)(t x:ℝ):= envelope b x ^2 * ray t x
def petal (x:ℝ):= pole x*gap x
lemma pSelf (x:ℝ) : star (petal x)=petal x:= by simp [petal,Complex.star_def,pole,gap]
variable (θ:ℝ)(p:θ∈ twilight)(S:SimpleFunc X ℝ)(h:∀ x, S x ∈ Ioo (0:ℝ) 1)
def reel (t:ℝ)(b:Bool):=grove P S (cash b t)
def royal := grove P S petal
local notation "r"=>reel P S
local notation "R"=>royal P S
local notation "α"=>S.range
local notation "z"=>Opera.spin θ
variable (A:H.Op)(x y:H)
-- avoid integral exchanging Bochner along unbounded; do directly finite.
@[fun_prop] lemma reel_cont (x:H)(b:Bool) : Continuous fun t=> reel P S t b x:= by unfold reel; simp_rw [grow]; unfold cash; fun_prop
include p h
lemma finbot : (∫ t:ℝ,cup θ t*(inner ℂ (r t false x) (A (r t true y)) + z*inner ℂ (r t true x) (A (r t false y)))) = inner ℂ (R x) (A (R y)):=by
 let Hm(i j:ℝ):=inner ℂ (leaf P S i x) (A (leaf P S j y))
 have hp(f g:ℝ→ℂ):inner ℂ (grove P S f x) (A (grove P S g y))= ∑ i∈α,∑ j∈α,(star (f i)* g j)*Hm i j:= by
   rw [grow, grow, sum_inner]; refine Finset.sum_congr rfl fun i v=>?_; rw [map_sum,inner_sum]; refine Finset.sum_congr rfl fun j q=>?_; rw [inner_smul_left,map_smul,inner_smul_right]; exact (mul_assoc ..).symm
 let F(t i j:ℝ):=cup θ t*(star (ray t i)*ray t j)*(gap i^2*pole j^2+z*pole i^2*gap j^2)* Hm i j
 have ht(i j:ℝ):Integrable (fun t=> F t i j):= by
   apply Integrable.mul_const; apply Integrable.mul_const; apply cup_prices θ p (fun t=> star (ray t i) * ray t j) (by fun_prop) 1; intro t; simp [ray,tune_norm,norm_mul]
 unfold reel; simp_rw [hp]; unfold royal; rw [hp];
 have he(t:ℝ): cup θ t*((∑ i∈α,∑ j∈α,star (cash false t i)*cash true t j*Hm i j)+ z*∑ i∈α,∑ j∈α,star (cash true t i)*cash false t j*Hm i j)= ∑ i∈α,∑ j∈α,F t i j:= by
   -- grouping sums
   rw [Finset.mul_sum _ _ z,← Finset.sum_add_distrib,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.mul_sum _ _ z,← Finset.sum_add_distrib,Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold cash F; simp only [star_mul',star_pow,gSelf]; simp only [envelope, if_true,if_false,reduceCtorEq]; ring
 simp_rw [he]; rw [integral_finsetSum α (fun i _=> integrable_finsetSum α (fun j _=>ht i j))]; refine Finset.sum_congr rfl fun i a=>?_ ; rw [integral_finsetSum α (fun j _=> ht i j)]; refine Finset.sum_congr rfl fun j b=>?_ ; unfold F; rw [integral_mul_const,pSelf,pop p i j (SimpleFunc.forall_mem_range.mpr h i a) (SimpleFunc.forall_mem_range.mpr h j b)]; unfold petal; ring

end YM.BridgeClub.Moth
