import ZecaRiptide
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open MeasureTheory Complex
variable {A:ℕ→ℂ→ℂ} {T:ℝ}{W:ℕ→ℝ→ℂ}
variable (h:Seaward A) (p:0<T) (q:Temporal T W)

include h p q
lemma shelf_lipid : ∃C:ℝ, 0≤C ∧ ∀ i, ∀ x∈Set.Ioc (0:ℝ) 1, ∀ y∈Set.Ioc (0:ℝ) 1,
  dist (shellI (A i) T (W 0) y) (shellI (A i) T (W 0) x) ≤ C*dist y x:=by
 obtain ⟨C,u,m⟩:=standing_room h p q 1
 simp only [pow_zero,div_one] at m
 refine ⟨C,u,fun i x e y f=>?_⟩
 have b: ∀w∈ Ioc (0:ℝ) 1,‖-I * shellI (A i) T (W (0+1)) w‖ ≤ C:=by
    intro w a
    rw [norm_mul,norm_neg,norm_I,one_mul]
    have wp:0<w:=a.1
    have k:=m (Real.sqrt w) ⟨Real.sqrt_pos.mpr wp,Real.sqrt_le_one.mpr a.2⟩ i
    unfold squareI at k; rw [Real.sq_sqrt wp.le] at k
    exact k
 rw [dist_eq_norm,dist_eq_norm]
 exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f':= fun w=>-I *
     shellI (A i) T (W (0+1)) w) (fun w (a:w∈Ioc (0:ℝ) 1)=> 
         (redshift (h.enters i) p q 0 a.1).hasDerivWithinAt)
       b (convex_Ioc ..) e f

lemma moth_uniform : ∀ r>0,∃S∈𝓝[>] (0:ℝ), ∀i, 
   ∀ x∈S, ∀ y∈S, dist (shellI (A i) T (W 0) x) 
          (shellI (A i) T (W 0) y) < r :=by
 intro r hp
 obtain ⟨C,e,z⟩:= shelf_lipid h p q
 let U := 𝓝[>] (0:ℝ)
 have f:(1+C)*0<r:=by simpa
 let w:=min 1 (r/(1+C))
 have e0:0<w:=lt_min zero_lt_one (by positivity)
 let S:=Ioo 0 w
 have j:S∈U:= Ioo_mem_nhdsGT e0
 have d: w≤1:=min_le_left ..
 have t: (1+C)*w≤r:= (le_div_iff₀' (by positivity:0<1+C)).mp (min_le_right ..)
 refine ⟨S,j,fun i x a y b=>?_⟩
 have sub:S⊆Ioc 0 1:=fun _ h=>⟨h.1,(h.2.trans_le d).le⟩
 have c:dist x y<w:=by
    rw [Real.dist_eq,abs_lt]
    constructor<;>linarith only [a.1,b.1,a.2,b.2]
 have k:C*dist x y<(1+C)*w:=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one: C≤1+C) dist_nonneg).trans_lt
       (mul_lt_mul_of_pos_left c (by positivity))
 exact (z i y (sub b) x (sub a)).trans_lt (k.trans_le t)

def sandpiperI (K:ℂ→ℂ) (T:ℝ)(φ:ℝ→ℂ):ℂ := limUnder (𝓝[>] (0:ℝ)) (shellI K T φ)
#check Filter.Tendsto.limUnder_eq
lemma enters_jetty (i:ℕ):
  Tendsto (shellI (A i) T (W 0)) (𝓝[>] 0) (𝓝 (sandpiperI (A i) T (W 0))) :=by
 let g:= shellI (A i) T (W 0)
 let U:= 𝓝[>] (0:ℝ)
 haveI:U.NeBot:=inferInstanceAs (𝓝[>] (0:ℝ)).NeBot
 have k:Cauchy (Filter.map g U):=by
   refine Metric.cauchy_iff.mpr ⟨inferInstance,?_⟩
   intro r e
   obtain ⟨S,a,v⟩:=moth_uniform h p q r e
   refine ⟨g '' S, Filter.image_mem_map a, ?_⟩
   rintro x ⟨y,b,rfl⟩ z ⟨t,f,rfl⟩
   exact v i y b t f
 obtain ⟨x,v⟩:= CompleteSpace.complete k
 unfold sandpiperI
 rw [(show Tendsto g _ _ from v).limUnder_eq]
 exact v
#print axioms enters_jetty
lemma jetty_uniform : ∀ r>0,∀ᶠ x in 𝓝[>] (0:ℝ),∀i, 
 dist (sandpiperI (A i) T (W 0)) (shellI (A i) T (W 0) x) ≤ r:=by
 intro r e
 obtain ⟨S,a,v⟩:=moth_uniform h p q r e
 filter_upwards [a] with x d i
 refine le_of_tendsto ((enters_jetty h p q i).dist tendsto_const_nhds) ?_
 filter_upwards [a] with y b
 exact (v i y b _ d).le
#print axioms jetty_uniform
#check tendsto_integral_filter_of_dominated_convergence
