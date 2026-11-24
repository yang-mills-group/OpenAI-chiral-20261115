import YM.CF.Haro.Keeps
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
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{n:ℕ}{K u v w A' B' C':ℝ}
variable (o:Seat f){P Y: RG.BudgetPoint}
abbrev pear(n:Side):=Support (More n)
abbrev pactB (n:ℕ)(i:Prism.Rock f)(j:Prism.Rock c):= (1+(G.count.val:ℝ)⁻¹*separation (node i.1) ((ratio G).embed (node j.1)):ℝ)^n
abbrev posG {c:Side}(i: Prism.Rock c):=node i.1
abbrev amt (m:ℕ)(q:Seat c)(i j: Prism.Rock c):=(1+(max (separation q (posG i)) (separation q (posG j)):ℕ):ℝ)^m
lemma rope (n:ℕ)(x:Seat c)(r s:Prism.Rock c)(i j:Slot)(t:ℝ)(P:RG.BudgetPoint)(h:n=P.power): tariff P x t {(true,(r,i)),(false,(s,j))}= amt n x r s*t^2:=by
 unfold Scree.tariff; rw [←h,show ({(true,(r,i)),(false,(s,j))}:Finset (Dwell c)).card=2 from ?_]; swap; · simp -- tune
 unfold amt; congr 3
 -- tune simp
 simp [endL, posG]
private lemma rer(o:Seat f)(i:Prism.Rock f)(p:Prism.Rock c):
 (1+(separation ((ratio G).parent o) (node p.1):ℝ)) ≤ 3*(1+(separation o (node i.1):ℝ))*(1+(G.count.val:ℝ)⁻¹* (separation (node i.1) ((ratio G).embed (node p.1)):ℝ)):= by
 let L:ℝ:=G.count.val; let a:=separation o (node i.1); let b:=separation (node i.1) ((ratio G).embed (node p.1)); let C:=separation ((ratio G).parent o) (node p.1)
 have hl:1 ≤ L:= Nat.one_le_cast.mpr G.count.property
 have hv := Corona.foreshorten (ratio G) o ((ratio G).embed (node p.1)); rw [Ratio.embed_parent] at hv; have hp : L*C≤ a+b+L:=by
    have h':G.count.val*C ≤ a+b+G.count.val:= hv.trans (Nat.add_le_add_right (separation_triangle ..) _); unfold L; exact_mod_cast h'
 have he:0<L:=zero_lt_one.trans_le hl
 change (1+(C:ℝ))≤ 3*(1+(a:ℝ))*(1+L⁻¹*(b:ℝ)); rw [inv_mul_eq_div]; field_simp
 nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) a) (Nat.cast_nonneg (α:=ℝ) b),mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg a)]
lemma amtV(r s:Prism.Rock f)(i j: Prism.Rock c)(m:ℕ) : amt m ((ratio G).parent o) i j ≤ (3:ℝ)^m * amt m o r s * pactB G m r i * pactB G m s j:=by
 have he (r z:Prism.Rock f) (i j:Prism.Rock c) : (1+(separation ((ratio G).parent o) (posG i):ℝ))^m ≤ (3:ℝ)^m * amt m o r z * pactB G m r i * pactB G m z j:=by
    refine le_trans ?_ (le_mul_of_one_le_right (show 0 ≤ (3:ℝ)^m * amt m o r z * pactB G m r i by unfold amt pactB; positivity) (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))); unfold amt pactB; rw [←mul_pow,←mul_pow]; apply pow_le_pow_left₀ (by positivity); refine (rer G o r i).trans ?_; gcongr; exact le_max_left ..
 by_cases h:separation ((ratio G).parent o) (posG j) ≤ separation ((ratio G).parent o) (posG i); · unfold amt; rw [max_eq_left h]; exact he r s i j -- tune rewrite ALL? 
 unfold amt; rw [max_eq_right (le_of_not_ge h),max_comm (separation o _) _]; rw [mul_right_comm]; exact he s r j i
variable {C b v' d:ℝ}(Z:Support (More f)→Toll (Iota G))(hp:∀ X,Z X≥0)(u':0≤d)(l: incline (hall G d) n (G.count.val:ℝ)⁻¹ (fun _=>C) b Z)(hb:0 ≤ b)
lemma gust_l(H:Support (More f)→Toll (Iota G))(x:Prism.Rock f)(y:Prism.Rock c)(T: Support (More f))(p:∀ X i j,0 ≤ H X i j):0≤ paintL G x y (H T):=sum_nonneg fun i _=> sum_nonneg fun j _=>p ..
include hp l h hb
lemma hK (r:Prism.Rock f): (∑ a:Prism.Rock c, ∑ i:Support (More f),pactB G n r a*paintL G r a (Z i))≤ Fintype.card Slot * C:=by
 let Y:= (switchG G).symm; let H(i:Slot)(v:Single c)(X:Support (More f)):= pactB G n r v.1* Z X (Y (r,i)) (patchQ G v); let Q(i:Slot):=∑ j:Single c,∑ X,H i j X
 have hv(i): Q i ≤ C:=by
    let x:=Y (r,i); let L:= (G.count.val:ℝ)⁻¹; let Z'(v:Iota G):=(1+L*separation (lookM G x) (lookM G v):ℝ)^n; let F(v:Iota G):= Z' v* saleM b Z x v
    have hh(v:Single c): Z' (patchQ G v)= pactB G n r v.1:=by unfold Z'; rw [trK G v h]; rw [show lookM G x=node r.1 from ?_]; rfl; change node ( ((switchG G) ( (switchG G).symm (r,i))).1.1) = _; rw [Equiv.apply_symm_apply]
    refine le_trans (b:=∑ j∈ univ.map (patchQ G),F j) ?_ ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg (by unfold Z'; positivity) (sale_nn hp b x i))).trans (l x)); rw [sum_map]; apply sum_le_sum; intro j _; unfold F saleM; rw [mul_sum]; apply sum_le_sum; intro W _; unfold H; rw [hh]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ?_ (Real.one_le_exp (by positivity))) (by unfold pactB; positivity); exact hp ..
 calc
   _ =∑ i:Slot,Q i:=by
       have he(i:Slot): Q i=∑ j:Prism.Rock c,∑ t:Slot,∑ X:Support (More f), H i (j,t) X:=Fintype.sum_prod_type ..; simp_rw [he]; rw [sum_comm (s:=(univ:Finset Slot))]; apply sum_congr rfl; intro a _; unfold paintL; simp_rw [Finset.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro j _; rw [sum_comm]
   _ ≤_:=by simpa using Finset.sum_le_sum (fun i (_:i∈(univ:Finset _))=> hv i)
end YM.CF.Haro
