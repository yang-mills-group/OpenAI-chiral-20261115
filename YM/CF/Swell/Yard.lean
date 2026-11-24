import YM.CF.Swell.Tap
import YM.CF.Roots.Halo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
-- Kernel pilot currency conversion from bank with price at supports.H. no era meta.
variable {N:Side}{P:BudgetPoint} {K t:ℕ}{c:ℝ}
variable {A:Type*}[Fintype A] {I:Type*}[Fintype I][DecidableEq I](σ:A→Seat N)(v:∀ t: Seat N, (univ.filter fun i:A=>σ i=t).card ≤ K)
def νfit(X:ℕ)(k:ℕ):= k*(4*X+2)+2*X
variable (o:Seat N)
include v
lemma swell_h(r:ℕ): (univ.filter fun i:A=> separation o (σ i)≤r).card ≤ ((2*r+1)^4)*K:=by
 classical
 let X:= halo r {o}; let Y:=univ.filter fun i:A=>separation o (σ i) ≤ r; have ha:(Y.biUnion fun i=>{i})=Y:=by ext; simp
 have hx(i:A): i∈ Y↔σ i∈X:=by simp [Y,X,Lattice.halo_spec]
 have hm: Y⊆ X.biUnion (fun x:Seat N=>univ.filter fun i:A=>σ i=x):=fun t h=>mem_biUnion.mpr ⟨σ _,(hx _).mp h,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
 refine le_trans (card_le_card hm) (card_biUnion_le.trans ((sum_le_sum (fun i _=>v i)).trans ?_))
 rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ ((Corona.halo_size {o} r).trans_eq (by simp [two_mul])) -- tune
omit v
variable (X:A→I→Support (Cube.More N))(u:A→I→ℝ)(h:∀ a:A,0 ≤ u a)
variable (Z:ℝ)(B:ℕ) -- tune
abbrev mass_B(Θ:ℝ)(i:A)(j:I):= currency B Θ (X i j)* u i j
abbrev Λpay(B:ℕ)(a:ℝ)(o:Seat N)(X:I→Support (Cube.More N))(F:I→ℝ):ℝ:= ∑ i:I with o∈X i,currency B a (X i)*F i
variable (D:ℝ)(p:0 ≤ D)(q:∀ a:A,∀ i,u a i≠0→σ a ∈ X a i)(r:∀ i:A, ∑ j:I,mass_B X u B (Z+1) i j ≤ D)
abbrev νlot (B m:ℕ):= (16*(B+1))^4 * (m+1)^4
lemma town_V (B m:ℕ): (2*νfit B m+1)^4 ≤ νlot B m:=by rw [νlot,←mul_pow]; unfold νfit; gcongr; nlinarith
include q r h p v
lemma peak_k(i:ℕ) : let F:=fun x:A=>univ.filter (fun j:I=> o∈ X x j ∧ coverNumber B (X x j)=i); (∑ x:A,∑ j∈F x,mass_B X u B Z x j) ≤ (νlot B i:ℝ)*K*(Real.exp (- (i:ℝ))*D):=by
 intro F; let M':=univ.filter (fun x:A=>separation o (σ x) ≤ νfit B i)
 have he(x:A)(t:x∉M'):∑ j∈F x,mass_B X u B Z x j=0:=by
    refine sum_eq_zero fun j s=>mul_eq_zero_of_right _ ?_; by_contra v; obtain ⟨o,hP⟩:=(mem_filter.mp s).2; exact t (mem_filter.mpr ⟨mem_univ _, (show _ from (by unfold νfit; rw [←hP]; exact Corona.extent _ _ o (q x j v)))⟩) -- name o shadow
 let t:= Real.exp (-(i:ℝ)); have hk:t>0:=Real.exp_pos _
 have hu(x:A): ∑ j∈F x,mass_B X u B Z x j ≤ t*D:=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_trans (sum_le_sum_of_subset_of_nonneg (f:=mass_B X u B (Z+1) x) (subset_univ (F x)) fun j _ _=>mul_nonneg (Real.exp_pos _).le (h x j)) (r _)) hk.le)
    rw [mul_sum]; apply sum_le_sum; intro j s; unfold mass_B; rw [←mul_assoc t]; unfold currency; rw [(mem_filter.mp s).2.2]; apply le_of_eq; congr 1; unfold t; rw [←Real.exp_add]; congr 1; ring
 rw [←sum_subset (subset_univ M') (fun i _=>he i)]; apply (sum_le_sum fun x _=>hu x).trans; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (swell_h σ v o _).trans (Nat.mul_le_mul_right K (town_V B i)) : (M'.card:ℝ) ≤ _ ) (mul_nonneg hk.le p) -- spacing
omit h q r v p
def κRepo := ∑' i:ℕ, ((i:ℝ)+1)^4 * Real.exp (-(i:ℝ))
def feeU(B K:ℕ):= ((16*(B+1:ℝ))^4) * K *κRepo
lemma κRepoH : 0≤κRepo:= tsum_nonneg (fun i=>by positivity)
lemma αfee : Summable (fun i:ℕ=> ((i:ℝ)+1)^4*Real.exp (-(i:ℝ))):=by
 -- ℝ exp.Need use geometric polynomial. inspect
 let P:= Real.exp (-1); have ht: (fun i:ℕ=> P^i)=fun i:ℕ=> Real.exp (-(i:ℝ)):=by
    funext i; unfold P; rw [←Real.exp_nat_mul]; congr 1; ring
 simp_rw [← congrFun ht]; -- tune
 have he:‖P‖<1:=by unfold P; rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_lt_one_iff]; norm_num
 have h(i:ℕ):Summable fun n:ℕ=> (n:ℝ)^i * P^n:=summable_pow_mul_geometric_of_norm_lt_one i he
 refine (((((h 4).add ((h 3).mul_left 4)).add ((h 2).mul_left 6)).add ((h 1).mul_left 4)).add (h 0)).congr ?_; intro b; ring
include p q r v h
lemma pyre_k: ∑ i:A, Λpay B Z o (X i) (u i) ≤ feeU B K* D:=by
 let Y(x:A):=univ.filter fun i:I=>o∈ X x i; let f(x:A)(i:I):=coverNumber B (X x i); let F:= Finset.univ.biUnion fun x:A=>(Y x).image (f x)
 let W(x:A):= univ.filter fun y:I=>o∈ X x y
 have hu(y:A): ∑ i∈W y,mass_B X u B Z y i=∑ l∈F,∑ j∈(W y).filter (fun j=>f y j=l),mass_B X u B Z y j:= (sum_fiberwise_of_maps_to (fun i p=>mem_biUnion.mpr ⟨y,mem_univ _, mem_image_of_mem _ p⟩) _).symm
 change ∑ i:A, ∑ j∈W i,mass_B X u B Z i j ≤ _; simp_rw [hu]; rw [sum_comm]; let K':= (16*(B+1:ℝ))^4; let V(x:ℕ):= ((x:ℝ)+1)^4*Real.exp (-(x:ℝ)); let L:=K' *K*D; have hl:0 ≤ L:=by unfold L K'; positivity
 apply (sum_le_sum (g:=fun i=>L*V i) ?_).trans; swap
 · intro i _; unfold W f; simp_rw [filter_filter]; refine (peak_k σ v o X u h Z B D p q r i).trans_eq ?_; unfold V L K' νlot; push_cast; ring
 rw [←mul_sum]; refine (mul_le_mul_of_nonneg_left (show ∑ i∈F,V i ≤ κRepo from αfee.sum_le_tsum _ (fun _ _=> by positivity)) hl).trans_eq ?_; unfold L K' feeU; ring
end YM.CF.Swell
