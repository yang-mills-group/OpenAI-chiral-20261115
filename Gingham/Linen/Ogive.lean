import YM.CF.Swell.Bark
import YM.CF.Roots.Halo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Linen.Incidence
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open Swell RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
/- Variant of YM.CF.Swell.{Yard,Bark}: convert anchor prices
    to incidence (per member) by spending just 1/2 of the rate. -/
-- Kernel pilot currency conversion from bank with price at supports.H. no era meta.
variable {N:Side}{P:BudgetPoint} {K t:ℕ}{c:ℝ}
variable {A:Type*}[Fintype A] {I:Type*}[Fintype I][DecidableEq I](σ:A→Seat N)(v:∀ t: Seat N, (univ.filter fun i:A=>σ i=t).card ≤ K)
variable (o:Seat N)
variable (X:A→I→Support (Cube.More N))(u:A→I→ℝ)(h:∀ a:A,0 ≤ u a)
variable (Z:ℝ)(B:ℕ) -- tune
variable (D:ℝ)(p:0 ≤ D)(q:∀ a:A,∀ i,u a i≠0→σ a ∈ X a i)(r:∀ i:A, ∑ j:I,mass_B X u B (Z+1/2) i j ≤ D)
include q r h p v
lemma peak_k(i:ℕ) : let F:=fun x:A=>univ.filter (fun j:I=> o∈ X x j ∧ coverNumber B (X x j)=i); (∑ x:A,∑ j∈F x,mass_B X u B Z x j) ≤ (νlot B i:ℝ)*K*(Real.exp (-1/2*(i:ℝ))*D):=by
 intro F; let M':=univ.filter (fun x:A=>separation o (σ x) ≤ νfit B i)
 have he(x:A)(t:x∉M'):∑ j∈F x,mass_B X u B Z x j=0:=by
    refine sum_eq_zero fun j s=>mul_eq_zero_of_right _ ?_; by_contra v; obtain ⟨o,hP⟩:=(mem_filter.mp s).2; exact t (mem_filter.mpr ⟨mem_univ _, (show _ from (by unfold νfit; rw [←hP]; exact Corona.extent _ _ o (q x j v)))⟩) -- name o shadow
 let t:= Real.exp (-1/2*(i:ℝ)); have hk:t>0:=Real.exp_pos _
 have hu(x:A): ∑ j∈F x,mass_B X u B Z x j ≤ t*D:=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_trans (sum_le_sum_of_subset_of_nonneg (f:=mass_B X u B (Z+1/2) x) (subset_univ (F x)) fun j _ _=>mul_nonneg (Real.exp_pos _).le (h x j)) (r _)) hk.le)
    rw [mul_sum]; apply sum_le_sum; intro j s; unfold mass_B; rw [←mul_assoc t]; unfold currency; rw [(mem_filter.mp s).2.2]; apply le_of_eq; congr 1; unfold t; rw [←Real.exp_add]; congr 1; ring
 rw [←sum_subset (subset_univ M') (fun i _=>he i)]; apply (sum_le_sum fun x _=>hu x).trans; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (swell_h σ v o _).trans (Nat.mul_le_mul_right K (town_V B i)) : (M'.card:ℝ) ≤ _ ) (mul_nonneg hk.le p) -- spacing
omit h q r v p
def κRepo := ∑' i:ℕ, ((i:ℝ)+1)^4 * Real.exp (-1/2*(i:ℝ))
def feeU(B K:ℕ):= ((16*(B+1:ℝ))^4) * K *κRepo
lemma κRepoH : 0≤κRepo:= tsum_nonneg (fun i=>by positivity)
lemma αfee : Summable (fun i:ℕ=> ((i:ℝ)+1)^4*Real.exp (-1/2*(i:ℝ))):=by
 -- ℝ exp.Need use geometric polynomial. inspect
 let P:= Real.exp (-1/2); have ht: (fun i:ℕ=> P^i)=fun i:ℕ=> Real.exp (-1/2*(i:ℝ)):=by
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
 change ∑ i:A, ∑ j∈W i,mass_B X u B Z i j ≤ _; simp_rw [hu]; rw [sum_comm]; let K':= (16*(B+1:ℝ))^4; let V(x:ℕ):= ((x:ℝ)+1)^4*Real.exp (-1/2*(x:ℝ)); let L:=K' *K*D; have hl:0 ≤ L:=by unfold L K'; positivity
 apply (sum_le_sum (g:=fun i=>L*V i) ?_).trans; swap
 · intro i _; unfold W f; simp_rw [filter_filter]; refine (peak_k σ v o X u h Z B D p q r i).trans_eq ?_; unfold V L K' νlot; push_cast; ring
 rw [←mul_sum]; refine (mul_le_mul_of_nonneg_left (show ∑ i∈F,V i ≤ κRepo from αfee.sum_le_tsum _ (fun _ _=> by positivity)) hl).trans_eq ?_; unfold L K' feeU; ring


omit p q r v h
 section
variable (M:I→Seat N)(T:I→ Support (Cube.More N))(G:I→ℝ)(hb:0 ≤ c)(g:0 ≤G) (pp:∀ i,M i∈ T i)(z: Seat N)(a:ℝ)
include g hb pp
lemma town_U(u:∀ i:Seat N,χbank P (a+1/2) i M T G≤c): Λpay P.B a z T G ≤ feeU P.B 1 * c:=by
 let f(x:Seat N)(i):=if M i=x then G i else 0; have hp(x): 0 ≤ f x:=fun i=>by unfold f; split; exact g _; rfl
 have hx(x:Seat N): ∑ j:I,mass_B (fun (_:Seat N)=>T) f P.B (a+1/2) x j ≤ c:=by unfold mass_B f; simp_rw [mul_ite,mul_zero]; rw [←sum_filter]; exact u x
 refine le_trans ?_ (pyre_k (fun i:Seat N=>i) (K:=1) (fun d=>by rw [show (univ.filter (fun j:Seat N=> j=d))= {d} from ?_]; exact (card_singleton d).le; ext; simp) z (fun _=>T) f hp a P.B c hb ?_ hx)
 · unfold Λpay f; rw [sum_comm]; refine le_of_eq (Finset.sum_congr rfl fun i _=>?_); rw [←mul_sum]; simp
 intro x i h; change (if M i=x then G i else 0)≠0 at h; split at h; next hx=> exact hx ▸ pp i
 next h'=>exact False.elim (h rfl)


lemma townSmall (u:∀ x:Seat N,χbank P a x M T G≤c):
 (∑ i∈univ.filter fun j:I=> z∈ T j ∧ coverNumber P.B (T j) ≤ P.B,
     currency P.B a (T i)*G i) ≤ (νlot P.B P.B:ℝ)*c:=by
 let l:=νfit P.B P.B; let S:=univ.filter fun x:Seat N=> separation z x ≤ l
 let Y:= univ.filter fun j:I=>z∈T j ∧ coverNumber P.B (T j) ≤ P.B
 have e: Set.MapsTo M Y S:=by
   intro i v; obtain ⟨w,t⟩ := (mem_filter.mp v).2
   refine mem_filter.mpr ⟨mem_univ _,(Corona.extent _ P.B w (pp i)).trans ?_⟩
   unfold l νfit; gcongr
 rw [←sum_fiberwise_of_maps_to e]; apply (sum_le_sum (g:=fun _=>c) ?_).trans
 · rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hb
   exact_mod_cast le_trans (swell_h (fun i:Seat N=>i) (K:=1) (fun d=>by rw [show (univ.filter (fun j:Seat N=> j=d))= {d} from ?_]; exact (card_singleton d).le; ext; simp) z l) ((Nat.mul_one _).le.trans (town_V ..))
 intro x _
 apply le_trans _ (u x)
 exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset_univ Y)) fun i _ _=>mul_nonneg (Real.exp_pos _).le (g i)
end

