import YM.CF.Swell.Yard
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
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
-- exchange ordinary anchor bank to incidence over all sites.Extra fuel.PSR.
variable {N:Side}{P:BudgetPoint} {K:ℕ}{c α Θ:ℝ}
variable {I:Type*}[Fintype I][DecidableEq I]
variable (M:I→Seat N)(T:I→ Support (Cube.More N))(G:I→ℝ)(hb:0 ≤ c)(g:0 ≤G) (p:∀ i,M i∈ T i)(z: Seat N)(a:ℝ)
def χbank (P:BudgetPoint)(b:ℝ)(t:Seat N)(M:I→ Seat N)(X:I→Support (Cube.More N))(Q:I→ℝ):= ∑ i:I with M i=t, Trees.currency P.B b (X i)*Q i
include g hb p
lemma town_U(u:∀ i:Seat N,χbank P (a+1) i M T G≤c): Λpay P.B a z T G ≤ feeU P.B 1 * c:=by
 let f(x:Seat N)(i):=if M i=x then G i else 0; have hp(x): 0 ≤ f x:=fun i=>by unfold f; split; exact g _; rfl
 have hx(x:Seat N): ∑ j:I,mass_B (fun (_:Seat N)=>T) f P.B (a+1) x j ≤ c:=by unfold mass_B f; simp_rw [mul_ite,mul_zero]; rw [←sum_filter]; exact u x
 refine le_trans ?_ (pyre_k (fun i:Seat N=>i) (K:=1) (fun d=>by rw [show (univ.filter (fun j:Seat N=> j=d))= {d} from ?_]; exact (card_singleton d).le; ext; simp) z (fun _=>T) f hp a P.B c hb ?_ hx)
 · unfold Λpay f; rw [sum_comm]; refine le_of_eq (Finset.sum_congr rfl fun i _=>?_); rw [←mul_sum]; simp
 intro x i h; change (if M i=x then G i else 0)≠0 at h; split at h; next hx=> exact hx ▸ p i
 next h'=>exact False.elim (h rfl)
omit g hb p
variable (F:RegBudget N)(W:Scree.Hub N→ℝ)(h:ℝ)(t:∀ X,PressB P X (F X) h (W X))(u:0 ≤h)
include t u
lemma peek0 {M V:ℝ}(o:Seat N)(x:Scree.Hub N)(i:Scree.Hub N)(p:x.val.2=i.val.2): PressB P x (F i) h (fareX P.B P i.val.2* (chi_f P.order*W i)):=by
 let T:= Classical.arbitrary (Ids N); have ht:= Vow.rimR (t i) u; rw [←p]; exact (p ▸ ht : Medal P x.val.2 ∅ (oV (F i)) h (chi_f P.order *W i)).preservesE T u P.B
-- E pulse measure.Assemble.Root shell. Burner wants After.Trans.T at P2.Double.
omit t
variable (o:Seat N)(D:ℝ)(pΩ:ForgeB F (filmK P (P.supportExponent+1+1)) P h (fun _=>D))(hpΩ:∀ i:Scree.Hub N,o∉i.val.2→F i=0)
local notation "Kγ"=> P -- fine.
abbrev pivot_T(P:BudgetPoint):= reserveT P.power P.order P.B 1* (chi_f P.order*(feeU P.B 1*D))
-- Θ bank derivative; re-root.X at ONE. Card_t.
include pΩ hpΩ
lemma ϕtip :∃ F':RegBudget N,IncX (fun _=>False) F' P h (pivot_T D P)∧(∀ i:Scree.Hub N,i.val.1 ≠o→ F' i=0)∧∀ V:Pane N,exponentL P F' V= exponentL P F V:=by
 obtain ⟨G,g,x⟩:=pΩ.bit; let U:=univ.filter (fun i:Scree.Hub N=>o∈ i.val.2)
 let X(i:Scree.Hub N): Scree.Hub N:=if z:o∈i.val.2 then ⟨(o,i.val.2),z⟩ else i
 let Z:=P.supportExponent; have hv(Y):0 ≤ G Y:= (Taxi.eraF _ Y (g _) u 1 (ping_f P _)).grade
 let pΨ(j:Scree.Hub N):=fareX P.B P j.val.2*(chi_f P.order*G j)
 have hZ:= town_U (fun i:Scree.Hub N=>i.val.1) (fun i:Scree.Hub N=>i.val.2) G (P:=P) (show 0≤D from le_trans (sum_nonneg (s:=univ) (fun i _=> mul_nonneg (show 0≤ filmK _ _ _ o from by unfold filmK; split; exact (Real.exp_pos _).le; rfl) (hv i))) (x o)) hv (fun i=>i.property) o (Z+1) (fun i=>?_); swap; · unfold χbank; rw [sum_filter]; refine le_trans ?_ (x i); exact sum_le_sum fun j _=>le_of_eq (by unfold filmK; simp only [eq_comm,ite_mul,zero_mul]; rfl)
 let Y':=Larch.sunY U X F; have he(i): (X i).val.2= i.val.2:=by unfold X; split <;>rfl
 have hp'(i:Scree.Hub N)(v:i∈U):=(show PressB P (X i) (F i) h (pΨ i) from peek0 (M:=1) (V:=1) F G h g u o _ _ (he i))
 have hf(j)(p:j∈U):=hp' _ p
 let B:= P.B; let R:= reserveT P.power P.order P.B 1; let τ:=chi_f P.order
 have hτ:0 ≤ τ:=spicy_f _
 have hR:0 ≤ R:=by unfold R reserveT coin_n stilK; positivity
 have hk(i:Scree.Hub N):P.mass (X i).val.2 (pΨ i)≤R*(τ * mass_B (fun _:Unit=>fun i:Scree.Hub N=>i.val.2) (fun _:Unit=>G) P.B (P.supportExponent+1) () i):=by
    rw [he]; let Y:=i.val.2; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nor.coinPay P Y 1 zero_lt_one) (mul_nonneg hτ (hv i))) (show 0≤Real.exp (P.supportExponent*coverNumber P.B i.val.2) from (Real.exp_pos _).le)); change _ ≤ R*(τ*(Real.exp _*G i)); rw [add_mul, Real.exp_add]; apply le_of_eq; unfold Y R; ring -- tune.
 refine ⟨Y', Larch.feat_v _ _ _ _ _ _ hf ?_, fun i t=>?_ ,fun V=>?_⟩
 · intro i; refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hτ) hR); unfold Λpay; simp_rw [mul_sum]; let S:= U.filter (fun j=> (X j).val.1=i); exact (sum_le_sum (fun j _=> hk j)).trans (sum_le_sum_of_subset_of_nonneg (s:=S) (filter_subset ..) (fun j _ _=>mul_nonneg hR (mul_nonneg hτ (mul_nonneg (Real.exp_pos _).le (hv j)))))
 · apply sum_eq_zero; intro j p; have hx:(X j).val.1=o:=by unfold X; rw [dif_pos ((mem_filter.mp (mem_filter.mp p).1).2)]
   exact False.elim (t ((mem_filter.mp p).2 ▸ hx))
 · have hp(i:Scree.Hub N): numbE P.threshold i.val.2 (Y' i) V=∑ j∈U with X j=i,numbE P.threshold j.val.2 (F j) V:=by
      unfold Y' Larch.sunY; unfold numbE; by_cases q:pingS P.threshold i.val.2 V
      · rw [Set.indicator_of_mem (show V∈_ from q)]; rw [Finset.sum_apply]; exact sum_congr rfl (fun j p=> (Set.indicator_of_mem (show V∈ {k:Pane N|pingS P.threshold j.val.2 k} from he j ▸ ((mem_filter.mp p).2 ▸ q)) _).symm)
      rw [Set.indicator_of_notMem (show V∉_ from q)]; symm; apply sum_eq_zero; intro j p; exact  Set.indicator_of_notMem (show V∉ _ from fun h=> q ((mem_filter.mp p).2 ▸ ((he j).symm ▸ h))) _
   unfold exponentL; simp_rw [hp]; rw [sum_fiberwise_of_maps_to (fun i _=>mem_univ _)]; apply sum_subset (subset_univ _); intro i p v; rw [hpΩ _ (fun p=>v (mem_filter.mpr ⟨mem_univ _,p⟩))]; simp [numbE]
end YM.CF.Swell
