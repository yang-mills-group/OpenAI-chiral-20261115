import YM.CF.Sour.Troop
import YM.CF.Ione.Rake
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt
variable (s t:Sweep n)(a:ℝ)
local notation "p₀"=> s.charge
local notation "x₀"=> castX s
local notation "T"=> γS s
local notation "Ω"=> Openc (More n) a
abbrev jLL (s:Sweep n)(i j:JS):= ‖(γS s).val i j‖
lemma rowC (Y:Finset JS)(v: JS→ℝ)(p:∀ i∈Y,v i≤1)(a:Seat n)(h:∀ i∈Y,node i.1.1=a) :∑ i∈ Y,v i ≤ Tenant.quota:=by
 let C0:=board (forum n 1) (Branch.bay (terr (More n)) a 0); have hx:Y⊆ C0:=by intro i p; refine mem_filter.mpr ⟨mem_univ _,?_⟩; change node _∈_; rw [h i p]; change a∈Branch.bay (terr _) a 0; rw [bay_mem]; change separation a a ≤ 0; simp -- tune
 have hp := (meterQ n 1).place a 0; change ((C0.card:ℝ) ≤ _) at hp; refine (sum_le_sum p).trans ((by rw [sum_const,nsmul_eq_mul,mul_one]; exact_mod_cast card_le_card hx : (∑ j∈Y,(1:ℝ)) ≤ C0.card) |>.trans (by simpa using hp))
local notation "U"=> jLL s
lemma urge (i j:JS) : jLL s i j ≤ 1:= (norm_entry (γS s).val i j).trans_eq (CStarRing.norm_of_mem_unitary (γS s).property)
lemma ρ_R(i:JS) : (∑ j:JS, jLL s i j) ≤ Tenant.quota :=by
 let a:=boxA s (node i.1.1); let F:=univ.filter fun j:JS=> (γS s).val i j≠0; rw [←sum_subset F.subset_univ]; swap
 · intro j _ t; have he:(γS s).val i j=0:=by unfold F at t; simpa using t -- tune
   rw [jLL,he,norm_zero]
 apply rowC _ _ (fun j _=>urge s i j) a; exact fun j k=> (Tye.birth_l i j (castX s) _ _ (mem_filter.mp k).2).symm -- tune
lemma ρ_K(j:JS) : (∑ i:JS, jLL s i j) ≤ Tenant.quota:=by
 let a:= (boxA s).symm (node j.1.1); let F:=univ.filter fun i:JS=> (γS s).val i j≠0; rw [←sum_subset F.subset_univ]; swap
 · intro i _ t; have he:(γS s).val i j=0:=by unfold F at t; simpa using t
   rw [jLL,he,norm_zero]
 refine rowC _ _ (fun i _=>urge s i j) a fun i k=>?_ ; apply (boxA s).injective; unfold a; rw [Equiv.apply_symm_apply]; exact Tye.birth_l i j (castX s) _ _ (mem_filter.mp k).2
variable (V:Support (More n)→Toll (Single n)){q:ℝ}
def tagR (X:Support (More n)): Toll (Single n) :=noteU s⁻¹ (V (actY s X))
lemma slip_v(i j:JS): saleM a (tagR s V) i j=noteU s⁻¹ (saleM a V) i j:=by
 unfold tagR saleM noteU; simp_rw [mul_sum]
 rw [sum_comm]; apply sum_congr rfl; intro k _; rw [sum_comm]; apply sum_congr rfl; intro l _; let f(X:SO):=actY s X
 refine sum_bij (fun X _=> f X) (fun _ _=>mem_univ _) (fun i _ j _ g=> map_injective _ g) (fun i _=>⟨actY s⁻¹ i,mem_univ _,?_⟩) ?_
 · unfold f; ext; simp [actY,sitU]
 intro X _; unfold f; unfold Branch.rent; rw [show (actY s X).card=_ from card_map ..,mul_left_comm]
lemma normU (i j p q:JS): ‖curbV s i j p q‖= U i p * U j q:=by rw [curbV,norm_mul,norm_star]
lemma ore_P {a:ℝ}{q:ℝ}(p:∀ S i j,0 ≤ V S i j)(e:Ledger a V q)(x: JS) : (∑ i:JS,noteU s (saleM a V) x i) ≤ Tenant.quota^2*q:=by
 let W:= saleM a V; let L:=Tenant.quota; have ht:0 ≤ L:=le_trans (by norm_num : (0:ℝ)≤16) quota_bound; unfold noteU; simp_rw [normU]; rw [sum_comm]; -- order
 trans ∑ j:JS,U x j*(L*q)
 · apply sum_le_sum; intro j _; rw [sum_comm]
   apply le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (e.rows j) ht) (norm_nonneg ((γS s).val x j))); rw [mul_sum,mul_sum]; apply sum_le_sum; intro i _; rw [←mul_assoc (U x j)] -- tune
   simp_rw [←Finset.sum_mul]; apply mul_le_mul_of_nonneg_right; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (ρ_K ..) (norm_nonneg _); exact sale_nn p a _ _
 rw [←sum_mul,sq,mul_assoc]; exact mul_le_mul_of_nonneg_right (ρ_R ..) (mul_nonneg ht e.posP)
lemma grainK {a:ℝ}(p:∀ S i j,0 ≤ V S i j)(e:Ledger a V q): Ledger a (tagR s V) (Tenant.quota^2*q):=by
 refine ⟨mul_nonneg (sq_nonneg _) e.posP,fun i=>?_,fun i=>?_⟩
 · simp_rw [slip_v]; exact ore_P _ _ p e _ -- tune
 simp_rw [slip_v]; let W(X):=Function.swap (V X); have hx (j l:JS) :noteU s⁻¹ (saleM a V) j l=noteU s⁻¹ (saleM a W) l j:=by
    unfold noteU; simp_rw [normU]; rw [sum_comm]; apply sum_congr rfl; intro p _; apply sum_congr rfl; intro q _; rw [mul_comm (jLL ..)]; rfl
 simp_rw [hx]; exact ore_P s⁻¹ W (fun X i j=>p ..) e.flip i
end YM.CF.Sour
