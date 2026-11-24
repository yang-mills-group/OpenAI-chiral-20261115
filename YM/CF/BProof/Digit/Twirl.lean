import YM.CF.BProof.Digit.Quilt
import YM.CF.BProof.Stage.Watch
import YM.CF.Pso.Azure
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Digit
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
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Push.AbsoluteSums Trees Mew Floral
open scoped YM.CF.Mew
variable {U:Set ℂ} {B:ℂ→Cusp n}{K:ℂ→Rinse (Seat n) (Copy n)}
abbrev PlayX (U:Set ℂ)(F:ℂ→Vow.Cusp n):Prop:=∀ X D i, Hol U (fun z=> F z X D i)
abbrev PlayC (U:Set ℂ)(k:ℂ→Rinse (Seat n) (Copy n)):Prop:=∀ X D Y i,∀ (F:ℂ→ Copy n), Hol U (fun z=> F z i)→ Hol U (fun z=> k z X D Y (F z) i)
variable (e: PlayX U B) (p:PlayC U K)
open PowerSeries
lemma sp_hol(c:ℝ){F:ℂ→ Cipher n}(v: Hol U F): Hol U fun t=>c • F t:=v.const_smul c
include e p
lemma play_k (j:ℕ)(X:Aura n)(D)(i:Orbit n): Hol U fun z=> coeff j (Cadre.chip (K z) (B z) X D) i:=by
 induction j using Nat.strong_induction_on generalizing X D with
 |h j ih=>
    cases j with
    |zero=>simp_rw [Cadre.peg]; exact e _ _ _
    |succ j=>
       have hv(z:ℂ): coeff (j+1) (Cadre.chip (K z) (B z) X D)=((j:ℝ)+1)⁻¹ • coeff j (Cadre.stepL (K z) (Cadre.chip (K z) (B z)) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       simp_rw [hv,Pi.smul_apply, Cadre.ore, Finset.sum_apply]; apply sp_hol; apply DifferentiableOn.fun_sum; intro i _; apply DifferentiableOn.fun_sum; intro G v; apply p; simp_rw [coeff_prod, Finset.sum_apply,Finset.prod_apply]; exact DifferentiableOn.fun_sum fun a y=> DifferentiableOn.fun_finsetProd fun m w=> ih (a m) (Nat.lt_succ_of_le (le_trans (single_le_sum (fun i _=> Nat.zero_le (a i)) w) ((mem_finsuppAntidiag.mp y).1.le))) m _
lemma play_r(j:ℕ)(X:Aura n)(D)(i:Orbit n): Hol U fun z=> coeff j (Cadre.nutL (K z) (B z) X D) i:=by
 cases j; · simp_rw [tick_r,Pi.zero_apply]; exact differentiableOn_const _ -- Pi simp tune
 rename_i j; unfold nutL; simp_rw [sprig,Pi.smul_apply, Cadre.front, Cadre.rill,map_sum,grate, coeff_mk, Finset.sum_apply]; apply sp_hol; apply DifferentiableOn.fun_sum; intro i _; apply DifferentiableOn.fun_sum; intro G v; apply p; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; exact DifferentiableOn.fun_sum fun a y=> DifferentiableOn.fun_finsetProd fun m w=> play_k e p _ m _ _
namespace Cash
variable {W:ℝ} {Z:ℂ→RegBudget n}{δ:ℕ}(A:ℂ→ blazeK n)(m:Cash P)(μ:ℂ→ Aura n→ℝ)(F:ℂ→ Bag n)(s:m.Warrant)(T:∀ z∈U,m.grapes (A z) (B z) δ W)(R:∀ z∈U,Pitch P W δ (K z) (μ z) (fun i Y=> F z Y i))(t:∀ z∈U,m.vines (A z) (μ z) 1)(k:1≤W)
include T k e p t R
lemma rem_hol(d:IsOpen U)(v:D⊆X.val)(i:Orbit n): Hol U fun z=> Stax.rem_X (P:=P) (B z) (K z) X D i:=by
 unfold rem_X lasting zenS; split; swap; exact differentiableOn_const _
 next hx=>
    obtain ⟨Y,y,x⟩:=hx; have hp:= zero_le_one.trans k; refine Complex.differentiableOn_tsum_of_summable_norm ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num)).mul_left (2*m.er/loom_v 0 0 (widthK n P.B) 2 X)) (fun j=>play_r e p j _ _ i) d (fun j z w=>?_)
    let M:= nutL (cribR (μ z)) (A z); let c:= clock₂ (t z w); have a:= deck _ _ (T z w).fr (K z) _ (R z w) hp X D v j; have hv:=(R z w).dice
    dsimp only
    rw [a.merit.same i (Y,i.2) x (fun _ _=>rfl)]; apply le_trans (a.merit.capF k (Y,i.2) y); apply Cadre.palm_ M _ m.κ c.slope _ _ _ _ _ X D v j
    · exact fun _ _ _=> Cadre.heatR (μ z) (A z) (fun X D v=> ((T z w).fr X D v).merit.wage hp) hv _ _
    exact fun o j=> c.worth Ψk le_rfl (show 0+wΨ≤wu P-wΨ*2 from (by unfold wu wΨ; linarith [P.exponent_pos])) _ (fun _ _ _=>tick_r _ _) (oreL0 _ _) o j
lemma lamp_hol (d:IsOpen U)(v:D⊆X.val)(i:Orbit n): Hol U fun z=> lamp (P:=P) (B z) (K z) X D i:=by
 unfold lamp; simp_rw [Pi.add_apply]; refine ((e X D i).add ?_).add (rem_hol e p A m μ F T R t k d v i); unfold birthL; split; exact p _ _ _ _ _ (differentiableOn_const _); exact differentiableOn_const _
variable (u:∀ j V,Hol U fun z=> Z z j V)
include u s
lemma twist_hol (d:IsOpen U)(u':U.Nonempty) (X:Aura n)(V:Orbit n) : Hol U fun z=> Nu P (Fine (lamp (P:=P) (B z) (K z))) (Fine (B z)) (Z z) X V:=by
 unfold Nu zenS; split; swap; exact differentiableOn_const _
 let M(z):= mix m (A z) (μ z); let T₀(z:ℂ)(v:z∈U):= logPay s (T z v) k (R z v) (t z v)
 have hz: 0≤P.supportExponent+1+1:=by linarith [P.exponent_pos]
 obtain ⟨z,g⟩:=u'; have hy:0≤ m.rate:= (ready_pos _ _ (T₀ z g).1).le
 exact ((Rive.lore_pit _ P k (fun X V=> lamp_hol e p A m μ F T R t k d (D:=∅) (X:=X) (empty_subset _) V) M hz (fun z v=> (T₀ z v).1) (fun z v=>(T₀ z v).2.1) hy s.earn d X V).sub (Rive.lore_pit _ P k (fun X V=>e X ∅ V) M hz (fun z v=> (T₀ z v).1) (fun z v=>(T₀ z v).2.2.1) hy s.earn d X V)).sub (DifferentiableOn.fun_sum (fun j _=>u j V.1))
end Cash
end YM.CF.Sour.Digit
