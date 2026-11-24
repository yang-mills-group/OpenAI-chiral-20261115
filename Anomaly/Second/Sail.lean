import Anomaly.Second.Pose
import Anomaly.Second.Jets
import YM.SU5.Exchange.Pilot.Bundle
import YM.CF.Hype.Migrate
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
-- Head of regulator as mask tile. Copies beyond positive degree 2 included!
variable {h a c:ℝ} {F : InkD n} {i:Scree.Hub n}
open Bake
variable {q:ℕ}
open Vow QuadClock Nor Larch Leaf Mew Rive
lemma tallK_nook (X:Aura n→ℝ)(s:ℝ)(P:BudgetPoint)(t:Seat n):nook (X*tact s P.B) t=tallB X P.B s t:=rfl
lemma reserve_lever (p i k:ℕ): 1≤reserveT p i k 1:=by
 have h1:1 ≤ stilK k:=by unfold stilK; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k]
 have hf(i:ℕ):(1:ℝ)≤ (i.factorial:ℝ):= Nat.one_le_cast.mpr (Nat.factorial_pos _); unfold reserveT coin_n; simp only [inv_one,one_pow,one_mul,mul_one]; apply one_le_mul_of_one_le_of_one_le; · refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hf i) (hf i)) ?_); exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ h1)) -- argument to hf(i)
 exact one_le_mul_of_one_le_of_one_le (hf _) (Real.one_le_exp zero_le_one)
def grainT(P:BudgetPoint)(C:Pax n)(F:Cusp n): Bag n:= frostC P C-toastC P F
lemma grainCost [Nonempty (Seat n)]{C:Pax n}{F:Cusp n}{x a z:ℝ}(u:Turf C)(S:Aura n→ℝ)(p:∀ i:Aura n,Medal P i.val ∅ (C i) h (S i))(t:1≤ h)(hx:∀ i:Seat n,tallB S P.B z i≤x)(r:Aura n→ℝ)(H: Anuk F r P h)(hg:∀ i:Seat n,tallB r P.B z i≤a): Sectoral P q (grainT P C F) h z (x+a):=by
 have hU(i:Aura n):Herb P q i h (grainT P C F i) ((S+r) i):=by
   let V:=frostCost (q:=q) (p i) (u i) t; let Q:= toastCost (X:=i) (q:=q) H t; unfold grainT; rw [sub_eq_add_neg]; exact V.addR Q.negR
 have hs(o): nook ((S+r)* tact z P.B) o ≤ x+a:=by rw [tallK_nook]; unfold tallB; simp only [Pi.add_apply,add_mul,sum_add_distrib]; exact add_le_add (hx o) (hg o)
 refine ⟨le_trans ?_ (hs (Classical.arbitrary _)),S+r,hU,hs⟩; exact sum_nonneg fun i _=> mul_nonneg (hU i).price (Real.exp_pos _).le
lemma grainReal {C:Pax n}{F:Cusp n}(P:BudgetPoint)(x:Orbit n): giveB (grainT P C F) x=(coldE P C x-fuelV P F x).val:=by
 change _=(Dough (Dwell n)).val (_-_)
 unfold giveB grainT frostC toastC coldE fuelV; simp_rw [Pi.sub_apply,Finset.sum_apply, sum_filter (s:=univ), capR]; simp only [Pi.sub_apply]; rw [sum_sub_distrib,map_sub, map_sum,map_sum]; apply congrArg₂ _ <;> apply sum_congr rfl <;> intro i u
 · by_cases p:x∈ pingMask P i.val; · rw [Set.indicator_of_mem p, if_pos (show pingS P.threshold i.val x.1 from p)]; rfl
   rw [Set.indicator_of_notMem p,if_neg (show ¬pingS P.threshold i.val x.1 from p)]; rfl
 split_ifs <;> rfl
variable {J:Type}[LinearOrder J][Fintype J]
local notation "PM"=> P.supportExponent+1+1
lemma altAura {σ:J→Seat n}{X:Key J→Pax n}{Y:Key J→Cusp n}{G:Key J→RegBudget n}{Z:Key J→ℂ}(u:1≤ h)(t:Diesel P σ h a c X Y G Z)(w:Key J)(p:w∈hill J): Sectoral P q (grainT P (X w) (Y w)) h PM (a+c)∧∀ i:Orbit n,FleetS P.threshold i.1→ giveB (grainT P (X w) (Y w)) i=Z w • (1:FC (Dwell n))+ (exponentL P (G w) i.1).val:=by
 obtain ⟨b,z,T⟩:=t.wage; obtain ⟨S,H,M⟩:=T w p; obtain ⟨V,Q,W⟩:= t.sponsor w p
 have hx:0 ≤ b:= le_trans (b:=(tallB S _ _ 0)) (sum_nonneg fun x v=> mul_nonneg ((H x).wage (zero_le_one.trans u)) (Real.exp_pos _).le) (M _)
 have ha:b≤a:= (le_mul_of_one_le_left hx (reserve_lever ..)).trans_eq z
 refine ⟨grainCost (t.spur w p) S H u (fun i=> (M i).trans ha) V Q W,?_⟩
 intro i g; rw [grainReal,t.stipend w p i g,add_sub_cancel_right]; rfl
end YM.CF.Sour
