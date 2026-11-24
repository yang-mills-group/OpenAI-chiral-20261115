import Anomaly.Ship.DeckFlux
import Anomaly.Ship.DeckMelt
import Anomaly.Ship.Cue
import Anomaly.Ship.Ped
import Anomaly.Ship.Salary
import Anomaly.Ship.Tines
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Swell Bake Rive Leaf QuadClock Prism
local notation "Φχ"=> Seat n
local notation "Υ"=> hill I
local notation "Δp" => P.supportExponent
local notation "bυ"=> ((P.B:ℝ)⁻¹)
open Py Neon Hope
variable {E:Key I→RegBudget n}{F:Key I→ForceBudget n}{a x y u c:ℝ}{σ:I→Seat n}
-- Tone eligibility after key masks. old F at zero for F*.San missions replace in sweep.RESULT not assuming convergence.
structure SiltQ (E:Key I→RegBudget n)(σ:I→Seat n): Prop where
 blank : ∀ X:Scree.Hub n, Hush σ X.val.2 fun z=> E z X
 token : ∀ (X:Scree.Hub n)(V:Pane n), River fun z:Key I=> E z X V
structure CrestPay (P:BudgetPoint)(σ:I→Seat n)(E:Key I→RegBudget n) (a h u:ℝ) :Prop extends SiltQ E σ where
 -- alternative for higher Reg support through all call budget
 yard : ∀ i∈ manySet σ,ForgeB (νΦX E i) (filmK P a) P h (fun _=>u)
structure GrowPay(P:BudgetPoint)(σ:I→Seat n)(F:Key I→ForceBudget n) (a h u:ℝ) : Prop extends BudK F σ where
 sap :∀ i∈ trueSet σ, SanB (νΦK F i) (giftK P a) P h (fun _=>u)
noncomputable section RootsGrow
lemma growE_t (Y:Key I→ RegBudget n)(p:SiltQ E σ)(z:∀ i∈hill I,ForgeB (Y i) (filmK P a) P h (fun _=>u))(e:∀ X V,River (fun z:Key I=> Y z X V))(μ:∀ i∈ manySet σ, νΦX Y i=νΦX E i)(hx:0 < h): CrestPay P σ E a h u:=by
 refine ⟨p,fun i U=>?_⟩; rw [← μ i U]; refine onset_t Y hx (filmK P a) ?_ (fun i=>?_) _ z e _
 · intro i j; unfold filmK; split; exact (Real.exp_pos _).le; exact le_rfl
 exact ⟨i.val.1,by unfold filmK; rw [if_pos rfl]; exact Real.exp_pos _⟩
lemma growG_t (p: BudK F σ)(z:∀ i∈ hill I,SanB (F i) (giftK P a) P h (fun _=>u))(hx:0 < h): GrowPay P σ F a h u:=by
 refine ⟨p,fun i x=>insight_t F hx (giftK P a) ?_ ?_ _ z p.toll (Mew.Cue I i)⟩
 · intro i j; unfold giftK; split; exact (Real.exp_pos _).le; exact le_rfl
 · intro i; exact ⟨i.val.1.val.1,by unfold giftK; rw [if_pos i.val.1.property]; exact Real.exp_pos _⟩
lemma pokePay {t} (p:SiltQ E σ)(i:Scree.Hub n)(v:νΦX E t i≠0): poke_F σ i.val.2 t:=by
 intro j w; by_contra h; apply v; funext V; exact husht_B _ _ _ (show Hush σ i.val.2 (fun z=> E z i V) from fun a r b u h=> congrFun (p.blank i a r b u h) V) (p.token ..) (Mew.Cue I t) j h (by simpa [Mew.Cue] using w)
lemma pokeCost {t} (p:BudK F σ)(i:Force n)(v:νΦK F t i≠0): poke_F σ i.val.1.val.2 t:=by
 intro j w; by_contra h; apply v; funext V; exact husht_B _ _ _ (show Hush σ i.val.1.val.2 (fun z=> F z i V) from fun a r b u h=> congrFun (p.quiet i a r b u h) V) (p.toll ..) (Mew.Cue I t) j h (by simpa [Mew.Cue] using w)
lemma CrestPay.sail (p:CrestPay P σ E a h u)(x:y≤ a)(v:0 < h): CrestPay P σ E y h u:=by
 refine ⟨p.toSiltQ,?_⟩; intro i t; obtain ⟨r,V,U⟩:= (p.yard i t).bit; refine ⟨⟨r,V,fun j=>le_trans (sum_le_sum (fun i _=>?_)) (U j)⟩⟩
 refine mul_le_mul_of_nonneg_right ?_ (gradeE _ _ (V _) v.le); unfold filmK; split; exact Real.exp_monotone (mul_le_mul_of_nonneg_right x (Nat.cast_nonneg _)); exact le_rfl
lemma GrowPay.sail (p:GrowPay P σ F a h u)(x:y≤ a)(v:0 < h): GrowPay P σ F y h u:=by
 refine ⟨p.toBudK,?_⟩; intro i t; obtain ⟨r,V,U⟩:= (p.sap i t).bit; refine ⟨⟨r,V,fun j=>le_trans (sum_le_sum (fun i _=>?_)) (U j)⟩⟩
 refine mul_le_mul_of_nonneg_right ?_ (gradeQ _ _ (V _) v.le); unfold giftK; split; exact Real.exp_monotone (mul_le_mul_of_nonneg_right x (Nat.cast_nonneg _)); exact le_rfl
variable {t:ℕ}
variable (uV:Force_M P.B σ t)(pT:packF c P.B t)(pk:8≤P.B) (pc:1 ≤ c)(uA:0≤x)(hx:0 < h)(z:Key I)(r:∀ i,‖z i‖≤ c)
local notation "Vκ"=> (P.supportExponent+(P.B:ℝ)⁻¹)
include uV pT pk pc uA hx r
lemma harvest_K (p: GrowPay P σ F (P.supportExponent+(P.B:ℝ)⁻¹) h x): Dark primeU (bustle σ F z) P h (t*c*x+chillCash P.B*x+chillCash P.B*x):=by
 let D:= trueSet σ; let A:= manySet σ; let X:=D\A
 have hu:A⊆ D:=fun i v=> mem_filter.mpr ⟨mem_univ _,card_pos.mp (lt_trans zero_lt_one (mem_filter.mp v).2.1),(mem_filter.mp v).2.2⟩
 let f(i:Finset I):= Mew.pine i z; have he(i:Finset I):‖f i‖≤c^i.card:=by unfold f Mew.pine; rw [norm_prod]; exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>r i)).trans_eq (Finset.prod_const ..)
 let B(i):= νΦK F i; let K(Y:Finset (Finset I)):= ∑ i∈Y,f i • B i
 have hq:bustle σ F z=K X+K A:=(sum_sdiff hu).symm
 rw [hq]; apply union_F
 · apply tiny_GK X B σ hx c x (fun _ _ i w=>pokeCost p.toBudK i w) (fun _ w=> p.sap _ (mem_sdiff.mp w).1) f (fun i w=> he i) pc pk uA uV.1 uV.2 pT; intro i u; obtain ⟨t,w⟩:=mem_sdiff.mp u; let v:= (mem_filter.mp t).2; have hk:=Finset.card_pos.mpr v.1; have hl: ¬ 1 < i.card:=fun p'=>w (mem_filter.mpr ⟨mem_univ _,p',v.2⟩); omega
 apply sprint_K_var A B σ hx c x (fun _ _ i w=>pokeCost p.toBudK i w) (fun i w=> p.sap _ (hu w)) f (fun i _=>he i) pc pk uA uV.1 uV.2 pT (fun i w=>(mem_filter.mp w).2.2) (fun i w=>(mem_filter.mp w).2.1)
lemma harvest_E (p:CrestPay P σ E (P.supportExponent+(P.B:ℝ)⁻¹) h x): IncX primeU (rim_C σ E z) P h (chillCash P.B*x):=by
 let X(i:Finset I):= Mew.pine i z; have he(i):‖X i‖≤c^i.card:=by unfold X Mew.pine; rw [norm_prod]; exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>r i)).trans_eq (Finset.prod_const ..)
 exact streak_E_var (manySet σ) (νΦX E) σ hx c x (fun _ _ i w=>pokePay p.toSiltQ i w) p.yard X (fun i _=> he i) pc pk uA uV.1 uV.2 pT (fun i w=>(mem_filter.mp w).2.2) (fun i w=>(mem_filter.mp w).2.1)
end RootsGrow
end YM.CF.Vow.TreasuryFog
