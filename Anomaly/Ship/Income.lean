import Anomaly.Ship.Growth
import Anomaly.Ship.Glass
import Anomaly.Apert.Lift
import Anomaly.Apert.Price
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
open Neon Bake Rive QuadClock Stilo Roots
-- earned Root-v keyed regulator rep. Analytic both fresh and old together.
-- expose First pins on separated Θ tests
variable {N B:Side}
local notation "Fᴷ" => mid N B
variable {A:Key I→ I→ Bag (mid N B)}
variable {a b: Key I→I→ Aura (mid N B)→ℝ} {K:Key I→ForceBudget (mid N B)}
variable (H:∀ z∈hill I,∀ i:I,∀ X:Aura (mid N B),Flight P q X h (A z i X) (a z i X) (b z i X))
variable {D:Finset I}{σ:I→Site (mid N B)}{Ω:Occlus P}
variable (T: Crews D K (Cube.node∘σ) Ω A H) (u:1≤ h)
local notation "Θ"=>presse H
variable(m:ℕ)
local notation "YX" x:max=> lensCells (K x) (Θ x) m
local notation "Yφ" x:max=> lensG (P:=P) (K x) (Θ x) m
local notation "Aφ"=> (P.supportExponent+Ω.η+Ω.η)
local notation "Vφ"=> (Aφ+Ω.η)
local notation "Sσ"=>Cube.node∘σ
local notation "T_N"=> lensG (P:=P) (K 0) (Θ 0) m
local notation "σ_h" z:max=> (Yφ z) z
variable {l:ℕ}{η v μ:ℝ}
variable (J: I→ RegBudget (mid N B))(G:I→Cusp (mid N B))(t0:I→ℂ)(x:I→ArcΦ)(Tp:Ids (mid N B))
local notation "σE"=> polish (K:=K) H m J Tp
local notation "σG" z:max=> mkCup P (K z) (Θ z) m G
-- v-analytic orientation.E dismissed offset.
variable (W:∀ i:I,Neon.Ice l (σ i) P h η v μ (coldE P (τι (lensG (P:=P) (K 0) (presse H 0) m) [i])) (J i) (G i) (t0 i) (x i))
open Py
include H W T u
lemma energyIncome : CrestPay P Sσ (polish (K:=K) H m J Tp) (P.supportExponent+Ω.η+Ω.η) h (yσE P Ω):= by
 let Q:= Yarm (K:=K) H m; let f(z:Key I):= cast_E (Q z) Tp; let p:= Polish_ports H T u m J G t0 x Tp W; let h(i):=(simple_bill H T u m i)
 refine growE_t f ⟨fun i=>(p.1 i).1,fun i=>(p.1 i).2⟩ (fun z v=>?_) (fun i V=> bScale _ ((h _).2 _) _) (fun i w=>?_) (zero_lt_one.trans_le u)
 · obtain ⟨a,b,r,R⟩:= T.wing z v; obtain ⟨p1,p2⟩:= (lowLens Ω (K z) (Θ z) Sσ q _ R m u Tp z v).1
   exact ⟨_,p1,p2⟩
 let L:= Mew.Cue I i; have ht:2 ≤ L.length:=by have hx:1 < i.card:=(mem_filter.mp w).2.1; unfold L Mew.Cue; rw [Finset.length_sort]; omega
 exact funext₂ fun x v=> (pulse_I Q J Tp (fun i=>(h i).2) x v L (Finset.sort_nodup ..) ht).symm
omit H W T u
open Hope
-- uniform service in lens SanB with rate (Σ+η), Gamma κ choice. no phase resizing required at v≠0.
lemma sanitize (x a':ℝ)(U V:ForceBudget n)(p:SanB U (giftK P η) P h (fun _=>x))(t:SanB V (giftK P η) P h (fun _=>a')) : SanB (U+V) (giftK P η) P h fun _=>x+a' :=by obtain ⟨r,s,u⟩:=p.bit; obtain ⟨L,p,q⟩:= t.bit; refine ⟨⟨r+L,fun i=> Roots.dom_h _ _ _ (s i) (p i),fun i=>?_⟩⟩; simp_rw [Pi.add_apply, mul_add,sum_add_distrib]; exact add_le_add (u i) (q i)
lemma san_minus(x a':ℝ)(U V:ForceBudget n)(p:SanB U (giftK P η) P h (fun _=>x))(t:SanB V (giftK P η) P h (fun _=>a')) : SanB (U-V) (giftK P η) P h fun _=>x+a':=by
 rw [sub_eq_add_neg]; refine sanitize _ _ _ _ p ?_; obtain ⟨r,V0,k⟩:= t.bit; refine ⟨⟨r,fun i=>?_,k⟩⟩; rw [← neg_one_smul ℂ]; simp only [Pi.smul_apply]; simpa only [norm_neg,norm_one,one_mul] using dúe i _ (V0 i) (-1:ℂ)
lemma cash_tune (F V:RegBudget n)(x a':ℝ) (p:ForgeB F (filmK P η) P h (fun _=>x))(t:ForgeB V (filmK P η) P h (fun _=>a')): ForgeB (F+V) (filmK P η) P h (fun _=>x+a'):=by
 obtain ⟨r,s,u⟩:=p.bit; obtain ⟨L,p,q⟩:=t.bit; refine ⟨⟨r+L, (fun i=> Larch.prop_add _ _ (s i) (p i)), fun i=>?_⟩⟩; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add (u i) (q i)
lemma CrestPay.fuse {E W:Key I→RegBudget n}{U:I→Seat n}{a c:ℝ}(p: CrestPay P U E η h a)(t:CrestPay P U W η h c): CrestPay P U (E+W) η h (a+c):=by
 refine ⟨⟨fun i x w y k u=>congrArg₂ (·+·) (p.blank _ x w y k u) (t.blank _ x w y k u), fun i v=> dub_V (p.token i v) (t.token i v) ⟩, fun i v=>?_⟩
 rw [show νΦX (E+W) i=νΦX E i+νΦX W i from funext₂ fun x y=>tip_A (p.token x y) (t.token x y) (Mew.Cue I i)]; exact cash_tune _ _ _ _ (p.yard i v) (t.yard i v)
lemma GrowPay.fuse {F V:Key I→ForceBudget n}{U:I→Seat n}{a c:ℝ}(p:GrowPay P U F η h a)(t:GrowPay P U V η h c): GrowPay P U (F+V) η h (a+c):=by
 refine ⟨⟨fun i x w y k u=>congrArg₂ (·+·) (p.quiet _ x w y k u) (t.quiet _ x w y k u),fun i v=> dub_V (p.toll i v) (t.toll i v)⟩,fun i v=>?_⟩
 rw [show νΦK (F+V) i=νΦK F i+νΦK V i from funext₂ fun x y=> tip_A (p.toll x y) (t.toll x y) (Mew.Cue I i)]; exact sanitize _ _ _ _ (p.sap i v) (t.sap i v)
local notation "ψN"=> inkF (K:=K) H m G
include H W T u Tp
lemma tallyK (n':ℕ)(e:∀ i∉ D,G i=0)(pv:GapN σ P.B l n') (qK:0 ≤ v) (pE:3*Ω.η ≤2) (uQ:(n':ℝ)*v+Ω.γ*(1-degreePrice P.B Ω.γ Ω.η)⁻¹≤1)
    (hK:Ω.γ+ Real.exp 1*(Ω.γ*(1-degreePrice P.B Ω.γ Ω.η)⁻¹ +n'*v) ≤100*Ω.γ):
    (∀ i:I,emberTip ψN i=emberTip (mkCup P (K 0) (Θ 0) m G) i)∧ GrowPay P Sσ ψN (P.supportExponent+Ω.η) h (yσF P Ω+yσF P Ω):=by
 refine ⟨Crews.leafTip H T u m G e, growG_t (Polish_ports H T u m J G t0 x Tp W).2.2.2 ?_ (zero_lt_one.trans_le u)⟩
 intro z t; obtain ⟨A',B,r,R⟩:= T.wing z t; choose q' V f S using fun i=>(W i).grant; let h(w:Key I)(v:w∈hill I):=glowMoney _ _ _ R m G q' V S f u qK pv pE uQ hK w v; unfold inkF
 exact san_minus _ _ _ _ ⟨_,(h z t).1,(h z t).2⟩ ⟨_, (h 0 roots).1,(h 0 roots).2⟩
end YM.CF.Vow.TreasuryFog
