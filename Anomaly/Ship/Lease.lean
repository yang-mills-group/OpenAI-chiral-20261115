import Anomaly.Ship.Lender
import Anomaly.Ship.Caret
import Anomaly.Ship.Icebox
import Anomaly.Ship.Pod
import Anomaly.Ship.TwinZ
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
set_option maxHeartbeats 700000
local notation "F₀"=> Orbit (mid N B)
open Py Oise Swell Sault Pastry Rue
variable {R:GramM (mid N B)}{L:Side}{wL:Odd L.val}{i_:ℕ}{X: Pricing i_ L wL (Thread i_)}{e':ℝ}(U:Grasp X B e')(C:Scree.Loom (mid N B))
variable {A:I→Bag (mid N B)}{Y:I→ phy (mid N B)}{D:Finset I}{σ:I→ Site (mid N B)}
variable {E:Key I→RegBudget (mid N B)}{K:Key I→ForceBudget (mid N B)}{x y:ℝ}{r:Key I→ℂ}
variable {T:Occlus R.p}{S:ℕ}{Ω:I→RegBudget (mid N B)}{G:I→Cusp (mid N B)} {t:I→ℂ} {Q:Key I→RegBudget (mid N B)}{V:Key I→ForceBudget (mid N B)}
variable {a b:I→ Aura (mid N B)→ℝ}(H:∀ (i:I)(X:Aura (mid N B)),Sour.Flight R.p q X h (A i X) (a i X) (b i X)) (p: Thrust U C H T D S σ Y E K r Ω G t Q V)
local notation "Sσ"=>Cube.node∘σ
variable {e d k:ℝ}(u:Furnace R D q σ E K r h e d k)(c:CrestPay R.p (Cube.node∘σ) E (R.p.supportExponent+1) h e)
variable (hv:8≤R.p.B)(hq:T.η=(R.p.B:ℝ)⁻¹)(hh:1≤h)
local notation "EF"=> (clearRoot σ (E+Q))
local notation "VK"=> (bustle (Sσ) (K+V))
local notation "Dκ"=> yσE R.p T
local notation "Zκ"=> yσF R.p T
local notation "PQC"=> R.p.supportExponent+T.η
include p hh hq hv u c
lemma limited : CrestPay R.p Sσ (E+Q) PQC h (e+Dκ) ∧ GrowPay R.p Sσ (K+V) PQC h (k+(Zκ+Zκ)):=by
 let L:=p.earns; have hx:0< h:=zero_lt_one.trans_le hh; have hp:= T.hη
 have ht:T.η≤1/2:=by rw [hq,one_div]; apply inv_anti₀ (by norm_num); exact_mod_cast Nat.le_trans (by norm_num) hv
 refine ⟨CrestPay.fuse (CrestPay.sail c (by linarith only [ht]) hx) (CrestPay.sail L.1 (by linarith only [hp]) hx), GrowPay.fuse (GrowPay.sail (growG_t u.kV u.San hx) (by linarith only [ht]) hx) L.2⟩
lemma lease_ticket : Notice σ EF VK ∧ (∀ i, νTip EF i=νTip E i+Ω i ∧ emberTip VK i=emberTip K i+emberTip (mkCup R.p R.K (zealPitch A a b H) S G) i) ∧ ∀ (l:List I), l.length ≤ S → ψS Sσ l → ∀ v:F₀, IsStarProjection (Dial.spar i_ R.J.M (C v)) → Injective (priorP v.2) → FleetS R.p.threshold v.1 → (Leit D l).Pairwise (fun i j=>Commute (Y i v) (Y j v)) → tipI (fun z:Key I=> denZ (color_b R R.beta (R.F+EF z) R.slip (R.K+VK z) (R.v + (r z+α_ξ t z))) U C v) l= acts (((Leit D l).map fun i=>Y i v).prod) (tipI (fun z:Key I=> denZ (color_b R R.beta (R.F+E z) R.slip (K z) (R.v+r z)) U C v) (Leit (univ\ D) l)):=by
 let k':=(K+V); have ht:(E+Q) 0=0:=by rw [Pi.add_apply,u.E0,p.live.1,add_zero]
 let w:= limited U C H p u c hv hq hh; obtain ⟨Z,T⟩:= cropEra ht σ w.1.toSiltQ w.2.toBudK -- order
 refine ⟨Z,fun i=>?_,?_⟩
 · let x:=p.first i; obtain ⟨h,h₁⟩:=T i
   have hv:emberTip (K+V) i=emberTip K i+emberTip V i:=funext₂ fun s j=> tip_A (u.kV.toll s j) (p.earns.2.toll s j) [i]; exact ⟨h.trans ((show νTip (E+Q) i=νTip E i+νTip Q i from funext₂ fun s j=> tip_A (u.nV.token s j) (p.earns.1.token s j) [i]).trans (congrArg (νTip E i+·) x.1)),h₁.trans (hv.trans (congrArg _ x.2))⟩
 intro l x t' V' p' hp hf W
 have he:k' 0=R.K:=by unfold k'; rw [Pi.add_apply,u.K0,p.live.2,add_zero]
 let r':= fun z:Key I=> r z+α_ξ t z; have hw:River r' :=dub_V u.lvl (rer_C t)
 have h:= (eat_sweep U C ht σ w.1.toSiltQ w.2.toBudK he.symm r' l t' V' p' hw).tip l (List.Sublist.refl _)
 have hP:=p.read l x t' V' p' hp hf W
 simp_rw [add_assoc] at hP; exact h.symm.trans hP
-- budgets on arbitrary Key resizes of the Keys AFTER receipt (noconsumption onto new requests on top of this one).
lemma lease_wall (w:ℝ)(k':ℕ)(Tz:packF w R.p.B k')(x:Force_M R.p.B Sσ k')(pW:1 ≤ w)(pE:0≤e+yσE R.p T)(pK:0≤ k+(yσF R.p T+yσF R.p T)) : ∀ z:Key I,(∀ i, ‖z i‖≤w) → IncX primeU (rim_C Sσ (E+ Q) z) R.p h (chillCash R.p.B * (e+yσE R.p T)) ∧ (let P:=k+(yσF R.p T+yσF R.p T); Dark primeU (VK z) R.p h (k'*w*P+chillCash R.p.B*P+chillCash R.p.B*P)) :=by
 let v:=limited U C H p u c hv hq hh
 rw [hq] at v; intro z hx; exact ⟨harvest_E x Tz hv pW pE (zero_lt_one.trans_le hh) z hx v.1, harvest_K x Tz hv pW pK (zero_lt_one.trans_le hh) z hx v.2⟩ -- tune z implicit maybe n
end YM.CF.Vow.TreasuryFog
