import Anomaly.Basis.Tempo
/-! normalize Offshell Space. Each column comparison is charged on THAT
 regulator rather than specializing at a mean momentum. credit Vita lemma. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill Buffered StressExchange Reed
open Py Neon Vow.TreasuryFog
variable {N B M L:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h x₀ y c s r:ℝ}{k q j l:ℕ}
local notation "Tc"=> mid N B
variable {g:ℕ}{wL:Odd L.val}{H:Pricing g L wL (Thread g)} {U:Grasp H B d}{R:GramM (mid N B)}{T:Scree.Loom (mid N B)}
variable (F:Ξθ→Bag (mid N B)) (X:Ξθ→ Mark (mid N B)) (V:Ξθ→phy (mid N B)){o:Site (mid N B)}
local notation "Κ" x:max u:max y:max G:max=> Totem U R T q l k j o x u y G
variable (p:1 ≤ h)
-- uniform cost of Σ by sum Gram grants linear charges on all responses. small drifts at estimate issue captured once. Ξ uniform *FULL* basis.Direction.Char motion not needed: frames.
variable (L':∀ i:Ξθ,Totem U R T q l k j o (F i) (X i) (V i) (cue_Φ s h i) h r a c (ΘS_F s) y)
local notation "Z"=> Ξθ
-- combos.E.W.B. not tied CAPS.Shape.T.Weight momentum. use tΘ correction norm fixed.H. Bounded.
include p L'
lemma contracted (g:0<t)(u:t*hc_P=s) :∃ C:Ξθ→Ξθ→ℂ, (∀ i, ∑ k:Ξθ, ‖C k i‖≤ (1/2:ℝ)) ∧ ∀ i:Ξθ,
 Totem U R T q l k j o (∑ a:Ξθ,C a i • F a) (∑ a:Ξθ,C a i • X a) (∑ a:Ξθ,C a i • V a) (cue_Φ t h i) h r (∑ k:Ξθ, ‖C k i‖ * a) (∑ k:Ξθ, ‖C k i‖*c) 0 (∑ k:Ξθ, ‖C k i‖*y):=by
 choose G A μ H' using fun i=> (L' i).bill.yard.price; let τ:Ids Tc:=Classical.arbitrary _
 let M(i):=singlePole τ (F i) (μ i) (node o); let Ψ(i):=pilasters l R.p o (M i)-cue_Φ s h i
 let K(i):= (L' i).bill.stamp (G i) (A i) τ (μ i)
 have ht(i): cue_Φ s h i +Ψ i= pilasters l R.p o (M i):= add_sub_cancel .. -- orientation check
 have hz(i):InΦ (Ψ i):= subCh _ _ (αout (M i) (K i).rights p) (sCap ..)
 have hZ(i):‖(Ψ i).1‖≤ ΘS_F s∧‖(Ψ i).2‖*h^2 ≤ ΘS_F s:= (K i).estimate
 have hw:0<s:=u ▸ mul_pos g hcP_ge
 obtain ⟨R,V',W'⟩:= Δquo s hw p Ψ hZ hz; let Hc:= ζFare R s t;
 refine ⟨Hc,fun i=>?_ ,fun i=>?_⟩
 · refine (sum_le_sum (fun j (_:j∈(univ:Finset Z))=> Φfrost s t hw p g Ψ hz R V' W' u _ _)).trans ?_; rw [sum_const,card_univ,nsmul_eq_mul]; exact duty_L s t hw p g Ψ hz R V' W' u -- order frost p & g
 have h(i): Totem U ‹GramM (mid N B)› T q l k j o (F i) (X i) (V i) (cue_Φ s h i + Ψ i) h r a c 0 y:=by rw [ht]; exact {(L' i) with bill:= drill_ray (L' i).bill τ (μ i)}
 let Lx:= Totem.span p univ _ _ _ _ _ _ _ _ (fun x _=> (h x).scaleP p (Hc x i)); have L':∑ x:Ξθ,Hc x i • (cue_Φ s _ x+Ψ x)=cue_Φ t _ i:= Θport s t hw p g Ψ hz R V' W' u i
 simp_rw [L',mul_zero,sum_const_zero] at Lx; exact Lx
end YM.CF.Swell.Porticus
