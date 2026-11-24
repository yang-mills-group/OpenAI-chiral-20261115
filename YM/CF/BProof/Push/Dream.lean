import YM.CF.BProof.Push.Furnace
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau.PushA
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Iva Lilt Salt Palot Floral Sour Haro Tap Sour.BondL Mew
open scoped YM.CF.Mew
open Reef Taxi.Denn
variable {κ Q γ u Γ σ H r Ue Zc Ce:ℝ}{q:Clip}{R:PathData SU.group}{L:ℕ}{t: Mint P R q h σ Q κ Γ n m L} -- Q=C_p not H
-- match for twoy. Initial rank absolute cost `u`, δ diff input; gate differences exactly Lips2.
structure Tune (P:BudgetPoint)(h γ Z H u:ℝ)(F Y:RegBudget n)(A V B K:Cusp n)(ε:ℝ):Prop where
 lm : 0 < ε
 hm : ε ≤ 1
 near : Books P (Y-F) h (ε*u/4)
 e : Binder P h (kδ P+wΨ) (lightP (B-A)) (3*ε*γ)
 q : Flaws P h (kδ P+wΨ) (B-A) (3*ε*Z)
 t : Heats P h (kδ P) (K-V) (ε*H)
abbrev alpha_v(P:BudgetPoint)(L:ℕ)(F G:RegBudget n):= aora P L F-aora P L G
namespace Mint
variable (t': Mint P R q h σ Q κ Γ n m L) (C:Cart n m)(x:Ids n) {B K A V:Cusp n}{Y F:RegBudget n}{M:Tulip.Male}{j:ℕ}{Θ:Finset (Scree.Hub n)}{U Vb v w:ℝ}{ε Hstar X:ℝ}
variable (g0:Birch A V F P w Zc H Vb u γ h M j Θ) (g1:Birch B K Y P v Zc H U u γ h M j Θ)(e:Tune P h γ Zc H u F Y A V B K ε) (cc:Crowd P h (8*γ) (8*Zc) (4*Hstar) X r) (hU:(1+CH P m Γ*‖Complex.reCLM‖)*u ≤ Ue) (hw:H+|glow_W P q σ Q Γ Ue L|+Ue≤Hstar)
local notation "ψ"=> alpha_v P L F Y
local notation "Kx"=> CH P m Γ
local notation "J"=> P.threshold^2*|ψ|
include e t' g0 g1
lemma psi_n : P.threshold^2*|ψ| ≤ ‖Complex.reCLM‖*(ε*u/4):=by
 unfold alpha_v; rw [abs_sub_comm,← aora_diff g1.pre.firm g0.pre.firm t'.nn] -- no field.
 exact (t'.ready_A 0 (Classical.arbitrary _) (congr_p g1.pre.firm g0.pre.firm e.near)).2.2.2.2.2.1
include hU
lemma cash_v : u + Kx * J ≤ Ue :=by
 apply le_trans _ hU; have hx:= psi_n t' g0 g1 e; have hp:=Books.pos (weaken g1.pre.firm) t'.nn; let K:= ‖Complex.reCLM‖; have hn:ε*u/4≤u:= (div_le_self (mul_nonneg e.lm.le hp) (by norm_num : (1:ℝ) ≤ 4)).trans ((mul_le_mul_of_nonneg_right e.hm hp).trans_eq (one_mul _))
 exact (add_le_add_right (mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))) (priceCH P m Γ t'.ha).le) _).trans_eq (by ring)
lemma er_v : u+Kx*(P.threshold^2*|(0:ℝ)|)≤Ue:=by rw [abs_zero,mul_zero,mul_zero]; exact (add_le_add_right (mul_nonneg (priceCH P m Γ t'.ha).le (mul_nonneg (sq_nonneg _) (abs_nonneg _))) u).trans (cash_v t' g0 g1 e hU)
local notation "RL_"=> (regC P q σ Q κ Γ)
private lemma χ_v : ε*u/4+Kx*J≤ ε*Ue/4:= calc
    _ ≤ ε*u/4 + Kx*(‖Complex.reCLM‖*(ε*u/4)) := add_le_add_right (mul_le_mul_of_nonneg_left (psi_n t' g0 g1 e) (priceCH P m Γ t'.ha).le) _
    _ = ε*((1+Kx*‖Complex.reCLM‖)*u)/4:=by ring
    _ ≤ _:= by gcongr; exact e.lm.le -- tune
variable (v': PushA.Crowd P h γ Zc H X r) -- remove
include C
lemma aligned : rise P L Y ψ= rise P L F 0 ∧ Books P (ascent P L Y ψ C R q-ascent P L F 0 C R q) h (ε*((RL_+1)*Ue)/4):=by
 obtain ⟨hz,t,hc,-,hv⟩:= t'.grow C ψ (fun _=>False) (Or.inr fun _ p=>p.elim); constructor
 · unfold rise lamp; rw [Cart.eras,add_zero,aora_add t'.nn g1.pre.firm hz,hv]; unfold alpha_v; abel
 unfold ascent lamp; rw [Cart.eras,add_zero,Cart.Sr_zero,add_zero,add_sub_right_comm,← brol_diff (addT P g1.pre.firm hz) g0.pre.firm t'.nn]; have ht:= χ_v t' g0 g1 e hU; have hn:0 ≤ ε*u/4:=by have:=e.lm; have:=Books.pos (weaken g1.pre.firm) t'.nn; positivity
 let Fp:=addT P (congr_p g1.pre.firm g0.pre.firm e.near) hz; have he:IncX Utrue (Y+Er n ψ-F) P h (ε*Ue/4):=by rw [add_sub_right_comm]; exact upE Fp ht
 refine Books.mono (Books.plus (weaken (t'.ready_A 0 (Classical.arbitrary (Ids n)) he).2.2.1) hc) ?_; exact (add_le_add_right ((le_add_of_nonneg_left (a:=Kx*J) hn).trans ht) _).trans_eq (by ring)
lemma thrill : Heats P h (kδ P) (ash P L Y ψ C R q x K-ash P L F 0 C R q x V) (ε *( H+|glow_W P q σ Q Γ Ue L|+Ue)):=by
 have h0:0 ≤ u:=Books.pos (weaken g0.pre.firm) t'.nn; have hp:= e.lm.le; have hUe:0 ≤ Ue:=(add_nonneg h0 (mul_nonneg (priceCH P m Γ t'.ha).le (mul_nonneg (sq_nonneg _) (abs_nonneg _)))).trans (cash_v t' g0 g1 e hU); obtain ⟨hz,t,hc,v,hv⟩:= t'.grow C ψ (fun _=>False) (Or.inr fun _ p=>p.elim)
 unfold ash lamp; rw [Cart.eras,add_zero,Cart.Zr_zero,add_zero, add_sub_right_comm, add_sub_add_comm,← truce_diff (addT P g1.pre.firm hz) g0.pre.firm t'.nn]; have he:IncX Utrue (Y+Er n ψ-F) P h (ε*Ue):=by rw [add_sub_right_comm]; exact upE (addT P (congr_p g1.pre.firm g0.pre.firm e.near) hz) ((χ_v t' g0 g1 e hU).trans (div_le_self (by positivity) (by norm_num)))
 refine Wallet.mono (Heats.plus (Heats.plus e.t (t'.ready_A 0 x he).1) v) ?_; rw [show glow_W P q σ Q Γ (ε*Ue) L= ε *glow_W P q σ Q Γ Ue L from (by unfold glow_W phase_v; ring),mul_add,mul_add]; exact add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left (le_abs_self _) hp) _) (((le_add_of_nonneg_left (a:=Kx*J) (show 0≤ε*u/4 by positivity)).trans (χ_v t' g0 g1 e hU)).trans (div_le_self (by positivity) (by norm_num)))
include cc hw
lemma paidK : Pressed P (burn P B (ash P L Y ψ C R q x K)-burn P A (ash P L F 0 C R q x V)) h (ε* Cog_P P X r):=by
 refine Case.lips (Case.mk e.lm e.hm (heats t' C x g0 cc (er_v t' g0 g1 e hU) ((add_le_add_left (add_le_add_right (le_abs_self _) _) _).trans hw) trivial) e.e e.q ?_ g1.quench) cc; exact Wallet.mono (thrill t' C x g0 g1 e hU) (mul_le_mul_of_nonneg_left hw e.lm.le)
end Mint
end YM.CF.Beau.PushA
