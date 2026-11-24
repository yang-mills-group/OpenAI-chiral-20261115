import YM.CF.Mica.Near
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (R E:RegBudget n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
lemma share_V(p:IncX (fun _=>False) R P h a):IncX (fun _=>False) (head_L R) P h a:=by obtain ⟨F,u,z⟩:=p.weight; exact ⟨⟨F,fun i=> easy_W P (u i),z⟩, fun _ v=> v.elim⟩
abbrev cone_D(k p:ℕ):ℝ:= 1+shine_M k p
lemma lake_X (p:IncX (fun _=>False) R P h a)(v:Sym_P (head_L R))(t:0 ≤ h): IncX Utrue (writ_E R) P h (cone_D P.order P.power*a):=by
 refine spin_m P _ ?_ (spin_E R); have hx:head_L R+cry_H R=R:= funext fun i=>funext fun j=>sub_add_cancel ..
 nth_rw 1 [←hx]; rw [writ_k,sure_c _ v, cone_D,add_mul,one_mul]; refine add_v P _ _ (?_:IncX (fun _=>False) (head_L R) P h a) ?_ -- tune
 · exact share_V P R p
 let K:= shine_M P.order P.power*a; let Z:= cry_H R
 have hu:= ton_W P (F:=fun s:T0=>base_Q s Z) (g:=fun _=>K) (fun i=> thrive_X P i p t) univ
 have hp:= thin_P P _ (plight_C n) hu; rw [abs_of_pos (envy n),sum_const,card_univ,nsmul_eq_mul,feed] at hp; exact hp -- tune
end YM.CF.Ione
