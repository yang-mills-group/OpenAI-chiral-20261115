import YM.CF.Pso.Tide
import YM.CF.Reed.Solo
import YM.CF.BProof.Counter.Turn
import YM.CF.Beau.Merc
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
-- unabbreviated budgets. Ξ subtraction lemma for applying price theorem.
open Iva Lilt
variable {F G:RegBudget n} {u v:ℝ} (hF:IncX Utrue F P h u) (hG:IncX Utrue G P h v)(x0:Scree.Hub n)
private lemma sub_of_plus{A B:Type*}[AddCommGroup A][AddCommGroup B](f:A→B)(h:∀ x y,f (x+y)=f x+f y)(x y):f (x-y)=f x-f y := eq_sub_of_add_eq (by rw [←h, sub_add_cancel]) -- tune
private lemma sad(F G:RegBudget n): cry_H (F-G)=cry_H F-cry_H G:= sub_of_plus (@cry_H n) (fun _ _=> funext fun _=> funext fun _=>plus_Y ..) F G
private lemma sadL(F G:RegBudget n): head_L (F-G)=head_L F-head_L G:=by have hp(A:RegBudget n): head_L A=A-cry_H A:=rfl; rw [hp,hp,hp,sad]; abel
private lemma map_S : caw P k' (cry_H (F-G))=(caw P k' (cry_H F))-(caw P k' (cry_H G)):=by rw [sad]; funext x; by_cases h:chute P k' x<;> simp [h,caw]
private lemma map_c : can_V P k' (cry_H (F-G))=can_V P k' (cry_H F)-can_V P k' (cry_H G):=by rw [sad]; funext x; by_cases h:chute P k' x<;> simp [h,can_V]
private lemma pot_sub (V:Pane n)(F G: InkD n): lifeH (F-G) V=lifeH F V-lifeH G V:= map_sub (pot (n:=n) ∅) _ _
private lemma real_S(F G:RegBudget n): realH (F-G)=realH F-realH G:=funext fun i=>funext fun V=>by change Complex.reCLM (lifeH (F i-G i) V)=_; rw [pot_sub,map_sub]; rfl
private lemma porch_sub(F G:RegBudget n)(x:Scree.Hub n): porch (F-G) x= porch F x-porch G x:=by
 funext V; unfold Taxi.porch; rw [Pi.sub_apply, pot_sub, sub_of_plus (@Pastry.hollow (Dwell n) _ _) (fun x y=>Iva.horn_s ..)]; rfl -- Pi.sub notation.
variable(h1:1 ≤ h)
include hF h1
private lemma law (k':ℕ) : (pintK P).Regular x0.val.2 (realH (caw P k' (cry_H F)) x0) := by
 let M:= ‖Complex.reCLM‖; obtain ⟨X,p,v⟩:= (Beau.price_Q P F hF).2.weight; unfold realH caw; split; exact (Taxi.cashR (X0:=x0) (cry_H F x0) (p x0) (zero_le_one.trans h1) _ M le_rfl).regular; exact reg_const (0:ℝ)
omit hF h1
private lemma moults{X:Scree.Hub n}{f g: Pane n→ℝ}(p:P.Regular X.val.2 f)(u:P.Regular X.val.2 g): fluxP X (f-g)=fluxP X f-fluxP X g:=by funext a b; unfold fluxP; simp only [Pi.sub_apply]; split; exact hessian_sub p u _ _; rw [sub_self]
include h1 hF hG
lemma aora_diff(k':ℕ): aora P k' (F-G)= aora P k' F-aora P k' G:=by
 unfold aora lureC payoutF; rw [map_S,real_S,←sum_sub_distrib]; exact sum_congr rfl fun i _=>by  rw [Pi.sub_apply,moults (law hF i h1 k') (law hG i h1 k'),Pi.sub_apply (f:=fluxP i _), Pi.sub_apply,mul_sub]
private lemma heat_S (k':ℕ)(o:Skye.Seat n): fuelC x0 (realH ((caw P k' (cry_H F))-(caw P k' (cry_H G))) x0) o=fuelC x0 (realH ((caw P k' (cry_H F))) x0) o-fuelC x0 (realH ((caw P k' (cry_H G))) x0) o:=by
 unfold fuelC; rw [real_S, Pi.sub_apply (f:=realH _), moults (law hF x0 h1 k') (law hG x0 h1 k'),←counter_sub,smul_sub]
private lemma bank_c(k':ℕ): bankT ((caw P k' (cry_H F))-(caw P k' (cry_H G))) x0=bankT ((caw P k' (cry_H F))) x0-bankT ((caw P k' (cry_H G))) x0:=by
 funext x; unfold bankT payout; simp_rw [heat_S hF hG _ h1 k',sum_sub_distrib]; rw [Pi.sub_apply (f:=∑ _, _),Complex.ofReal_sub, sub_of_plus (@Pastry.hollow (Dwell n) _ _) (fun x y=> Iva.horn_s ..)]; rfl
private lemma Coil_sub(k':ℕ): Beau.Coil ((caw P k' (cry_H F))-(caw P k' (cry_H G)))=Beau.Coil ((caw P k' (cry_H F)))-Beau.Coil ((caw P k' (cry_H G))):=by
 funext x; unfold Beau.Coil sunY; simp_rw [mowR,Pi.sub_apply,bank_c hF hG _ h1 k',porch_sub]; rw [←sum_sub_distrib]; apply sum_congr rfl; intro i _; abel
-- rare path not tested in linearity: use path-linear charges even before aperture
lemma brol_diff(k':ℕ)(R: PathData SU.group)(q:Clip): brol P R q k' (F-G)=brol P R q k' F-brol P R q k' G:=by
 have hp(x:ℝ): lite_b n P R q x=x • lite_b n P R q 1:=funext fun i=> funext fun y=>(bothC P R q x i y).1
 have hv(x:ℝ): lit_P n P R q x=x • lit_P n P R q 1:=funext fun i=> funext fun y=>(bothC P R q x i y).2
 let r:=aora P k' F; let s:=aora P k' G; dsimp only [brol]; rw [map_c,map_S,aora_diff hF hG h1,Coil_sub hF hG h1,sadL,hp (aora P k' F),hp (aora P k' G),hv (aora P k' F),hv (aora P k' G),hp (r-s),hv (r-s),sub_smul,sub_smul]
 rw [show (Coil ((caw P k' (cry_H F)))-Coil ((caw P k' (cry_H G)))+(r • lite_b n P R q 1-s • lite_b n P R q 1))+(r • lit_P n P R q 1-s • lit_P n P R q 1)=(Coil ((caw P k' (cry_H F)))+r • lite_b n P R q 1+r • lit_P n P R q 1)-(Coil ((caw P k' (cry_H G)))+s • lite_b n P R q 1+s • lit_P n P R q 1) from by abel, sub_of_plus (@writ_E n) (fun a b=>writ_k ..)]; unfold r s; abel
private lemma peel_c(k':ℕ):peelR ((caw P k' (cry_H F))-(caw P k' (cry_H G))) x0 D=peelR ((caw P k' (cry_H F))) x0 D-peelR ((caw P k' (cry_H G))) x0 D:=by
 have hv:oV (porch ((caw P k' (cry_H F)) - (caw P k' (cry_H G))) x0)= oV (porch ((caw P k' (cry_H F))) x0)-oV (porch ((caw P k' (cry_H G))) x0):=by rw [porch_sub]; rfl
 have he :∀ j:Site (More n), Taxi.say_t ((caw P k' (cry_H F))-(caw P k' (cry_H G))) x0 D j=Taxi.say_t ((caw P k' (cry_H F))) x0 D j-Taxi.say_t ((caw P k' (cry_H G))) x0 D j:=by
    intro j; unfold Taxi.say_t; split; rw [sub_self]
    funext x; unfold oV Taxi.page; rw [heat_S hF hG x0 h1 k' j, Pi.sub_apply,map_sub]; rfl
 unfold peelR Vow.flick; simp_rw [hv,he,sum_sub_distrib]; split
 · rw [show oV (((caw P k' (cry_H F))-(caw P k' (cry_H G))) x0)=oV (((caw P k' (cry_H F))) x0)-oV (((caw P k' (cry_H G))) x0) from rfl]; abel
 abel
lemma truce_diff(k':ℕ)(R:PathData SU.group)(q:Clip)(T: Ids n): truce P R q k' (F-G) T=truce P R q k' F T-truce P R q k' G T:=by
 have h(x:ℝ): ΘK T P R q x=x • ΘK T P R q 1:=funext fun i=>funext fun D=>funext fun V=>pique_z P R T q x i V D
 have hv:voids ((caw P k' (cry_H F))-(caw P k' (cry_H G)))=voids ((caw P k' (cry_H F)))-voids ((caw P k' (cry_H G))):=by
    unfold voids; rw [←sum_sub_distrib]; refine sum_congr rfl fun i _=>?_ ; unfold pamE chasmR; funext j D; by_cases g:j=pur (stateT i); · subst j; simp only [Pi.sub_apply,Pi.single_eq_same]; exact peel_c hF hG i h1 k' -- tune _ application
    rw [Pi.single_eq_of_ne g,Pi.sub_apply (f:=Pi.single _ _),Pi.single_eq_of_ne g, Pi.single_eq_of_ne g]; rw [Pi.sub_apply]; simp
 unfold truce; let r:=aora P k' F; let s:=aora P k' G; rw [aora_diff hF hG h1,map_S,hv,h r,h s,h (r-s),sub_smul]
 rw [show voids ((caw P k' (cry_H F)))-voids ((caw P k' (cry_H G)))-(r • ΘK T P R q 1-s • ΘK T P R q 1)=voids ((caw P k' (cry_H F)))-r • ΘK T P R q 1-(voids ((caw P k' (cry_H G)))-s • ΘK T P R q 1) from by abel, sub_of_plus (@writ_K n) (fun a b=>writ_plus ..)]
end YM.CF.Beau.PushA
