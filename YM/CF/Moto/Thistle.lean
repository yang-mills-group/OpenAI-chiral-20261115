import YM.CF.Moto.Thorn
import YM.CF.Moto.Jazz
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione Beau
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Hope Taxi
local notation "Rp"=> Rink -- tune junk
variable {X₀:Scree.Hub n}{F G:InkD n}
local notation "X"=> X₀.val.2
local notation "o"=> X₀.val.1
local notation "Ew"=> (increment (1:Pane n))
local notation "θ"=> P.threshold
local notation "Hq"=> Haro.orbitPH
variable(q:PressB P X₀ F h a)(u:PressB P X₀ G h b)(v:0 ≤ h)
local notation "Ω"=> NormedSpace.exp
local notation "PZ"=> Pastry.pane
local notation "gϵ" f:max=> lifeH f ∘ increment (1:Pane n)
local notation "gη" a:max=> tooth o P a
open Hove
local notation "Y₀"=> (fun i:Pane n=> exp (G i))
abbrev foot_(Q:InkD n):InkD n:=fun i=> exp (Q i)
local notation "O"=> F * foot_ G
abbrev ωX(z:InkD n):= Complex.exp (Taxi.lifeH z 1)
local notation "T"=> ωX G
include q u v
lemma stake_s0 (e:lifeH F 1=0):lifeH O 1=0∧ gη O = T • gη F ∧ Hq (O 1)= T • Hq (F 1) :=by
 let f:= lifeH O ∘ increment 1; let g:= lifeH F ∘ increment 1; let h:= Complex.exp ∘ (lifeH G ∘ increment 1); have hp:= (show f=g*h from funext fun i=> (show Pastry.pane _= _ from (mast_mul _ _).trans (congrArg (Pastry.pane (F _)*·) (paneExp (G (Ew i)))))); have hv:PZ (G 1)=lifeH G 1:=rfl
 have ht:g 0=0:=by unfold g; rw [Function.comp_apply, AnalyticBridge.VerifiedReset.at_zero,e]
 have hT:h 0= T:=by unfold h; rw [Function.comp_apply, Function.comp_apply,AnalyticBridge.VerifiedReset.at_zero]
 refine ⟨?_,funext fun i=>funext fun j=>?_,?_⟩
 · rw [←AnalyticBridge.VerifiedReset.at_zero (1:Pane n),show lifeH _ _= f 0 from rfl,hp]; simp only [Pi.mul_apply,ht,zero_mul]
 · change iteratedFDeriv ℝ 2 f 0 _= T * _; rw [hp]; exact (lyfe _ _ (by simpa only [Nat.cast_ofNat] using heatP q v) (Complex.contDiff_exp.contDiffAt.comp _ (by simpa only [Nat.cast_ofNat] using heatP u v)) (hutC q v) ht).trans (congrArg (· * _) hT)
 rw [Pi.mul_apply, pay_U _ _ e]; unfold foot_; rw [paneExp,hv]
include q u v
lemma hut_p : gη (F-G)=gη F-gη G:=by
 have ht: lifeH (F-G) ∘ increment 1= lifeH F ∘ increment 1-lifeH G ∘ increment 1:= funext fun i=>show Pastry.pane (F (Ew i)-G (Ew i))=_ from map_sub (panHom _) (F (Ew i)) (G (Ew i)) -- assoc parse parentheses
 funext i j; unfold tooth; change iteratedFDeriv ℝ 2 _ _ _= (tooth o P F) i j-(tooth o P G) i j; rw [ht,iteratedFDeriv_sub_apply (heatP q v) (heatP u v)]; rfl
omit q u v
variable (L:Skate)(Z:InkD n){xP:ℝ}
lemma tail_K(K L:Cipher n) : Haro.orbitPH (K-L)= Haro.orbitPH K-Haro.orbitPH L:=by ext i j; simp_rw [Haro.orbitPH,Matrix.of_apply,Prism.port_eq]; simp only [Bool.false_eq_true,Prod.mk.injEq,Bool.true_eq_false,false_and,if_false]; let T1:=Haro.tray i j; let z:= parity (true,i) {(false,j)}; change z*(crumb K.val T1-crumb L.val T1)=_; rw [mul_sub]; simp [Matrix.sub_apply,Prism.port_eq]; rfl
lemma hol_l(U:ℂ): Hq (Pastry.hollow (n:=LeanV (Single n)) U)=0:=by ext i j; simp_rw [Haro.orbitPH,Matrix.of_apply,Prism.port_eq]; split; rfl; change _ * (U • (1:FC (LeanV (Single n)))) _ _=0; simp
local notation "D"=> plateZ o P L
lemma heat_s(p:∀ U:Pane n,Z U= plateZ o P L U): Haro.orbitPH (Z 1)=0:=by rw [p]; exact hol_l _
local notation "Sρ"=> (↑N+1:ℝ)
local notation "ξ"=> (P.order.factorial:ℝ)
include q u v
abbrev hrζ (P:BudgetPoint)(a b:ℝ):= a + (P.order.factorial:ℝ)*(((P.order+1:ℝ)*a)*((P.order+1:ℝ)*((P.order.factorial:ℝ)*(Real.exp ((P.order+1:ℝ)*b)*((P.order+1:ℝ)*b))))) -- hygiene P?
lemma virtue_w : PressB P X₀ O h (hrζ P a b):=by
 have he:= peer_P q (ε_P u v) v; let g:InkD n:= fun i=>exp (G i)-1; rw [show O=F+F*g from ?_]; exact Larch.prop_add _ _ q he
 funext i; change F i*exp (G i)= F i +F i*(exp (G i)-1); ring
structure Clad(P:BudgetPoint)(Z0:Scree.Hub n)(F G:InkD n)(h c:ℝ): Prop where
 paid: PressB P Z0 F h c
 loaded(U:Pane n):pingS P.threshold Z0.val.2 U→ exp (F U)-1= G U
 mute(l: Taxi.lifeH G 1=0):Taxi.lifeH F 1=0 ∧ tooth Z0.val.1 P F=tooth Z0.val.1 P G∧ Haro.orbitPH (F 1)= Haro.orbitPH (G 1)
abbrev rotζ (P:BudgetPoint)(a:ℝ):=2*(P.order.factorial:ℝ)*((↑P.order+1:ℝ)*a)
omit u v
include q
lemma herve (he:1≤h)(s:Sρ*a≤1/4)(z:rotζ P a≤1) : Clad P X₀ (linen P X₀ F) F h (rotζ P a):=by
 obtain ⟨u,v⟩:=coy_P q he s; exact ⟨u,v,true_K u (zero_le_one.trans he) he z v⟩
omit q
end YM.CF.Moto
