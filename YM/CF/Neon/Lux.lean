import YM.CF.Neon.Ten
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S_O:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S_O}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u_O Hh pKe qK a γ vS dS kL w:ℝ}{r p_aux i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
open Taxi Hope Mew
local notation "Θ"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
-- Total motion receipt ONE SOURCE. c offsets only constrained at singleton.Fo.Press.Priority. covariance later. mask pay separately.
variable (o:Site (mid N B)) (p0:BudgetPoint) (h ν :ℝ)
local notation "Tκ"=> Cube.node o
local notation "Cκ"=> (Φrap Θ o 10)
variable (L0:ℕ)(Vκ:ℝ)(Ψ: DayT p0.order Vκ)(uK:0 ≤ Vκ)
variable {I:Type}[Fintype I][LinearOrder I]
local notation "ΦΞ"=> Key I
variable (σ:I→ Site (mid N B))(Q':I→ Cusp (mid N B))(W:I→ℝ)(Kχ:I→ ℂ) -- fix
local notation "ω"=> Aura Θ
variable (F:Mew.Key I→ Pax (mid N B))(F':I→ RegBudget (mid N B))(Z Φ:I→ℝ)(E:I→ArcΦ)(Ux:∀ i,Ice L0 (σ i) p0 h (Z i) (W i) (Φ i) (coldE p0 (τι F [i])) (F' i) (Q' i) (Kχ i) (E i))
local notation "Dμ"=> Φstack Q'
local notation "Φt" z:max=> Aura_T F z
variable (Tp:Ids (mid N B))
local notation "Φr" z:max=> Ione.cast_E (Aura_T F z) Tp
local notation "IZ"=> FacetE F F' Tp
local notation "Tσ"=> α_ξ Kχ
open Rive
variable (w0:∀ z∈hill I,Turf (F z))(uF:∀ i x,River fun z=> F z i x) (p:∀ i:Aura (mid N B),Hush (Cube.node ∘ σ) i.val fun z=> F z i)
-- aperture and chart.Meta. dual extraction per root. up Field covariance later.
variable {Λe:Type*}[NormedAddCommGroup Λe][NormedSpace ℂ Λe][CompleteSpace Λe]
variable (x:Scree.Hub (mid N B))(v:Pane (mid N B))(q:Aura (mid N B))(A0:Orbit (mid N B))
abbrev Rep_C (f:I→ Λe)(z:Key I):Λe:=∑ i:I,z i • f i
lemma rer_C(f:I→Λe):River (Rep_C f) :=by apply (tip_bank (univ : Finset I) (fun i z=> z i • f i) _).1; exact fun i _=> by simpa only [Mew.pine,Finset.prod_singleton] using (Mew.lift_b ({i}:Finset I) (f i))
lemma αtip (f:I→Λe)(l:List I)(p:l.Nodup): tipI (Rep_C f) l= ∑ i:I,if l.toFinset={i} then f i else 0 :=by
 let F' (i:I) z:= Mew.pine {i} z • f i
 rw [show Rep_C f = fun z=>∑ i:I,F' i z from (by unfold Rep_C; simp only [F',Mew.pine,Finset.prod_singleton]), (tip_bank _ F' (fun i _=>lift_b _ _)).2]; simp_rw [F',tip_tape _ p]
lemma sTip (f:I→Λe)(i:I):tipI (Rep_C f) [i]= f i:=by rw [αtip _ _ (by simp)]; simp
lemma far_P (f:I→Λe)(l:List I)(p:l.Nodup)(s:2≤ l.length):tipI (Rep_C f) l=0:=by
 rw [αtip _ _ p]; apply sum_eq_zero; intro i _; rw [if_neg]; intro t; have he:= congrArg Finset.card t; rw [List.toFinset_card_of_nodup p, card_singleton] at he; omega -- tune
include uF
lemma hus_k : River (fun z:Key I=> (Aura_T F z) q A0):=by
 unfold Aura_T; simp_rw [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply]; exact river_minus _ _ (uF _ _) (rer_C _)
lemma growth_P : River (fun z:Key I=> FacetE F F' Tp z x v):=by
 unfold FacetE EraT Ione.cast_E; simp_rw [Pi.add_apply,Finset.sum_apply, Pi.smul_apply]; exact dub_V (rer_C _) (bScale _ (hus_k _ uF _ _) _)
local notation "P_"=> (Ione.cast_E)
lemma pulse_I (l:List I)(p:l.Nodup)(s:2 ≤ l.length) : tipI (fun z:Key I=> FacetE F F' Tp z x v) l= tipI (fun z:Key I=> Ione.cast_E (F z) Tp x v) l:=by
 let U:= F; let Q:=lagE x; let K(i):= F' i x v; let E(z):=F z Q (v,Tp); let J(i:I):=τι F [i] Q (v,Tp); let G(z):=Rep_C J z; let c:ℂ:= bassH Q
 have ht:E=(fun z=>E z):= rfl; have hw(z:Key I): IZ z x v=Rep_C K z+ c • (E z-G z):=by unfold FacetE Ione.cast_E EraT G Rep_C Aura_T; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,Pi.sub_apply,smul_sub]; simp only [Finset.sum_apply,Pi.smul_apply]; rfl -- scope c comm
 have hs(z): P_ (F z) Tp x v=c • E z:=rfl; let T:= uF Q (v,Tp); let HH:=river_minus _ _ T (rer_C J); simp_rw [hw,hs]; rw [tip_A (rer_C K) (HH.scale _),far_P _ _ p s,zero_add,tip_C HH,tip_C T,tip_M T (rer_C J), far_P _ _ p s,sub_zero]
lemma pulse_Z (i:I): tipI (fun z:Key I=> FacetE F F' Tp z x v) [i] = F' i x v:=by
 let U:= F; let Q:=lagE x; let K(i):= F' i x v; let E(z):=F z Q (v,Tp); let J(i:I):=τι F [i] Q (v,Tp); let G(z):=Rep_C J z; let c:ℂ:= bassH Q
 have hw(z:Key I): IZ z x v=Rep_C K z+ c • (E z-G z):=by unfold FacetE Ione.cast_E EraT G Rep_C Aura_T; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,Pi.sub_apply,smul_sub]; simp only [Finset.sum_apply,Pi.smul_apply]; rfl
 simp_rw [hw]; let T:= uF Q (v,Tp); let HH:=river_minus _ _ T (rer_C J); rw [tip_A (rer_C K) (HH.scale _), tip_C HH, tip_M T (rer_C J),show tipI (fun z=>Rep_C K z) [i]=_ from sTip _ i,show tipI (fun z=>G z) [i]=_ from sTip J i,show J i= tipI E [i] from rfl,sub_self,smul_zero,add_zero]
lemma punk (f:F 0=0): FacetE F F' Tp 0=0:=by unfold FacetE EraT Ione.cast_E Aura_T; simp [f]; funext i j; change bassH (lagE i) • (0:Cipher Θ)=0; exact smul_zero _
end YM.CF.Neon
