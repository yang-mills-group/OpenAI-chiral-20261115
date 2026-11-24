import YM.CF.Tale.Halo
import YM.CF.Beau.Ray
import YM.CF.Hope.Log
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Taxi
open Vow
local notation "G₅"=> SU.group
abbrev Skate:= PlaqAxes→ PlaqAxes→ℂ
def tooth (o: Site (More n))(P:BudgetPoint)(Q: InkD n):Skate:= fun i j=> iteratedFDeriv ℝ 2 ((lifeH Q) ∘ increment 1) 0 ![Tale.clipT P o i,Tale.clipT P o j]
abbrev kerP (o: Site (More n))(P:BudgetPoint)(Q:Skate): Pane n→ℂ:= fun V=> ↑(counter (G:=SU.group) (fun i j=> (Q i j).re/P.threshold^2) o V)+ (↑(counter (G:=SU.group) (fun i j=> (Q i j).im/P.threshold^2) o V):ℂ)*Complex.I
def plateZ(o:Skye.Seat n)(P:BudgetPoint)(Q:Skate): InkD n:= fun U=> Pastry.hollow (kerP o P Q U)
def Verc (Q:Skate):Prop:=∀ x y,Q x y= Q y x
open Ione
local notation "QZ"=> ((More n))
variable (P) (Q:InkD n)(Xo:Scree.Hub n)
local notation "o"=> Xo.val.1
local notation "X"=> Xo.val.2
local notation "θ"=> P.threshold
local notation "tX"=> tooth o P
variable (w:PressB P Xo Q h c)(he:0≤h)
include w he
lemma cym (L:ℂ→L[ℝ]ℝ)(A B:PlaqAxes): L (tooth o P Q A B)= AnalyticBridge.VerifiedReset.coeff (L ∘ lifeH Q) o A B * θ^2 :=by
 let V:= Tale.clipT P o; let f:= lifeH Q ∘ increment 1; let G:=L ∘ f
 have hv:L (tooth o P Q A B) = logHessian (L ∘ lifeH Q) (V A) (V B):=by
    change _= iteratedFDeriv ℝ 2 (L ∘ (lifeH Q ∘ increment 1)) 0 _; rw [L.iteratedFDeriv_comp_left ((eraF _ _ w he _ (ping_f P X)).paid) (i:=2) (Nat.cast_le.mpr ((by decide:2 ≤ 6).trans P.order_ge))]; rfl
 have e:= cashR Q Xo w he L ‖L‖ le_rfl; rw [hv, show logHessian _ (V A) (V B)= _ from label_color o Thera.yet_one e.regular A B (θ • spike G₅) (θ • spike G₅), real_inner_self_eq_norm_sq,norm_smul,spike_norm Thera.yet_one,mul_one, Real.norm_of_nonneg P.threshold_pos.le]
lemma ploy : Verc (tX Q):=by
 intro a b; have hv(L:ℂ→L[ℝ]ℝ):L (tX Q a b)= L (tX Q b a):=by rw [cym P Q Xo w he,cym P Q Xo w he]; exact congrArg (fun v=>v*θ^2) (hessian_symm (cashR Q Xo w he L _ le_rfl).regular ((AnalyticBridge.VerifiedReset.wedge a (spike G₅)).field _) ((AnalyticBridge.VerifiedReset.wedge b (spike G₅)).field _))
 exact Complex.ext (hv Complex.reCLM) (hv Complex.imCLM)
lemma dia(A B:PlaqAxes): ‖tooth o P Q A B‖≤c:=by
 have hZ(i:Fin 2): P.dirBound o ((![Tale.clipT P o A,Tale.clipT P o B]:Fin 2→ tangD n) i):=by fin_cases i; exact Tale.fore_l P _ A; exact Tale.fore_l P _ B
 exact (eraF _ _ w he _ (ping_f P X)).token 2 ((by decide: 2 ≤6).trans P.order_ge) _ hZ
lemma pith (p:4 ≤ (More n).val)(u:Nonwrapping X o) (x: lifeH Q 1=0)(g:tX Q=0) : Beau.spark o Q:=by
 refine ⟨x,fun i j z v=>?_⟩
 let b:tangD n→ℂ:= (lifeH Q ∘ increment 1); let K:= iteratedFDeriv ℝ 2 b 0 ![i,j]
 have hv(L:ℂ→L[ℝ]ℝ): L K= 0:=by
    let f:= L ∘ lifeH Q; have hM:= (cashR Q Xo w he L _ le_rfl).regular; have hx:(AnalyticBridge.VerifiedReset.coeff f o)=0:=by
       ext a b; apply mul_right_cancel₀ (pow_ne_zero 2 P.threshold_pos.ne'); change AnalyticBridge.VerifiedReset.coeff _ o _ _ * θ^2=0*θ^2; rw [←cym P Q Xo w he L a b,g,zero_mul]; exact map_zero L
    have hr: L K=logHessian f i j:=by
       have he:= L.iteratedFDeriv_comp_left ((eraF _ _ w he _ (ping_f P X)).paid) (i:=2) (Nat.cast_le.mpr ((by decide:2 ≤ 6).trans P.order_ge)); change _=iteratedFDeriv ℝ 2 (L ∘ (lifeH Q ∘ increment 1)) 0 _; rw [he]; rfl
    rw [hr]; apply affine_zero hM o _ i j z v
    intro l; rw [LinearJet.hessian_curl Thera.yet_one hM u p (positive_primitive l.positive).symm (positive_primitive l.positive).symm,flux_formula o Thera.yet_one hM,hx]; simp
 change K=0; exact Complex.ext (hv Complex.reCLM) (hv Complex.imCLM)
omit w he
variable (Y': Site (More n))(F:PlaqAxes→PlaqAxes→ℝ)
include P
lemma yew(A B:PlaqAxes)(u:20<(More n).val): AnalyticBridge.VerifiedReset.coeff (counter F Y' (G:=SU.group)) Y' A B= (F A B+F B A)/2:=by
 let E:=counter F Y' (G:=SU.group); let b(i:PlaqAxes):LinearJet G₅:= AnalyticBridge.VerifiedReset.wedge i (spike G₅); let p:Flux G₅ :=(b A).positive; let q:Flux G₅ :=(b B).positive
 let M:=(b A)-(b B); have ht:M.positive=p-q:=LinearJet.positive_sub ..; have hh:M.field Y'=(b A).field Y'-(b B).field Y':= LinearJet.field_sub ..
 have hw:= counter_diag Thera.yet_one P Y' u M F; let J(x y:Flux G₅):=AnalyticBridge.VerifiedReset.quad F x y; change logHessian E _ _= J _ _ at hw
 have ha(i j:PlaqAxes) : J (b i).positive (b j).positive=F i j:=by unfold J AnalyticBridge.VerifiedReset.quad b; simp [curl_wedge,apply_ite]; rw [sum_eq_single i]; simp [spike_norm Thera.yet_one]; intro k _ t; simp [t.symm]; simp
 have hJ:J (p-q) (p-q)=J p p-J p q-(J q p-J q q):=by unfold J AnalyticBridge.VerifiedReset.quad; simp_rw [Pi.sub_apply,inner_sub_left,inner_sub_right,mul_sub,sum_sub_distrib]
 rw [hh,ht,hJ] at hw; rw [hessian_eq] at hw; simp only [map_sub,_root_.sub_apply] at hw; simp_rw [←hessian_eq] at hw; rw [hessian_symm (show P.Regular (halo 2 {Y'}) E from counter_regular ..) ((b B).field Y') ((b A).field Y'), show logHessian E ((b A).field Y') ((b A).field Y')=J p p from counter_diag Thera.yet_one P _ u _ _,show logHessian E ((b B).field Y') ((b B).field Y')= J q q from counter_diag Thera.yet_one P _ u _ _,show J p q = _ from ha A B, show J q p = _ from ha B A] at hw
 change logHessian E ((b A).field Y') ((b B).field Y')= _; linarith only [hw]
end YM.CF.Moto
