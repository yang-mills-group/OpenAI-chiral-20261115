import YM.CF.Oath.Eva
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
local notation "V'"=> Support (Domain N B)
local notation "PX" b:max a:max=> (twigExt (b,a))
local notation "β"=> bring t' Tg
local notation "Xm"=> cala G S g_ t t' W Y Tg kR
abbrev pinZ (R₀:Support (Domain P B)):= pairZ G t t' Y Tg (twigExt (true,p)) (twigExt (false,q)) R₀
abbrev barO (c':Bool)(i: Single (mid P B))(a:Single (mid N B))(X:Support (Domain P B)):= cSignX c' (openQ G (bring t' Tg) W X c' i a)
abbrev legM (b':Bool)(p:Single (mid P B))(X:Support (Domain P B)): FC CM:= ∑ i:Single (mid N B),barO Tg W t' b' p i X • put (b',i)
abbrev frostM (R₀:Ride S)(Q:ℂ):Track (Ride S) (FC CM):=∑ X:Support (Domain P B), Pi.single (R₀⊔mark_l S kR X) ((Q*pinZ p q Tg Y t' X) • 1)
abbrev primeY (X Y:Support (Domain P B))(R₀:Eire.Ride S):Eire.Ride S:=R₀⊔mark_l S kR X ⊔ mark_l S kR Y
abbrev lockP(X F:Support (Domain P B))(R₀:Eire.Ride S)(Q:ℂ):Track (Ride S) (FC CM):= Pi.single (R₀⊔mark_l S kR X ⊔ mark_l S kR F) (Q • (legM Tg W t' true p X*legM Tg W t' false q F))
abbrev pileP(Q:ℂ)(K:Eire.Ride S):= ∑ X:Support (Domain P B),∑ Y:Support (Domain P B),lockP p q Tg W t' kR X Y K Q
variable (Q:ℂ)
include g_
lemma carryF (a':Bool)(u: Ride S)(p: Single (mid P B)) : Stilo.lank (Xm u).seats (twigExt (a',p))=∑ X∈gleans S kR u,legM Tg W t' a' p X:=by
 unfold Stilo.lank; simp_rw [miles,Finset.sum_smul]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [Fintype.sum_prod_type,sum_eq_single a']; apply sum_congr rfl; intro j _
 change (if a'=a' then cSignX a' _ else 0) • _=_; rw [if_pos rfl]; rfl -- tune
 intro a _ v; apply sum_eq_zero; intro j _; unfold gash Urn.mount; change (if a=a' then cSignX a' _ else 0) • _ = _; rw [if_neg v,zero_smul]
 simp
omit g_
lemma coldZ : due_z G (twigExt (true,p)) (twigExt (false,q))=0:=by
 unfold due_z Urn.soar; dsimp only; let L₀:Levier.Grave:=(true,true,true,false); change (if true=false then 0 else cSignX true _) = _; rw [if_neg (by decide)]; change star (feeX G L₀ _ _) = 0; unfold feeX; simp [L₀] -- tune names
include g_
set_option maxHeartbeats 650000 in
lemma kicks (K₄:Eire.Ride S): ranks [(true,p),(false,q)] K₄ Q (cala G S g_ t t' W Y Tg kR) = frostM p q Tg Y t' kR K₄ Q + pileP p q Tg W t' kR Q K₄ :=by
 let T:=PX true p; let V:=PX false q; let X:=Xm
 apply Scion.solve; intro a
 have h: Stilo.view a (frostM p q Tg Y t' kR K₄ Q)= if K₄≤a then (∑ i∈ gleans S kR a,(Q*pinZ p q Tg Y t' i) • 1) else 0:=by
    change (vAdd a) _=_; unfold frostM; rw [map_sum]; simp_rw [show ∀ h:Track (Ride S) (FC CM), vAdd a h=view a h from fun _=> rfl,singleV,sup_le_iff]; unfold gleans; rw [sum_filter]; split_ifs with p; exact sum_congr rfl fun i _=>by simp only [p,true_and,mark_l]
    apply sum_eq_zero; simp [p] -- tune
 let Z(a':Bool)(p':Single (mid P B))(S:Support (Domain P B)):= legM Tg W t' a' p' S
 have hu:Stilo.view a (pileP p q Tg W t' kR Q K₄) = if K₄≤a then ∑ i∈ gleans S kR a,∑ j∈gleans S kR a,Q •(Z true p i * Z false q j) else 0:=by
    change (vAdd a) _=_; unfold pileP; simp_rw [map_sum,show ∀ h:Track (Ride S) (FC CM), vAdd a h=view a h from fun _=> rfl,lockP,singleV,sup_le_iff]; split_ifs with p0; swap; · simp [p0]
    unfold gleans mark_l; simp only [p0,true_and]; rw [sum_filter]; apply sum_congr rfl; intro i _; split_ifs with t; · simp_rw [t,true_and]; rw [sum_filter]; -- tune defeq
    simp [t]
 rw [view_add,h,hu]; split_ifs; swap; · rw [add_zero]
 rw [map_smul,LinearMap.smul_apply]; let R:= X a; have hx : issue R (rollC put [(true,p),(false,q)]) 1=lank R.seats T*lank R.seats V +Stilo.price R.pals CM T V:= by
    rw [show (1:FC (Single (mid P B)))=rollC Hake.bell [] from (by unfold rollC; simp), Scion.ring_u]; unfold Scion.cue; change taskC _ _ [T,V]=_; simp only [task_one,task_zero,picks,List.map_cons, List.map_nil,List.sum_cons,List.sum_nil,ite_false,Bool.false_eq_true,add_zero,mul_one]
 rw [show issue _ _ _= _ from hx,smul_add]; change Q • (lank _ _*lank _ _) + _ = _; rw [carryF Tg W Y g_ t' kR true a p,carryF Tg W Y g_ t' kR false a q]; unfold Stilo.price; rw [show R.pals T V=_ from (cryZ G S g_ _ _ W Y kR _ _ Tg a),coldZ p q,add_zero]; -- tune
 rw [add_comm,sum_mul_sum]; simp_rw [Finset.smul_sum]; simp_rw [Finset.sum_smul]; simp_rw [Finset.smul_sum,smul_smul]; rfl
end YM.CF.Oath
