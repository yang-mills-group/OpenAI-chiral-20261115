import YM.CF.Wray.Pose
import YM.CF.Pig.Foil
import YM.CF.Iva.Plink
import YM.CF.Wray.Shop
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
open Iva Eire Font
local notation "Z_"=> Domain N B
local notation "c'"=> Single N
local notation "Φ"=> Branch.ledgerV
-- COLOR set occupancy(real). No unproven host exceptions
local notation "P"=> Raid (LeanV (Single N))
structure SupportP {n:Type*}[Fintype n][LinearOrder n](X:Raid n)(H A:ℝ) :Prop where
 yes: 0 ≤ X
 gold: joinV (stake H) X ≤ A
namespace SupportP
variable {o:Type}[LinearOrder o][Fintype o]
variable (k l:ℕ){a b c H:ℝ}{X Y:Raid o}
lemma pos_v(v:SupportP X H a)(h:0≤H): 0 ≤ a:=(show 0≤ joinV (stake H) X from sum_nonneg (fun i _=>mul_nonneg ((stokes h).fee i) (v.yes i))).trans v.gold
lemma more(v:SupportP X H a)(h:a ≤ b): SupportP X H b:=⟨v.yes,v.gold.trans h⟩
lemma sab(v:SupportP X H a)(h: 0≤H):SupportP (Rue.saber X l) H (Real.exp a * a^l):=by
 have he:=v.gold; have hp:0 ≤ joinV (stake H) X:=sum_nonneg fun i _=>mul_nonneg ((stokes h).fee i) (v.yes _)
 exact ⟨(Rue.saber_r _ v.yes _ (stokes h)).1, (Rue.peony _ v.yes (stokes h)).trans (mul_le_mul (Real.exp_monotone he) (pow_le_pow_left₀ hp he _) (pow_nonneg hp l) (Real.exp_pos _).le)⟩
lemma sadd(v:SupportP X H a)(w:SupportP Y H b):SupportP (X+Y) H (a+b):=⟨fun i=>add_nonneg (v.yes _) (w.yes _),by rw [joinVadd]; exact add_le_add v.gold w.gold⟩
lemma skirtS(v:SupportP X H a)(p:SupportP Y H b)(h:0 ≤ H):SupportP (skirt X Y) H (a*b):=by
 have hh:0 ≤ joinV (stake H) Y:=sum_nonneg fun i _=>mul_nonneg ((stokes h).fee _) (p.yes _)
 exact ⟨skirtPos _ _ v.yes p.yes,(turnS (stokes h) X Y v.yes p.yes).trans (mul_le_mul v.gold p.gold hh (v.pos_v h))⟩
lemma pearP(h:0 ≤ a):SupportP (Iva.naked (n:=o) (steel k a)) H (steel k a):=by
 refine ⟨fun i=>?_,?_⟩
 · rw [Iva.naked,Pi.single_apply]; split; unfold steel; positivity; exact le_rfl
 unfold Iva.naked; rw [joined,show stake (n:=o) H ∅=1 from pow_zero _,one_mul]
abbrev ST (k:ℕ):=steel k (Real.exp 1)
abbrev goT(q:ℝ)(k:ℕ)(v:ℝ):=steel k (2*q)*(ST k*v)
abbrev cuP(q:ℝ)(k:ℕ)(s t:ℝ):=goT q k t + goT q k t + (ST k*s)*(ST k*s)+(ST k*s)*(ST k*s)
lemma escort(v:SupportP X H a) (h:0 ≤ H): SupportP (Iva.solo k X) H (ST k*a):=(pearP k (Real.exp_pos _).le).skirtS v h
lemma hop{Z W:Raid o}{b:ℝ}(v:SupportP X H a)(t:SupportP Y H a)(z:SupportP Z H c)(w:SupportP W H c)(p:0 ≤ b)(h:0≤H):SupportP (Iva.duet k b b X Z Y W) H (cuP b k a c):=by
 let P₀:SupportP (plink o k b) H (steel k (2*b)):=pearP k (by positivity)
 let Q:=skirtS (escort k v h) (escort k t h) h; exact ((((P₀.skirtS (escort k z h) h).sadd (P₀.skirtS (escort k w h) h)).sadd Q).sadd Q)
abbrev Bx (k:ℕ)(x:ℝ)(a b H:ℝ):= steel k (Kplan k a)+ H^2*steel k ((countH (radiusB x+1):ℝ)^2*Kplan k b)
lemma sunday (x:ℝ)(o:Site (More N))(h:0≤a)(g:0≤b): SupportP (cull k (groveR N (radiusB x+1) o (Kplan k b)) (Kplan k a)) H (Bx k x a b H):=by -- tune implicit N
 refine ⟨cull_p _ _ (fun i j=>gro_p _ (plan_nn k g) _ _ _ _) (plan_nn k h),?_⟩
 rw [stars]; exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lens_u o _ (plan_nn k g)) (by positivity)) (sq_nonneg H))
abbrev BaseT(k:ℕ)(x:ℝ)(W:Wages)(H:ℝ):= Bx k x W.tip W.puff H
abbrev TopT(k:ℕ)(x:ℝ)(W:Wages)(H:ℝ):= Bx k x W.spring W.span H
abbrev PowerP(k:ℕ)(x:ℝ)(W:Wages)(H:ℝ):=Real.exp (BaseT k x W H)* BaseT k x W H ^2
abbrev PnT(k:ℕ)(x:ℝ)(W:Wages)(H:ℝ):=Real.exp (BaseT k x W H)*BaseT k x W H
abbrev VoltP(k:ℕ)(x:ℝ)(W:Wages)(H:ℝ):=PowerP k x W H+PowerP k x W H+ TopT k x W H
lemma sunV (o:Site (More N))(x:ℝ)(W:Wages)(h:0 ≤ W.tip)(u:0≤W.puff)(z:0≤W.span)(v:0 ≤ W.spring)(p:0≤H):SupportP (sliceP x N o W k) H (PnT k x W H) ∧ SupportP (evenX x N o W k) H (VoltP k x W H):=by
 let B0:= BaseT k x W H; have hp:= sunday (H:=H) k x o h u; have he:= (hp.sab 2 p) -- tune elaborator
 refine ⟨(hp.sab 1 p).more (by change Real.exp B0 * B0 ^ 1≤ _; rw [pow_one]), (he.sadd he).sadd (sunday k _ o v z)⟩
end SupportP
end YM.CF.Wray
