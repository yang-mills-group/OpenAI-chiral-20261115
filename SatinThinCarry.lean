import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance
variable (i k:ℕ) {P' V: Side} {f r v t m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
/- Actual-path Lease of Parliament: convoy and roots. Any number of supports. No stencils in cutoff budgets before size. -/
-- arithmetic delivery & Versions
local notation "X" s:max=> RootBook Y i k s
local notation:max "S" s:max=> (VO).CapeT s
abbrev morning(s:ℕ):= Scree.denZ (RootBook Y i k s) P.U ((VO).CapeT s)
def artwork {J:Type}[Fintype J][LinearOrder J] (E:Key J→ RegBudget (side Y i f))(F:Key J→ ForceBudget (side Y i f))(l:List J)(x:Orbit (side Y i f)):= tipI (directZ P.V P.U ((VO).CapeT f) (RootBook Y i k f) E F x) l
variable (p:Satin.PairIdx Y f i k)
-- dual lift used exact mark shape NO contour e.
variable {I J:Type} [Fintype I][Fintype J][LinearOrder I][LinearOrder J]
def carryStep : (Orbit (side Y i (f+1))→ Phys (side Y i (f+1)))→ (Orbit (side Y i f)→Phys (side Y i f)):= pushCloud (K:=P.K) P.J.d (Gξ f) (Stem Y i k f) (S f) (S (f+1)) (X (f+1)) Chi.canonical (patternQ Y f i k).val
include p
local notation "Qt"=>patternQ Y f i k
local notation "μ" s:max=> city (Ω s)
lemma kayStep {F:Orbit (side Y i (f+1))→ Phys (side Y i (f+1))}(t:Version (city (Ω (f+1))) F)(c:Mark (side Y i f))(v:AtSupport false univ c) : markedRead c (S f) (carryStep Y i k F)= markedRead (ascender Y f i k c) (S (f+1)) F:=by
 have a:= (fullness Y i k p.1).cap_grant; obtain ⟨l'⟩:= a.grant f p.2; exact liftCloud_step _ (Gξ f) l' (Stem Y i k f) (a.branch f p.2) (Qt) P.R.odd_side (Journey.legal P) v F t
lemma phaseStep {F:Orbit (side Y i (f+1))→ Phys (side Y i (f+1))}(t:Version (city (Ω (f+1))) F) : Version (μ f) (carryStep Y i k F):=by
 have a:= (fullness Y i k p.1).cap_grant; obtain ⟨l'⟩:= a.grant f p.2; exact cloud_version P.V _ (b:=l') (a.branch f p.2) t
omit p
variable {p':I→Site (side Y i f)} {u v:ℝ}
abbrev routeTip (c:ℝ)(s:ℕ)(x:Site (side Y i s)): Mark (side Y i s):=(↑c:ℂ) • turfMark (slotFee P s) (RootBook Y i k s).p.threshold x
lemma route_scalar (x:Site (Ω f))(s:ℝ)(z:Mark (side Y i f)) : Commute (routeTip Y i k s f x) z:=by
 unfold Commute SemiconjBy; funext v; unfold routeTip turfMark; simp only [Pi.mul_apply,Pi.smul_apply,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
lemma route_owns (s:ℕ)(u:ℝ)(x:Site (side Y i s)): AtSupport false (fatAt x 12) (routeTip Y i k u s x):=(cup_owns x _ _).smulM _
-- versions and arithmetic
noncomputable abbrev feeArr (x:Orbit (side Y i f))(o:Site (side Y i f)):ℂ:= clothMark (slotFee P f) (RootBook Y i k f).p.threshold o x.1
variable (o:Site (side Y i f))(l:List (Site (side Y i f))) {α: Orbit (side Y i f) → Phys (side Y i f)}
def chamber (o:Site (side Y i f)):= routeTip Y i k 1 f o
lemma chamber_cash (u:Orbit (side Y i f)) : chamber Y i k o (u.1,S f u)=feeArr Y i k u o • (1:FC (Single (Ω f))):=by unfold chamber routeTip turfMark; rw [Complex.ofReal_one]; rw [one_smul]
lemma chamber_bill : AtSupport false (fatAt o 12) (chamber Y i k o):= route_owns ..
lemma fee_safe : Version (μ f) (fun v:Orbit (side Y i f)=> feeArr Y i k v o):= ver_of (Env.along (g:=Prod.fst) (Girt.pole_w (clothMark (slotFee P f) (X f).p.threshold o) Complex.ofReal Complex.continuous_ofReal (coinZenv ..)) measurable_fst)
-- read laws at one Height.
variable (A:Mark (side Y i f)){α': Orbit (side Y i f) → Phys (side Y i f)}
lemma ring_plus (w:Envelope A)(u:Version (μ f) α)(v:Version (μ f) α') : markedRead A (S f) (fun t=> α t+α' t)= markedRead A (S f) α + markedRead A (S f) α':=by
 unfold markedRead; simp_rw [map_add]; have ht:= ((Y.voyage i).ownership f).paid.bill; exact integral_add (u.letterpay ht w) (v.letterpay ht w)
lemma ring_scale (z:ℂ) : markedRead A (S f) (fun t=>z • α t)=z • markedRead A (S f) α:=by unfold markedRead; simp_rw [map_smul]; rw [integral_smul]
lemma ring_toll : markedRead A (S f) (fun t=> feeArr Y i k t o • α t)= markedRead (A * chamber Y i k o) (S f) α:=by
 apply integral_congr_ae; refine ae_of_all _ fun x=>?_ ; dsimp only; rw [map_smul,Pi.mul_apply,chamber_cash,mul_smul_comm,mul_one]; unfold letterRead; simp only [ContinuousLinearMap.comp_apply]; rw [act_smul,map_smul]
lemma palm_plus {V:Mark (side Y i f)}(x:Envelope A)(w:Envelope V)(u:Version (μ f) α): markedRead (A+V) (S f) α=markedRead A (S f) α+markedRead V (S f) α:=by
 let U':= (S f); let v(B':Mark (Ω f))(t:Orbit (Ω f)):=letterRead (B' (t.1,U' t)) (α t); have ht(x):v (A+V) x=v A x+v V x:=by unfold v; rw [Pi.add_apply]; unfold letterRead; simp only [ContinuousLinearMap.comp_apply]; rw [act_add,map_add]
 change (∫ x,v (A+V) x∂μ f)=_; simp_rw [ht]; have hm:= ((Y.voyage i).ownership f).paid.bill; exact integral_add (u.letterpay hm x) (u.letterpay hm w)
lemma palm_scale (z:ℂ) :markedRead (z • A) (S f) α=z • markedRead A (S f) α:=by unfold markedRead; simp_rw [Pi.smul_apply,letterRead,ContinuousLinearMap.comp_apply,act_smul,map_smul]; rw [integral_smul]
lemma morning_safe (u:(Y.voyage i).kick≤k)(x:f≤Y.uv k) : Version (μ f) (morning Y i k f):=ver_of (Y.each_level i k f u x).permits
#print axioms kayStep
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
