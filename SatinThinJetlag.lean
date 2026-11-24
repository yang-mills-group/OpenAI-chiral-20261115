import SatinThinLoyal
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
variable (i k:ℕ) {P' V: Side} {f r v m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
/- Actual-path Lease of Parliament: convoy and roots. Any number of supports. No stencils in cutoff budgets before size. -/
-- arithmetic delivery & Versions
local notation "XP" s:max=> RootBook Y i k s
local notation:max "S" s:max=> (VO).CapeT s
/- Parliament finances. -/
variable {I:Type} [Fintype I] [LinearOrder I]
local notation:max "Rn" s:max=> slotFee P s
local notation "Ξ"=> Article I
local notation "Υ"=> Key (Article I)
local notation "ΞM"=>List (Article I)
-- first downward power. `Loyalty` reports exact density on the SAME sharp tape.
variable (o:I→Site (side Y i f))
local notation "Ƶ" s:max=> morning Y i k s
local notation "Πξ" p:max=>upRoot Y i p
local notation "Ξν" s:max =>nightSet Y i s (I:=I)
local notation "ΞV" s:max=> rideSet Y i s (I:=I)
local notation:max "flightY" p:max=>convoy Y i k p
local notation "µ" s:max=> city (Ω s)
variable {E:nightSet (I:=I) Y i f}{F:rideSet (I:=I) Y i f}
variable (p:f≤v)
local notation "ψξ"=> artwork Y i k E F
local notation "ϕ" b:max=> principal Y i k p b
local notation "δ" s:max=> mark_cost Y i k s
/- Open at f with tickets independent of all positions. Match open keys in `spray`. -/
variable {u A: ℝ} 
local notation:max "αq"=> openingCost o (Rn f) (RootBook Y i k f).p
local notation "Φ"=> artwork Y i k E F
local notation "ψx"=> artwork Y i k (openTabs (RootBook Y i k f) o (slotFee P f) E) (F∘unison)
local notation "𝜔"=> Orbit (side Y i f)
local notation "Dq" l:max t:max=> l.map (Prin:I→ Ξ)
local notation:max "Rτ" l:max z:max=> (artwork Y i k E F l z)
-- spent keys as List I (only a gap usage can spend). w/spare rule tests ensure existing prefix accum. `S` opener works on both even if mixed.
def stageInset(u:ℝ)(j:Ξ): Mark (Ω v):=let F':=principal Y i k p u (o (QuadClock.host j)); if layer j=0 then F' else F'-convoy Y i k p (chamber Y i k (o (QuadClock.host j)))
noncomputable def chapterRead (s:List I)(l:ΞM)(x:𝜔): Phys (side Y i f):= spray (αq x.1) (fun i=> Φ ((s++i.map QuadClock.host).map Prin) x) l
-- need E,F argument explicit
local notation:max "mt" s:max l:max=> chapterRead (E:=E) (F:=F) Y i k o s l
local notation "τ" s:max=> ((s).map (principal Y i k p u ∘ o)).prod -- hygiene s binder
local notation "Rt" s:max=> ((s).map (chamber Y i k ∘ o)).prod
local notation "Qt" s:max=> ((s).map ((convoy Y i k p) ∘ chamber Y i k ∘ o)).prod
local notation "αt"=> stageInset Y i k o p u
local notation "χ" s:max=> ((s).map (stageInset Y i k o p u)).prod
variable (U:Loyalty Y i k o p u E F)(v':v≤ Y.uv k)(x:(Y.voyage i).kick ≤ k) (z:Beyond P ℓ o 12)
protected lemma BudgetSum (F: Ξ→Mark (side Y i f))(c:∀ i,AtSupport false univ (F i))(l:ΞM): AtSupport false univ (l.map F).prod:=receipt_word c l (fun _ _=> Finset.Subset.refl _)

variable (j:I) {s':List I}(r':List (Article I))
lemma chapter_slice (s':List I)(j:Ξ): mt s' (j::r') =fun x:𝜔=> αq x.1 j • mt s' r' x+ mt (s'++[QuadClock.host j]) r' x:=by
 funext x; unfold chapterRead; rw [QuadClock.spray]; simp [List.map_cons,List.append_assoc]; -- no toga? simp risk
lemma chapter_term0 (s':List I) : mt s' (Prin j::r')= mt (s'++[j]) r':=by rw [chapter_slice]; funext i; rw [fee_station i.1 j,zero_smul,zero_add]; rfl
lemma chapter_term1 (s':List I) : mt s' (Astr j:: r')= fun t:𝜔=> (-1:ℂ) • (feeArr Y i k t (o j) • mt s' r' t)+mt (s'++[j]) r' t:=by
 rw [chapter_slice]; funext t; rw [fee_opening t.1 j,smul_smul,neg_one_mul]; rfl
omit p in
lemma enrol (l:ΞM)(j:I)(s:List I)(z:(s ++ (j::l.map QuadClock.host)).Nodup): (s++l.map QuadClock.host).Nodup∧ ((s++[j])++l.map QuadClock.host).Nodup:=⟨List.Sublist.nodup (show (s++_).Sublist (s++_) from List.Sublist.append (List.Sublist.refl s) (.cons j (List.Sublist.refl _))) z,by simpa [List.append_assoc] using z⟩
include U
lemma chapter_sky (s:List I)(l:ΞM)(z:(s++l.map QuadClock.host).Nodup): Version (µ f) (mt s l):=by
 induction l generalizing s with
 | nil=> apply Version.cong (U.sky s (by simpa using z)) (Eventually.of_forall fun x=>?_); simp [chapterRead,QuadClock.spray]
 | cons j l ih=>
    have hv:=enrol l _ s z; let k':= ih _ hv.1; let v:= ih _ hv.2; rw [chapter_slice]; refine plusV (prodV ?_ k') v
    rw [recover_art j]; generalize QuadClock.host j=y; generalize layer j=m; fin_cases m
    · exact (show Version (µ f) (fun _=> (0:ℂ)) from ver_of (Girt.rite_c _)).cong (Eventually.of_forall fun x=> (fee_station x.1 y).symm)
    have hp:= fee_safe Y i k (o y); obtain ⟨k,v,x⟩:=hp; exact ⟨_,((show _ =ᵐ[µ f] _ from Eventually.of_forall fun i=> fee_opening i.1 y)).trans (v.neg),Girt.pole_w k (fun i:ℂ=> -i) (by fun_prop) x⟩ -- direction
#print axioms chapter_sky
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
