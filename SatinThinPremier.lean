import SatinThinLoyal
import SatinThinRoster
import SatinThinTill
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
noncomputable abbrev APlot (s:ℕ):= upRoot Y i (Nat.le_refl s) -- unused
variable {p}
local notation "🌀"=>heel (Gξ f)
variable (pr:f<v) {A Z:ℝ}{U:Funds P.R.L}{T:Fin 2→ Topic (side Y i f)}{G:nightSet Y i (f+1) (I:=I)}{W₁:rideSet Y i (f+1) (I:=I)}
variable (x:Loyalty Y i k (Hove.heel (Vale.apt (Y.ir i) P.block P.R.L f) ∘ o) pr Z G W₁) -- pr: f<v definitional? indicates ≤ for f+1. unification if metavars. 
private lemma trace_words (D': ℝ) (l:List I) : (l.map (principal Y i k pr.le (D'*Z) ∘ o)).prod= ((↑(D'^l.length)):ℂ) • (l.map (principal Y i k (show f+1 ≤ v from pr) Z ∘ heel (Gξ f) ∘ o)).prod:=by
 induction l with
 | nil=> simp
 | cons i l ih=> rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,ih]; simp only [Function.comp_apply]; rw [Algebra.mul_smul_comm]; unfold principal upRoot; rw [climbing_step (X:=fun j=>Site (side Y _ j)) _ (o i) pr]; unfold routeTip; rw [Complex.ofReal_mul,←smul_smul, Algebra.smul_mul_assoc,smul_smul,List.length_cons,pow_succ]; push_cast; rfl
variable (prΞ:Satin.PairIdx Y f i k)(hu: transportA Y i k o G W₁ E F U)(hc:CityCall Y i k o)
include pr x prΞ hu hc
set_option maxHeartbeats 190000 in
lemma tribal_1 (l:List I)(w:l.Nodup) : Version (µ f) (artwork Y i k E F (l.map Prin)):=by
 have p:= pulse_P Y i k o G W₁ hu prΞ hc l w; exact (multV (a:= ↑(U.ticket^l.length)) (phaseStep Y i k prΞ (x.sky l w))).cong p.symm
set_option maxHeartbeats 340000 in
lemma tribal_2 (l:List I)(w:l.Nodup)(A:Mark (side Y i f))(h:AtSupport false univ A):
 markedRead A (S f) (artwork Y i k E F (l.map Prin)) = mark_cost Y i k v (convoy Y i k pr.le A*(l.map (principal Y i k pr.le (U.ticket*Z) ∘ o)).prod):=by
 let p:=prΞ
 let H:=hu
 have b:=hc
 let φ(l:List I):= artwork Y i k G W₁ (l.map Prin); let W':=carryStep (f:=f) Y i k
 have he(l v):= pulse_P Y i k o G W₁ H p b l v
 let H'(B':Mark (side Y i v)):=mark_cost Y i k v B'; let C'(l:List I)(b:ℝ):=(l.map (principal Y i k pr.le b ∘o)).prod; let y:= convoy Y i k (show f+1 ≤ v from pr) (ascender Y f i k A)
 let α:= (l.map (principal Y i k (show f+1≤v from pr) Z ∘ heel (Gξ f) ∘ o)).prod; let η:ℂ:= ↑(U.ticket^(l.length)); let W:= artwork Y i k E F (l.map Prin)
 have ht:markedRead A (S f) W=η • H' (y*α):=by
    have f0:=ring_scale Y i A (α:= W' (φ l)) η
    have hv':=kayStep Y i k p (x.sky l w) A h
    exact (read_version A (S f) (he l w)).trans (f0.trans (congrArg (η • ·) (hv'.trans (x.grant l w (ascender Y f i k A) (weight_all Y i k h p)))))
 -- have hβ : principal Y i k (f:=f) pr.le Z ∘ o=principal Y i k (show f+1≤v from pr) Z ∘ heel (Gξ f) ∘ o:=funext fun k=> congrArg _ (climbing_step _ (o k) pr) -- maybe unused delete
 have hv : y=convoy Y i k pr.le A := (climbing_step (X:=fun s=> Mark (side Y i s)) (fun s=> ascender Y s i k) A pr).symm
 have hz : C' l (U.ticket*Z)=η • α := trace_words Y i k o pr U.ticket l
 have ha : η • (y* α) = (convoy Y i k pr.le A * C' l (U.ticket*Z)) := by rw [hz,←hv, Algebra.mul_smul_comm]
 exact ht.trans ((palm_scale (f:=v) (α:=morning Y i k v) Y i (y*α) η).symm.trans (congrArg H' ha))
lemma tribal : Loyalty Y i k o pr.le (U.ticket*Z) E F:= by
 constructor
 · intro l w; exact tribal_1 Y i k o pr x prΞ hu hc l w
 intro l w A v; exact tribal_2 Y i k o pr x prΞ hu hc l w A v
omit pr x prΞ hu hc
-- all tableaux, independent arrays.
structure Consulate (p:f≤v)(A b:ℝ):Prop where
 aims: Premier L (v-f) b
 emit: ∃ Z:Fin 2→ Topic (side Y i f),∀ (I:Type)[Fintype I] [LinearOrder I] (o:I→ Site (side Y i f)), CityCall Y i k o →∃ (E:nightSet Y i f (I:=I))(F:rideSet Y i f (I:=I)), weather_Tab Y i k o A Z E F ∧ PanAt Y i k A E F ∧ Loyalty Y i k o p b E F
variable {pr}
lemma launch_card (f:ℕ)(t:Credentials Y i k A f f): Consulate Y i k (Nat.le_refl f) A 1:=by
 constructor; · rw [Nat.sub_self]; exact premier_zero _
 refine ⟨host_set Y i k f,fun I _ _ o p=>⟨baseTab Y i k o,0,?_,?_,start_frame Y _ _ o t.pays t.caps⟩⟩
 · exact ((t.pass f le_rfl le_rfl).2 I o p).1
 exact ((t.pass f le_rfl le_rfl).2 I o p).2
-- stronger H expose period-dependent Γ matrix schedule. Output can't be priced until shape granted in at least one eligible consultation, Money clause clamps.
lemma tip_toe {B':ℝ}(pr:f<v)(Q:Consulate Y i k (show f+1 ≤ v from pr) A B')(v0:Credentials Y i k A f v): ∃ b:ℝ, Consulate Y i k (p:=pr.le) A b:=by
 obtain ⟨Z,W⟩:= Q.emit; obtain ⟨g,A'⟩:= (v0.hues f le_rfl pr).gives
 let U:= warpLine g Z P.R.L A (Rn (f+1)) (Rn f); have H:=v0.vacant Y i k (show f≤f+1 from Nat.le_succ _) pr
 refine ⟨U.ticket * B', ?_, hatchTopic P.R.L g Z A (Rn (f+1)) (Rn f),fun I _ _ o p=>?_ ⟩
 · rw [show v-f=(v-(f+1))+1 from by omega]; exact premier_L P.R.L _ B' U Q.aims
 obtain ⟨E,F,x,t,u⟩:= W I (heel (Vale.apt (Y.ir i) P.block P.R.L f) ∘ o) (sprint_B Y i k f (pr.trans_le v0.caps) v0.go o p);
 obtain ⟨E',F',z,a,b⟩:= @A' I _ _ Z o E F p (loosen_tabs x H.le (zero_le_one.trans v0.cost)); exact ⟨E',F',z,a,tribal _ _ _ _ pr u ⟨v0.pays,pr.trans_le v0.caps⟩ b p⟩
lemma purchased_theta (p: f ≤ v) : Credentials Y i k A f v→ ∃ b:ℝ, Consulate Y i k p A b:=by
 induction p using Nat.decreasingInduction with
 | self=> exact fun t=>⟨1,launch_card Y _ _ _ t⟩
 | of_succ f p ih=> intro t; obtain ⟨b,h⟩:= ih (t.part Y _ _ (show f≤f+1 from Nat.le_succ _) p le_rfl); exact tip_toe Y i k p h t
#print axioms purchased_theta
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
