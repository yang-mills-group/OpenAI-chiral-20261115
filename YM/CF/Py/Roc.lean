import YM.CF.Py.Fuse
import YM.CF.Py.Sole
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a α:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W) (M:Side)(ht:T.q ≤ M.val)(l0:ℕ)
local notation "L'"=>R.L
variable {r h:ℝ}{N':Side}(J:Robes N' V W)(q:Chi)
variable (Ta: Warm V U W N0 J.n i p q J.k J.d J.roomX a h) (F G:ℕ→ℝ→ℝ)
-- Everything SAME Gram path. Chime.F.Transits Print. includes output budgets and unmasked normalized expansion on every admissible law.F.No β Continuation.
structure Charted (D:Month x a i p N0 V W)(M:Side)(hM:D.q ≤ M.val) (B0:ℕ→ℝ) (Y:Cape M B R.L)(X: Vestal M B R.L) : Prop where
 day: Due V a p i N0 D M hM l0 B0
 mark(j:ℕ): Rue.IsleB SU.group (D.a j).threshold
 roof(j:ℕ):RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (Y j) (apt M B R.L j) q
 unit:Flourish V a p i N0 D M hM l0 J q h B0 F G Y X 0
 uptime(j:ℕ): (D.a j).threshold ≤ J.k
variable (hi:6≤ i)(hp:2≤p)(ha:0<a)(hF:Valley V q J a h N0 p Ta l0 F G)
-- θ.CLM all ABOVE arrears. Any period M of compatible congruence once M.val≥ Theta.Log.Roc.M. One calendar FOR ALL. h fixed.
abbrev grainZ (S:GivenX V U)(j:ℕ)(x:ℝ):ℕ:=S.n+(100+j)*(1+Pressure.radiusB x)
structure ClockT (u:ℝ)(D:Month u a i p N0 V W) :Prop where
 z :D.q=grainZ V W N0 u
 calendar(M:Side)(t:J.h≤M.val)(pM:D.q ≤ (M*N').val) :∃ (B0:ℕ→ℝ)(Y:Cape (M*N') B R.L)(X: Vestal (M*N') B R.L), Charted V a p i N0 l0 J q F G D (M*N') pM B0 Y X (h:=h) -- implicit h not synthesized until field include!
-- use all in type binder H.
include hi hp ha hF
lemma seed_p (z:ℝ):∃ u:ℝ,z<u∧ ∃ D:Month u a i p N0 V W, ClockT V a p i N0 l0 J q F G u D (h:=h) :=by
 obtain ⟨v,P⟩:= eventually_atTop.mp hF.use; obtain ⟨w,Q⟩:= eventually_atTop.mp (Month.fitX i p N0 hi hp V W)
 have he:Tendsto Pressure.temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 obtain ⟨x,hx⟩:=eventually_atTop.mp (he.eventually (ge_mem_nhds J.ht)); let Q':=max z (max x (max v w)); obtain ⟨u,hu,t⟩:= Rue.inherits SU.group Q' _ (pitch R.L)
 have hp:v ≤ u ∧ w ≤ u :=⟨le_trans (le_max_left ..) ((le_max_right ..).trans ((le_max_right ..).trans hu.le)), le_trans (le_max_right ..) ((le_max_right ..).trans ((le_max_right ..).trans hu.le))⟩
 obtain ⟨T,hx0⟩:= Q _ hp.2 _ ha; refine ⟨u,(le_max_left ..).trans_lt hu, T,⟨by rw [hx0]; simp only [grainZ,hat,Nat.cast_zero,zero_mul,add_zero],?_⟩⟩
 intro M v' t'; choose Y HY using fun i=> form_t V U W J q v' i
 obtain ⟨B0,p0,p1,q2⟩:= T.book t' l0
 obtain ⟨K',X⟩:= plan_u V a p i N0 T (M*N') t' l0 J q h B0 F G Y ⟨p0,p1,q2⟩ Ta hF (P _ hp.1) HY
 refine ⟨B0,Y,K',⟨⟨p0,p1,q2⟩,fun i=>?_,HY,X,fun i=>?_⟩⟩
 · rw [(T.boot _).1]; exact t _
 rw [(T.boot _).1]; exact hx _ ((le_max_left ..).trans ((le_max_right ..).trans (hu.le.trans (crown R.L u i))))
end YM.CF.Py
