import YM.SU5.FiniteGaugeData.LocalLimit.Physical
import YM.CF.Continuum.CandleRoom

/-! # Donor compatibility with the top shire integral, and propagation of a
restricted reflected form on gauge probes

Horizontal arrows in our setting. Adapted from CF/Continuum's helpers on
its different trajectory packages. `Donor` is not the trajectory from CandleRoom,
but it **does** give a `Carousel` argument using the price rate delivered in
heat election. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x delay wα y : ℝ} {C D Q R0 E Cf δ Fp : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {D' : Heron V 1 2 6 N0 0 J q h wα R0 E Cf δ y} {hy : y ≤ x} {V0 Jx : ℕ → ℝ}
local notation "Ω" => cell m B R.L
local notation "kT" => trunkY n b
local notation "kS" => buoy n
local notation "B'" => ActualSpine T ht W0 f kT
local notation "BT" => Actual T ht W0 f kT
local notation "Yb" i:max => dleaf R.L (hat R.L x i)
local notation "Γ" => StarPS kT
local notation "Φ" i:max => wage_B n b i R.L x
open Brace

namespace Donor
variable {F0:Scrolls B} (Y:Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0)
open Period Window
open scoped ComplexOrder
include ht
protected def carnival : Carousel V 1 2 6 N0 J q h Q D x m (buoy n):=by
 have hm:buoy n≤post_H n:= Nat.le_add_right ..; have he:kS ≤ kT:= hm.trans (by unfold trunkY; omega)
 refine ⟨T,ht,kT,he,B0,Y.gram,W0,Y.wave,Y.tilt,Y.pull.wear,Y.pull.owns,Y.pull.sift,Y.rare,Y.pole,Y.cape,Y.due,?_ ,Y.balance,Y.pull.color.trans Y.due.unit,fun i v=>?_ ,fun i z=>?_ ,fun i z=>?_,fun i z=>Y.pull.shift _ (z.trans_le he)⟩
 · intro i z; have h:=(Y.pull.note i z).lot; have he:= Y.pull.owns _ z
   refine ward_m (show (Y.gram i).path.Bounds (Y.gram i).funds K.top.width K.top.paths V.W.bar from ?_) h
   rw [← (show _ =(Y.gram i).path from he.path), ←(show _ =(Y.gram i).funds from he.fund)]; exact V.L.mood _
 · exact (Y.pull.tip i (v.trans_le he)).trans_eq (by unfold coldQ; rw [if_pos v])
 · have ht:= Y.pull.price i (z.trans_le he); rwa [mode_D,if_pos z] at ht
 have hz:= Y.pull.note i (z.trans he); rw [Y.vane _ z,zone_F,if_neg (not_lt.mpr (z.trans hm))] at hz; exact hz
local notation "Tr" => Y.carnival ht

-- This time scale is specific to its Donor, as is the operator connection
-- to physical top marks. `TestOK` is for the canonical reflected seam at plane 0.
open Mir Mir.Trip Reflect Spark
variable {A r v:ℝ} (hp:∀ m,ScaleK A r (F0 m)) (hw:Budget B d v)
local notation "M_" => Vale.mesh m R.L (trunkY n b)
local notation "ξ" => cell m B R.L
local notation "Z₊" j:max => partitionZ (Y.gram j) U (W0 j)
local notation "T…" => RP.Str.shireF K.top.clip (T.a kT).threshold (Y.gram kT).beta (F0 M_) d 0 (↑(radiusB (hat R.L x kT)):ℝ) 1 (Brace.northZ M_ B)
abbrev probe (j:ℕ) := Window.finiteForm V.U U (Y.gram j) (W0 j)
local notation "Φ…" => probe ht Y
include hp hw
lemma top_interface (X:Window.Evaluation (ξ kT))(hc:Continuous X) :
    (∫ i:Orbit (ξ kT),inner ℂ (mateK _) (acts (X i.1) (denZ (Y.gram kT) U (W0 kT) i)) ∂city _)= (T…) (Chaff.leer M_ B X) := by
 have he: Y.gram kT=fulvia Y.top Y.offset (Vale.launch V.L (Y.gram kT).beta (T.a kT) (ξ kT)):= Y.pull.boot.trans (by rw [hue_top]; rfl)
 conv_lhs=> rw [he]
 exact Chaff.lit_R _ _ _ _ Y.lives X hc (hp _) hw (Y.rare _)
lemma vacuum : Z₊ kT = (T…) (emptyF M_ B) := by
 let X(i:Pane (ξ kT)):FC (Single (ξ kT)):=1; have he:leer M_ B X=emptyF M_ B:=funext fun _=>Window.cross_one _
 rw [←he,← Y.top_interface ht hp hw X continuous_const]
 unfold X; simp [partitionZ]
lemma positive {j:ℕ} (hj:j≤ kT)(hz:(Z₊ j)≠0):0< (Z₊ kT) := by
 rw [Y.balance _ hj] at hz
 have he:= Y.vacuum ht hp hw; refine lt_of_le_of_ne ?_ hz.symm
 rw [he, ← grass_Q M_ B (0:Site (More M_)) (northZ M_ B) (0:Axis)]
 exact RP.Str.greenRF _ _ _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (hp _) hw _ _ _ ⟨continuous_const, fun _=> Sector.one,fun _ _ _=>rfl⟩
omit hp hw
lemma normalized (j:ℕ)(hj:j ≤ kT): Integrable (fun x:Orbit (ξ j)=>(partitionZ (Y.gram j) U (W0 j))⁻¹ • denZ (Y.gram j) U (W0 j) x) (city _) :=by
 have hi:= Girt.sailW (Y.gram j) ((Tr).legal j hj) W.pearl V.note W.health (by have h:=V.L.lobby; have ht:=R.order_cut; omega) J.n _ (Carousel.loomActs V 1 2 6 N0 J q h Q D Tr j) (J.gran.trans ((Tr).roof j).size)
 exact (Integrable.of_bound (μ:=city (cell m B R.L j)) hi.meas.aestronglyMeasurable _ (Eventually.of_forall hi.cost.choose_spec)).smul ((partitionZ (Y.gram j) U (W0 j))⁻¹)
include hp hw
lemma PSD_offer (s:Axis) (hz: Z₊ kT ≠ 0) : TestOK M_ B s (Φ… kT) := by
 have hx:= Y.normalized ht kT le_rfl
 constructor
 · intro X Y hx' hy; exact Window.moment_add hx hx' hy
 · intro X _ a; exact Window.moment_scalar X a
 intro X xk; let Z:= ticketWeights s xk; let W':= flipTime M_ B s X * X; have hc : Continuous W' :=
    ((mem_localObs _).mp (flipTime_positive s xk)).1.mul ((mem_localObs _).mp xk).1
 have hh:0 ≤ T… (squareR M_ B 0 (northZ M_ B) s (toTicket s X) false):= RP.Str.greenRF _ _ _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (hp _) hw s _ _ Z
 rw [ticket_η s xk,←Y.top_interface ht hp hw W' hc] at hh
 change 0≤ finiteForm V.U U _ (W0 kT) W'; rw [by_denominator]; exact div_nonneg hh (Y.positive ht hp hw le_rfl hz).le
universe w
variable {I:Type w}[Fintype I]
lemma PSD_buffered (s:Axis) (j:ℕ)(hj:j ≤ kT)(hz: (Z₊ j) ≠ 0)(X:I→Pane (ξ j)→ℂ)(u:∀ i,ξTape s R _ (X i)) :
    (reflectionForm (B:=B) s (Φ… j) (fun i=>bosonic (ξ j) (X i))).PosSemidef:=by
 let k:= kT-j
 have hh:j+k=kT:=by omega
 have htZ:=hz; rw [Y.balance _ hj] at htZ
 have hv(m':ℕ)(X₀:I→Pane (ξ m')→ℂ)(u:∀ i,ξTape s R _ (X₀ i))(pK:m'=kT): (reflectionForm (B:=B) s (Φ… m') (fun i=>bosonic (cell m B R.L m') (X₀ i))).PosSemidef:=by
    subst m'; exact psdTape _ (Y.normalized ht kT le_rfl) (Y.PSD_offer ht hp hw s htZ) X₀ u
 let F:= fun i:I => Carousel.liftV V 1 2 6 N0 J q h Q D Tr j (X i) k
 have hk: reflectionForm s (Φ… j) (fun i=>bosonic (cell m B R.L j) (X i))= reflectionForm s (Φ… (j+k)) (fun i=>bosonic (cell m B R.L (j+k)) (F i)):=by
    ext k' i'; exact Carousel.liftSquareG V 1 2 6 N0 J q h Q D Tr s (X k') (X i') (u k') (u i') k (hh.le)
 rw [hk]; exact hv (j+k) F (fun i=>Carousel.liftCost V 1 2 6 N0 J q h Q D Tr s _ (u i) k) hh
end Donor
end LocalLimit
end YM.CF.Py.Rate
