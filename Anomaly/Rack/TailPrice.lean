import Anomaly.Rack.Collect
import YM.SU5.Interaction.Kerosene.FuelDesk
/-!
Paying OrbitRack tariff using the actual Quench on F births and operator
costs from candles. Choose κ=1 (Kf also Quench), Γ Quench, bandwidth 1/B
using L=1+5/b, rate inside operator reserve at 1+8/b. No iterative
investment per footprint.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}

namespace BScale

open Roots Wray Py Ione Lor Push.AbsoluteSums.Animals Vow Stax Cadre Sour Vow.TreasuryFog

lemma npl_chill {C:ℝ→ℝ}(p:BPress.NPL C): Chill_v C:= p.vanish

abbrev inkScatter (k:ℕ)(B : ℕ)(U:ℝ) := taxIns (10*B) * (k:ℝ) * (Real.exp 1 * U)

lemma billScatter (k:ℕ)(T:ℝ→ℝ)(p:Chill_v T) : Chill_v (fun i=>inkScatter k (radiusB i) |T i|) := by
  let f(i:ℝ):= taxIns (10*radiusB i); have ht:BoreP f:=by
    simp only [f,taxIns,Nat.cast_mul, Nat.cast_ofNat]; exact (BoreP.still _).grip (((BoreP.still _).grip BoreP.radius_c).self _)
  exact Chill_v.leanB ((p.trend (F:=fun i=>|T i|) (Eventually.of_forall fun i=>by simp)).cheap (Real.exp 1)) (ht.grip (BoreP.still _))
lemma billScatter2 (k:ℕ)(T:ℝ→ℝ)(p:Quench R T) : Quench R (fun i=>inkScatter k (radiusB i) |T i|) := by
  let W(x):=pinpr R.L x
  let C (x):= T x / W x
  have h:=billScatter k C p
  apply Chill_v.trend h; filter_upwards with i
  unfold inkScatter; apply Eq.le; apply congrArg abs
  have hv: 0 ≤ W i := sq_nonneg _; unfold C; rw [abs_div,abs_of_nonneg hv]; unfold W pinpr; ring

lemma productQuench {T:ℝ→ℝ}(p:Chill_v T) : Quench R (fun i=>T i*pinpr R.L i):=by
  apply Chill_v.trend p; filter_upwards [(draft_π R.L)] with i h
  rw [mul_div_cancel_right₀]; exact (pow_pos h.2.1 _).ne'

-- Big scalar inequalities required to pay from *same* flag and palette at this level.
-- W:=Departure (kernel full). Y:=birth. K:=force.
structure ThresholdPool (B:ℕ)(δ F K Y U:ℝ) : Prop where
  -- δ=1/B, U is occupied end-coats Γ
  roof_limit : 0 < δ ∧ 5*δ≤1/2
  κval:0<U
  fog: spanV B * U ≤ δ
  start: |K| < U
  rank: degreePrice B (100*U) δ≤ 1/2 ∧ degreePrice B U δ < 1
  dollars : U*(1-degreePrice B U δ)⁻¹ ≤ 1
  cover : U+Real.exp 1*(U*(1-degreePrice B U δ)⁻¹) ≤ 100*U
  price : spanV B * |F| ≤ δ
  void : |Y|+(δ⁻¹*spanV B*|F|)*U-(δ-spanV B*|F|)*U < 0

lemma spanning {F K Y:ℝ→ℝ}(L:Patch)(f:Chill_v F)(k:Quench L K)(p: Quench L Y):
    ∃ U:ℝ→ℝ,Quench L U∧∀ᶠ i in atTop,ThresholdPool (radiusB i) (runway i) (F i) (K i) (Y i) (U i):=by
  let b(x:ℝ):ℝ:= radiusB x; let S(x:ℝ):ℝ:= spanV (radiusB x);
  let V(x):=pinpr L.L x; let H(x):=V x * V x
  have hV: Quench L H:= productQuench (npl_chill (nq L.L))
  let E(x):= |K x|+ |Y x| + H x
  let G(x):= b x*E x
  let U(x):= 4*G x
  have hv:Quench L U:=(((k.normF.addL p.normF|>.addL hV).bondF BoreP.radius_c).manyF (4:ℝ))
  refine ⟨U,hv,?_⟩
  let D:=runway; have hF : Chill_v (fun x=>|F x|):= f.trend (Eventually.of_forall fun _=>by simp)
  have hδ:Quench L (fun i=>dollarT _ (runway i) (U i)):= dollar_Q _ _ hv
  have hK:Chill_v (fun x=> (b x)^2*(S x* |F x|)):= (hF.leanB span_bore).leanB (BoreP.radius_c.self _)
  have hS:Chill_v (fun x=>b x * (S x* U x)):= (hv.illum_Q.leanB span_bore).leanB BoreP.radius_c
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 10,
    draft_π L.L, hK.spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num)), hδ.illum_Q.spine_a.eventually (ge_mem_nhds zero_lt_one), hS.spine_a.eventually (ge_mem_nhds zero_lt_one),
    (deg_chill _ (hv.illum_Q.cheap 100)).spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    (deg_chill _ (hv.illum_Q)).spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num))] with x hx hp t d g v u
  have hxb:10≤b x:= by unfold b; exact_mod_cast hx
  have hxb': 0<b x:= by linarith only [hxb]
  have h' :0< H x:=mul_pos (pow_pos hp.2.1 _) (pow_pos hp.2.1 _)
  have pE : 0 < E x:=add_pos_of_nonneg_of_pos (by positivity) h'; have hU : 0 < U x:=by unfold U G; positivity
  change (b x)^2 * (S x * |F x|) ≤ 1/4 at t
  change b x * (S x * U x) ≤ 1 at g
  have w:0< D x:=inv_pos.mpr hxb'; let C:= U x
  have hu': 1/2 ≤ 1-degreePrice (radiusB x) (U x) (runway x):=by linarith only [u]
  have hb: (1-degreePrice (radiusB x) C (D x))⁻¹ ≤ 2:=by
    exact (inv_anti₀ (by norm_num : (0:ℝ)<1/2) hu').trans_eq (by norm_num)
  have hg : |K x| < E x := (le_add_of_nonneg_right (abs_nonneg (Y x))).trans_lt (lt_add_of_pos_right _ h')
  have hD : E x= U x*(D x)/4:=by unfold D runway U G; change _=4*(b x* _)*(b x)⁻¹/4; field_simp
  have hY: |Y x| ≤ U x*D x/4:= hD ▸ ((le_add_of_nonneg_left (abs_nonneg (K x))).trans (le_add_of_nonneg_right h'.le) : |Y x|≤ E x)
  have hB': D x≤ 1/10:=by
    rw [one_div]; exact inv_anti₀ (by norm_num) hxb
  have ut: b x * (S x*|F x|) ≤ (D x)/4 := by
    have he:b x* (S x* |F x|) ≤ (b x)⁻¹ *(1/4) := (le_inv_mul_iff₀ hxb').mpr (by linarith only [t])
    exact he.trans_eq (by change _=(b x)⁻¹/4; ring)
  have st : 0 ≤ S x := Nat.cast_nonneg _
  have hy: S x*|F x| ≤ D x/4:= (le_mul_of_one_le_left (mul_nonneg st (abs_nonneg _)) (show 1≤ b x by linarith only [hxb])).trans ut
  refine ⟨⟨w,(by change 5*D x ≤1/2; linarith only [hB'])⟩,hU, (le_inv_mul_iff₀ hxb').mpr g|>.trans (mul_one (b x)⁻¹).le,?_, ⟨v,u.trans_lt (by norm_num)⟩, (show _ from by simpa only [dollarT,pow_zero,mul_one] using d),?_, le_trans hy (by change D x/4 ≤ D x; linarith only [w]),?_⟩
  · nlinarith only [hD,hg,hxb',hU,w,mul_le_mul_of_nonneg_left hB' hU.le] -- top flag
  · have hv := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hU.le) (Real.exp_pos 1).le
    have hp : Real.exp 1 * (U x*2) ≤ 6*U x:=by nlinarith only [mul_le_mul_of_nonneg_right Real.exp_one_lt_d9.le hU.le,hU]
    linarith only [hv.trans hp,hU]
  rw [show (runway x)⁻¹=b x from inv_inv _]
  change |Y x| + _-(D x-S x* |F x|) * U x < 0 -- missed U factor lhs
  have hh:S x*|F x|≤ D x/4:=hy; nlinarith only [hY,hU,mul_pos hU w,mul_le_mul_of_nonneg_right ut hU.le,mul_le_mul_of_nonneg_right hh hU.le]

end BScale
end YM.CF.Py.Rate
