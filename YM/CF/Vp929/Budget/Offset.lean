import YM.CF.Vp929.Budget.Correction
import YM.CF.Graph.Sore
import YM.CF.Sedge.Craft
import YM.UVNext.COUPLING_RESET.Probe
import YM.Push.BETA_TRANSPORT.Separation

/-! Offsets in different representations: use the scalar read at identity. -/
set_option autoImplicit false
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

variable {J : Type} [LinearOrder J] [Fintype J] {P : Op J} {p : Wave J} (A : IsStarProjection P) (h : Sea P p)
include A h
lemma erase (i : LeanV J) : acts (star (drawT P i)) p=0 := by
  unfold drawT; split
  · rw [seekF,prong_p]; exact tars A h.1 (by rw [← act_mul,mul_sub,mul_one,A.isIdempotentElem.eq,sub_self,act_zero])
  rw [hideF,prong_t, remove,star_star]; exact tarp A h.1 (by rw [← act_mul,A.isIdempotentElem.eq])
omit A h in
lemma column_head {I : Type*} [LinearOrder I] [Fintype I] {J : Type*} [Monoid J] (F : I → J) {b : Finset I} (hb : b ≠ ∅) : ∃ i c, Scree.column F b = F i * c := by
  unfold Scree.column; cases hp : b.sort (· ≤ ·) with
  | nil => have ht:= congrArg List.length hp; simp [hb] at ht
  | cons i L => exact ⟨i, _, rfl⟩
lemma testTank (r : ribbon J) : inner ℂ p (acts (tank P r) p) = pane r := by
  rw [tank, act_sum, inner_sum, Finset.sum_eq_single ∅]
  · rw [act_smul,inner_smul_right,Scree.column]; simp [inner_self_eq_norm_sq_to_K,h.2]; rfl
  · intro b _ hb
    obtain ⟨i,c,hx⟩:= column_head (drawT P) hb; rw [act_smul, inner_smul_right,hx,act_mul,←act_inner,erase A h,inner_zero_left,mul_zero]
  simp
omit A h
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m n B : Side} (U : Grasp V.U B d)
open UVNext.CouplingReset
local notation "N" => mid m B
lemma sea_read {p : BudgetPoint} (f : PathData SU.group) (c : Clip) (S : Scree.Loom N)
    (I : Interest N) (F : Corr N) (v : ℂ) (b : ℝ) (y : Orbit N)
    (hx : flags p.threshold y.1=∅) (hp : U.roundZ ≤ (N).val) (hg : Guard (S y) d) :
    let B := changeM U (S y) I.M
    inner ℂ B (denZ (construct p f c I b F v) U S y) = Complex.exp (v - f.inChannels c p b y.1 - Pec.pigment I.I (S y) + pane (exponentL p F.1 y.1) + pane (Hest.boat (I.P.den (S y)))) := by
  intro B; let P:=spar K.j I.M (S y); let A:= exponentL p F.1 y.1; let U':= Hest.boat (I.P.den (S y))
  have he : IsStarProjection P:= (U.broadness _ hp _).projection _ hg
  have hy:= Spire.sea_g (P:=U) hp (S y) hg I.M
  let T:= (nursery P he).cook
  unfold denZ GramM.board relV; dsimp only [construct]; rw [Vale.still_Footprint,add_zero,fuel_one _ _ _ hx,mul_one]
  rw [← Hest.birth _ _ he, ← Poly.rising]
  change inner ℂ B (Complex.exp _ • acts (T (exp A)) (acts (T (exp U')) B))=_
  rw [inner_smul_right,←act_mul, ←map_mul T]; unfold T; rw [←tank_eq,testTank (p:=B) he hy (exp A * exp U')]
  change Complex.exp (v - f.inChannels c p b y.1 - Pec.pigment I.I (S y)) * panHom _ _= _
  rw [map_mul,show panHom _ (exp A) = _ from paneExp A,show panHom _ (exp U') = _ from paneExp U',← Complex.exp_add,← Complex.exp_add]; congr 1; dsimp [A,U']; ring
lemma clear_identity (p : BudgetPoint) : Rue.FleetS p.threshold (1:Pane n) := fun i => by simpa [faceValue,square,travel,Lattice.oriented] using (ne_of_lt p.threshold_pos)
open Push.BetaTransport in
lemma channels_identity (f : PathData SU.group) (c : Clip) (p : BudgetPoint) (b : ℝ) : f.inChannels c p b (1:Pane n)=0 := by rw [channels_split, kinetic_one, loop_one,mul_zero,zero_add]
lemma exponent_paid {p : BudgetPoint} {F : Corr n} {h a : ℝ} (hh : 0 ≤ h) (H : Cost p h a F) (U : Pane n) : |(pane (exponentL p F.1 U)).re| ≤ a*sites n :=
  (Complex.abs_re_le_norm _).trans ((pane_cost _ hh).trans (Graph.toeE H.inc hh U))
lemma compare_real {q q' : BudgetPoint} {f : PathData SU.group} {c : Clip} {I : Interest N} {F F' : Corr N} {S : Scree.Loom N}
    {v v' : ℂ} (b b' : ℝ) {h h' a a' : ℝ} (hp : U.roundZ ≤ (N).val) (hg : ∀ x, Guard (S x) d) (hh : 0 ≤ h) (hh' : 0 ≤ h')
    (p : Cost q h a F) (p' : Cost q' h' a' F')
    (e : ∀ y, Rue.FleetS q.threshold y.1 → Rue.FleetS q'.threshold y.1 → denZ (construct q f c I b F v) U S y = denZ (construct q' f c I b' F' v') U S y) :
    |v.re-v'.re| ≤ (a+a')*sites (mid m B) := by
  let y : Orbit (mid m B):= (1,Classical.arbitrary _)
  let P:= exponentL q F.1 (1:Pane _); let Q:= exponentL q' F'.1 (1:Pane _)
  have hv:= congrArg (fun x=> ‖inner ℂ (changeM (m:=m) U (S y) I.M) x‖) (e y (clear_identity q) (clear_identity q'))
  rw [sea_read U f c S I F v b y (flags_one _) hp (hg _),sea_read U f c S I F' v' b' y (flags_one _) hp (hg _)] at hv
  dsimp only [y] at hv; simp only [Complex.norm_exp,Real.exp_eq_exp,Complex.add_re,Complex.sub_re, Complex.ofReal_re, channels_identity] at hv
  have he:= abs_le.mp (exponent_paid hh p 1); have ht:= abs_le.mp (exponent_paid hh' p' 1); exact abs_le.mpr ⟨by linarith [he.1,ht.2,he.2,ht.1],by linarith [he.2,ht.1,he.1,ht.2]⟩

lemma ae_fleet {x : ℝ} (p : Rue.IsleB SU.group x) : ∀ᵐ y ∂city n, Rue.FleetS x y.1 := (measurePreserving_fst (μ:=prior SU.group (More n)) (ν:=depot n)).quasiMeasurePreserving.ae (p _)
end YM.CF.Py.Rate
