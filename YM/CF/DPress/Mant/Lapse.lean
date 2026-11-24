import YM.CF.DPress.Mant.Echo
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {x:ℝ}{C:Tew W}{β:ℝ}{t:Yds (mid P B)}{v:ℂ}{b:ℝ}{O:Shore0} {Q:Maud x C G S}(m:Penny Q O)
 (E₀ E₁:Lobby Q O β)
open DPress.Analytic Salt Oise Quality
abbrev εΔ (O:Shore0) (D:ℝ) := 4*D/O.δ
-- Cost via Δ path relative witness.Note allows arbitrary offsets.
structure Lapse (E₀ E₁:Lobby Q O β)(D:ℝ):Prop where
 money: 0 < D
 budget: D≤ O.δ/4
 stip : AccountY Q.Y.p C.h E₀.F0 (O.δ/2)
 less : AccountY Q.Y.p C.h (E₁.F0-E₀.F0) D
variable {D:ℝ}
namespace Lapse
variable {E₀ E₁}(f:Lapse E₀ E₁ D)
abbrev Lrad (O: Shore0) (D:ℝ) := 1+1/(εΔ O D) -- ≤ old radius δ/(2D).
include f
lemma δpos : 0< O.δ := by linarith [f.budget,f.money]
lemma εpos : 0< εΔ O D:= div_pos (mul_pos (by norm_num) f.money) f.δpos
lemma εone : εΔ O D ≤ 1:= by rw [εΔ,div_le_one f.δpos]; linarith [f.budget]
lemma wide : 1 < Lrad O D:= lt_add_of_pos_right _ (div_pos zero_lt_one f.εpos)
lemma rwCost(a:ℝ): a/(Lrad O D-1)= εΔ O D*a:=by unfold Lrad; rw [add_sub_cancel_left]; ring_nf; simp -- tune
lemma pay : Léon Q.Y.p C.h R.L.val (E₁.F0-E₀.F0) D:=⟨f.less,(E₁.Φ.sub C.uB E₀.Φ).oily⟩
omit f
abbrev stream(X Y:Yds (mid P B))(z:ℂ):=X + z • (Y-X)
lemma point (z:ℂ)(y:‖z‖ < Lrad O D)(f:Lapse E₀ E₁ D): Léon Q.Y.p C.h R.L.val (stream E₀.F0 E₁.F0 z) O.δ:=by
 let τ:Léon Q.Y.p C.h R.L.val E₀.F0 (O.δ/2):= ⟨f.stip,E₀.Φ.oily⟩; apply (τ.add C.uB (f.pay.scale C.uB z)).more C.uB; have hp: ‖z‖*D ≤ Lrad O D * D:= mul_le_mul_of_nonneg_right y.le f.money.le; have ht: Lrad O D*D=D+O.δ/4:=by unfold Lrad εΔ; field_simp [f.money.ne', f.δpos.ne']
 linarith [f.budget]
def curve(f:Lapse E₀ E₁ D) (z:ℂ): Lobby Q O β:= if p:‖z‖<Lrad O D then ⟨stream E₀.F0 E₁.F0 z,E₀.J+z*(E₁.J-E₀.J), E₀.τ, point z p f⟩ else E₀
include f
lemma start : f.curve 0 = E₀:=by rw [curve,dif_pos (by rw [norm_zero]; exact zero_lt_one.trans f.wide)]; apply Lobby.ext<;> simp [stream]
lemma last : f.curve 1 = E₁:=by rw [curve,dif_pos (by rw [norm_one]; exact f.wide)]; apply Lobby.ext<;> simp [stream]
-- satisfy hol reach
lemma enter (v:ℂ)(t:v∈ank (Lrad O D)):(f.curve v).F0=stream E₀.F0 E₁.F0 v:=by rw [curve,dif_pos (by simpa only [DPress.Analytic.ank,mem_ball, dist_zero_right] using t)]
lemma reach : Reach (Lrad O D) f.curve :=by
 constructor
 · intro i U'; have he {z:ℂ}(t:z∈ank (Lrad O D)): (curve f z).F0.1 i U'=E₀.F0.1 i U'+z • (E₁.F0-E₀.F0).1 i U':=by rw [enter f z t]; rfl
   apply DifferentiableOn.congr _ (fun z t=> he t); exact (differentiableOn_const _).add (differentiableOn_id.smul_const _)
 intro i U'; have he {z:ℂ}(t:z∈ank (Lrad O D)): (curve f z).F0.2 i U'=E₀.F0.2 i U'+z • (E₁.F0-E₀.F0).2 i U':=by rw [enter f z t]; rfl
 apply DifferentiableOn.congr _ (fun z t=> he t); exact (differentiableOn_const _).add (differentiableOn_id.smul_const _)
omit f
def splitS(f:Lapse E₀ E₁ D) : Lobby Q O β:= ⟨_,0,E₀.τ,f.pay.more C.uB (by linarith [f.budget,f.money])⟩
lemma sect(f:Lapse E₀ E₁ D)(u:HonestL E₀)(v:HonestL E₁): HonestL f.splitS:= v.sub u
end Lapse
end YM.CF.Py.Kay
