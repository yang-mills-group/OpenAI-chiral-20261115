import YM.SU5.Interaction.Kerosene.Packing
import YM.SU5.Interaction.Draught.Heater
import YM.SU5.Interaction.Reg.Earnings
import YM.SU5.Interaction.Reg.Brim
import YM.CF.Vp929.Stage.Sole
import YM.CF.Roots.Cane

/-! Uniform rate strengthening usable through the regulator comparison at (124). Choose costs post geometry. -/
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
open Roots Wray Py Ione

-- Q and w_0 of (124)
open Lor Push.AbsoluteSums.Animals Vow Stax Cadre Sour
variable (L:Patch)
local notation "ρ" => L.L
variable (C H F:ℝ→ℝ)
local notation "Ĉ" k:max=> Chill_v k
local notation "b_" k:max=> (radiusB k:ℝ)
def runway (x:ℝ):ℝ:= (radiusB x:ℝ)⁻¹
def Quench (L:Patch)(X:ℝ→ℝ):Prop:= Chill_v (fun x=> X x / (Scales.g SU.group L.L x)^2)
namespace Quench
variable {L C H F}
lemma illum_Q (v:Quench L C):Chill_v C := by
 have hx:Chill_v (allotΨ L.L) := Chill_v.coin (Q:=L) ((size_ψ _).low (by omega)); apply (Chill_v.leanB (E:=fun x=> C x / (allotΨ L.L x)) v (hx.pane)).trend; filter_upwards [(Scales.year SU.group L.L).eventually_gt_atTop 0] with x t; have hp:0 < allotΨ L.L x:=pow_pos (Scales.gauge _ _ t) _; refine Eq.le (congrArg abs ?_); have ht:= Scales.gauge SU.group L.L t; field_simp
lemma normF (v:Quench L C): Quench L (fun i=> |C i|):= Chill_v.trend v (Eventually.of_forall fun i=>by rw [abs_div,abs_div,abs_abs])
lemma addL (p:Quench L C)(q:Quench L H):Quench L fun x=>C x+H x:=by unfold Quench; simp_rw [add_div]; exact Chill_v.noteR p q
lemma manyF (p:Quench L C) (x:ℝ): Quench L fun i=>x*C i:=by unfold Quench; simp_rw [mul_div_assoc]; exact Chill_v.cheap p x
lemma bondF (p:Quench L C) (x:BoreP H):Quench L fun i=>H i*C i:=by unfold Quench; simp_rw [mul_div_assoc]; exact Chill_v.leanB p x
lemma cheaper (p:Quench L H)(v:∀ᶠ x in atTop,|C x| ≤ |H x|): Quench L C:=by apply Chill_v.trend p; filter_upwards [v] with x h; rw [abs_div,abs_div]; exact div_le_div_of_nonneg_right h (abs_nonneg _)
end Quench
lemma span_bore : BoreP fun x=> Sour.spanV (radiusB x) := by unfold Sour.spanV; push_cast; exact ((BoreP.radius_c.join BoreP.radius_c).join (BoreP.still 1)).self _
lemma deg_chill (p:Chill_v C):Ĉ (fun x=> degreePrice (radiusB x) (C x) (runway x)) := by
 unfold degreePrice Trees.stretch ballCost; push_cast; unfold runway
 have he:= (((p.leanB span_bore).leanB BoreP.radius_c).cheap 4); refine he.trend (Eventually.of_forall fun i => ?_); apply Eq.le; congr 1; unfold Sour.spanV; push_cast; rw [div_eq_mul_inv,inv_inv]; ring
noncomputable abbrev dollarT (k:ℕ)(δ:ℝ)(X:ℝ):ℝ:= X*(degreePrice k X δ)^0*(1-degreePrice k X δ)⁻¹
lemma dollar_Q (p:Quench L C) : Quench L (fun i=> dollarT (radiusB i) (runway i) (C i)) := by
 let G(i):=(1-degreePrice (radiusB i) (C i) (runway i))⁻¹; have he:Tendsto G atTop (𝓝 1):= by
    unfold G; let H:= (deg_chill _ p.illum_Q).spine_a; simpa only [sub_zero,inv_one] using ((tendsto_const_nhds (x:=(1:ℝ))).sub H |>.inv₀ (show (1:ℝ)-0≠0 by norm_num))
 have hp:BoreP G:= (BoreP.still 2).tune ((he.abs).eventually (ge_mem_nhds (by norm_num : |(1:ℝ)| < |(2:ℝ)|)))
 exact (p.bondF hp).cheaper (Eventually.of_forall fun i=>by unfold dollarT G; rw [pow_zero,mul_one,mul_comm (C i)])
lemma reserve_bond (i n:ℕ) : BoreP fun x=> reserveT i n (radiusB x) (runway x):=by
 have h:=(((BoreP.still 5).grip (BoreP.radius_c.join (BoreP.still 1))).self i)
 have hp:BoreP fun x=> coin_n i n (radiusB x):=by unfold coin_n stilK; exact h.grip ((BoreP.still _).grip (((BoreP.still _).grip h).self _))
 have he:BoreP fun x=>Real.exp (runway x):=(BoreP.still (Real.exp 1)).tune (by
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x t; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; exact inv_le_one_of_one_le₀ (by exact_mod_cast t))
 unfold reserveT runway; simp_rw [inv_inv]; exact hp.grip (((BoreP.radius_c.self _).grip (BoreP.still _)).grip he)
-- `c` full C payment cool, F Body (K.Phi initially paid) & H Birth cool*Q. store packing sales
structure WinterFuel (L:Patch)(C H F: ℝ→ℝ) (Γ Γ':ℝ→ℝ): Prop where
  ζ : Quench L Γ
  ζp : Quench L Γ'
  live : ∀ᶠ x:ℝ in atTop, let δ:=runway x ; let s:= Sour.spanV (radiusB x); let c_:= |C x|; let y:=H x; let V:=F x;
    0<δ∧ δ ≤ 1/5 ∧ 0 < Γ x ∧ 0< Γ' x ∧ s*c_≤ δ ∧ s*Γ x ≤ δ ∧ V+y+ Γ x*(δ⁻¹*s)* c_ ≤ Γ x ∧
    dollarT (radiusB x) δ (Γ x) ≤1 ∧ degreePrice (radiusB x) (Γ x) δ <1 ∧ degreePrice (radiusB x) (Γ' x) δ <1 ∧ Γ x+Real.exp 1*dollarT (radiusB x) δ (Γ x) ≤ Γ' x
lemma purchaseWinter (p:Chill_v C) (q:Quench L H)(f: Quench L F) : ∃ Γ Γ':ℝ→ℝ, WinterFuel L C H F Γ Γ':=by
 let i(x:ℝ):ℝ:= F x; let S':=allotΨ L.L; let z(x):=(S' x)^2; have hx:Quench L z := by
    have ht:Chill_v (allotΨ L.L):= Chill_v.coin (Q:=L) ((size_ψ _).low (by omega)); exact ht.trend (Eventually.of_forall fun i=> by unfold z S' allotΨ; generalize (Scales.g SU.group L.L i)^2=c; by_cases h:c=0; simp [h]; rw [pow_two,mul_self_div_self])
 let g(x):= (|F x|+|H x|+ z x); let Γ(x):=(4:ℝ)*g x; have hg:Quench L Γ:=(((f.normF).addL (q.normF)).addL hx).manyF _
 let Γ'(x):=Γ x+Real.exp 1*|dollarT (radiusB x) (runway x) (Γ x)|; have hu:Quench L Γ':=hg.addL (((dollar_Q L _ hg).normF).manyF _)
 let Flavor:= fun x=> Sour.spanV (radiusB x)
 have h(x:ℝ):0 ≤ runway x:=by unfold runway; positivity
 have l:= hg.illum_Q; have hP:Chill_v (fun x=>|C x|):= p.trend (Eventually.of_forall fun x=>by rw [abs_abs]); have hC(t):0 ≤ Flavor t:=by unfold Flavor Sour.spanV; positivity
 refine ⟨Γ,Γ',hg,hu,?_⟩; filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 5,(Scales.year SU.group L.L).eventually_gt_atTop 0,(((l.leanB span_bore).leanB BoreP.radius_c).spine_a).eventually (ge_mem_nhds zero_lt_one), (((hP.leanB span_bore).leanB BoreP.radius_c).spine_a).eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)),(deg_chill _ l).spine_a.eventually (Iio_mem_nhds zero_lt_one),(deg_chill _ (hu.illum_Q)).spine_a.eventually (Iio_mem_nhds zero_lt_one),(dollar_Q L _ hg).illum_Q.spine_a.eventually (ge_mem_nhds zero_lt_one)] with x b pV cQ u hF hG w
 let B:=(radiusB x:ℝ); have ht:0 < B:=by unfold B; have h:0 < radiusB x:=(by omega); positivity
 have hγ:0< Γ x:=by have hz:0< S' x:= pow_pos (Scales.gauge _ _ pV) _; unfold Γ g z; positivity
 change B* (Flavor x * Γ x) ≤ _ at cQ; change B*(Flavor x*|C x|) ≤ _ at u; change 0 < B⁻¹∧ B⁻¹ ≤ _ ∧ _<_ ∧ _<_ ∧ Flavor x* |C x|≤ B⁻¹ ∧ Flavor x* Γ x≤B⁻¹∧ _+Γ x*( (B⁻¹)⁻¹ * Flavor x)* |C x| ≤ Γ x ∧ _
 rw [inv_inv]; refine ⟨by positivity, show B⁻¹≤_ from ((by rw [one_div]; exact inv_anti₀ (by norm_num) (by change 5 ≤ (radiusB x:ℝ); exact_mod_cast b))), hγ, by unfold Γ'; positivity, (le_inv_mul_iff₀ ht).mpr (by linarith) |>.trans_eq (mul_one _), ((le_inv_mul_iff₀ ht).mpr cQ).trans_eq (mul_one _),?_,w,hF,hG,?_⟩ -- replace
 · have hr:= mul_le_mul_of_nonneg_left u hγ.le; have hv: F x+H x≤ Γ x/4:=(le_trans (add_le_add (le_abs_self _) (le_abs_self _)) (le_trans (le_add_of_nonneg_right (sq_nonneg (S' x))) (by unfold Γ g z; linarith))); nlinarith only [hr,hv,hγ]
 unfold Γ'; exact add_le_add_right (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le) _
end BScale
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.BScale.purchaseWinter
