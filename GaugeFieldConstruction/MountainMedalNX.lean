import GaugeFieldConstruction.MeanSoulNX
import GaugeFieldConstruction.SummonOroNX
-- preselection version. computes stock at narrowing scales without new basis.J
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
variable {P:Spine}(i:Axis){A:P.Glaze}{a b l r v e:ℝ}{y z:ℂ}
lemma hearthSumNX(P:Spine)(i:Axis){a b:ℝ}(h:0≤a)(u:0≤b) :P.hearthNX i a * P.hearthNX i b=P.hearthNX i (a+b):=Subtype.ext ((P.publicH i).Time.wax_sq h u)
lemma hearthBudgetNX(P:Spine)(i:Axis)(a:ℝ) : ‖P.hearthNX i a‖ ≤1:= (P.publicH i).Time.wax_pay a
lemma grantStretchNX (s d:ℕ)(F:P.Test)(u:P.tock s d≤a)(p:P.tock s d≤b)(t:a≤l)(q:b≤r): P.grantGapNX i s d F l r=P.hearthNX i (l-a) * P.grantGapNX i s d F a b * P.hearthNX i (r-b):=by
   unfold grantGapNX; conv_rhs=>rw[←mul_assoc _ _ (hearthNX _ i _),←mul_assoc,hearthSumNX _ _ (sub_nonneg.mpr t) (sub_nonneg.mpr u),mul_assoc _ (hearthNX _ i _) _,hearthSumNX _ _ (sub_nonneg.mpr p) (sub_nonneg.mpr q)]
   rw [sub_add_sub_cancel,add_comm (b-_),sub_add_sub_cancel]
lemma civicUnitNX (d:ℕ)(u:0<d)(s:ℕ)(hp:P.tock s d≤a)(hv:P.tock s d≤b):P.grantGapNX i s d 1 a b=P.hearthNX i (a+b):=by
   unfold grantGapNX corneaNX; rw[map_one,HabBox_one s P i (by omega)]
   let X:=P.tock s d
   have hx:0≤X:=P.tock_nonneg _ _
   rw [show (P.Eucl i _)=hearthNX P i (X+X) from (by unfold X; congr; rw [←P.tock_add,←Nat.cast_add,P.tock_when,Real.toNNReal_coe])] -- tune
   rw[P.hearthSumNX _ (sub_nonneg.mpr hp) (by positivity),P.hearthSumNX _ (by positivity) (sub_nonneg.mpr hv)]
   congr 1; unfold X; ring
lemma civicPlusNX (d s:ℕ){F G:P.Test}(p:P.BEntry i (d+d) (P.shifts i d F))(q:P.BEntry i (d+d) (P.shifts i d G))(a b:ℝ):P.grantGapNX i s d (F+G) a b=P.grantGapNX i s d F a b+P.grantGapNX i s d G a b:=by
   unfold grantGapNX corneaNX; rw[map_add,HabBox_add s p q,mul_add,add_mul]
lemma civicSharesNX (d s:ℕ){F:P.Test}(p:P.BEntry i (d+d) (P.shifts i d F))(a b:ℝ)(z:ℂ):P.grantGapNX i s d (z•F) a b=z•P.grantGapNX i s d F a b:=by
   unfold grantGapNX corneaNX; rw [map_smul,HabBox_smul s p,mul_smul_comm,smul_mul_assoc]
lemma civicClearNX (p:P.Taste A.F A.S y)(ha:0<v)(t:0<e):∀ᶠ s in atTop,P.tock s A.w≤ v ∧ ∀ l≥v,∀ r≥v,‖P.grantGapNX i s A.w A.F l r-y•P.hearthNX i (l+r)‖ ≤ e:=by
 let d:=A.w
 filter_upwards [P.tock_small A.w ha,collectFourNX i p ha (by positivity: 0<e/8)] with s v₀ u
 refine ⟨v₀,?_⟩
 intro l v r p
 let T:= A.soot y
 have h':P.BEntry i (A.w+A.w) (P.shifts i d 1):=by rw[map_one]; exact BEntry.one _ _ (add_pos A.pos A.pos)
 have he : ‖P.grantGapNX i s d T.F l r‖ ≤ e:=by
   rw [grantStretchNX i s d T.F v₀ v₀ v p]
   exact (norm_mul_le ..).trans ((mul_le_mul (le_trans (norm_mul_le ..) (mul_le_mul (P.hearthBudgetNX ..) (u.trans_eq (by ring)) (norm_nonneg _) zero_le_one)) (P.hearthBudgetNX ..) (norm_nonneg _) (by positivity)).trans_eq (by ring))
 change ‖P.grantGapNX i s A.w (A.F+(-y)•1) l r‖ ≤ _ at he
 have un:P.BEntry i (d+d) (P.shifts i d ((-y)•(1:P.Test))):=by rw[map_smul]; exact h'.smul _
 rw [civicPlusNX i d s (A.centers i) un,civicSharesNX i d s h', civicUnitNX i _ A.pos _ (v₀.trans v) (v₀.trans p), neg_smul] at he
 simpa only [sub_eq_add_neg] using he
variable {Z:Lead.Clan}(M:P.Medal Z)
lemma oreCrossNX (p:0<v)(q:0<e)(i:Axis):∀ᶠ s in atTop, P.tock s M.bright.w ≤v ∧ ∀ l≥v,∀ r≥v,‖P.grantGapNX i s M.bright.w M.bright.F l r- P.hearthNX i (l+r)‖≤e:=by
 let κ:=M.y
 let c:=‖κ⁻¹‖; have hp:0<c:= norm_pos_iff.mpr (inv_ne_zero M.nonzero)
 filter_upwards [civicClearNX i (A:=M.cross) M.worth p (div_pos q hp)] with s u
 refine ⟨u.1,fun l v r y=>?_⟩
 have hx : ‖κ⁻¹‖ * ‖P.grantGapNX i s M.cross.w M.cross.F l r-κ • P.hearthNX i (l+r)‖≤e:= (le_div_iff₀' hp).mp (u.2 l v r y)
 rw [←norm_smul, smul_sub,smul_smul,inv_mul_cancel₀ M.nonzero,one_smul,← civicSharesNX i _ s (M.cross.centers i)] at hx
 exact hx
variable {M':P.Menagerie}{n:ℕ}
lemma heavenlyCoinNX (p: P.Company n M' a)(Z:Lead.Clan){v e:ℝ}(h:0<v)(w:0<e):∀ᶠ s in atTop, ∀i:Axis,
   let Y:=P.thinString Z s n
   let X:=Y.u i
   P.tock s X≤v∧∀ l≥v,∀ r≥v, ‖P.grantGapNX i s X Y.F l r-P.electro M' Z•P.hearthNX i (l+r)‖≤e:=by
   let q:= P.electro M' Z
   have hg:0<‖q‖:= norm_pos_iff.mpr (electro_alive _ _)
   refine eventually_all.mpr ?_; intro i
   let K:=(M' Z).bright
   have ht: q•K.F=P.frontMat Z n:=by unfold q K; rw [electro_front,p.clock Z]
   have he:P.BEntry i (K.w+K.w) (P.shifts i K.w (q•K.F)):=by rw [map_smul]; exact (K.centers i).smul _
   let X:=P.probeClock n i
   filter_upwards [oreCrossNX (M' Z) h (div_pos w hg) i,P.tock_small X h] with s u U
   refine ⟨U,?_⟩; intro l v r y
   -- noop
   have hu : ‖q‖ * ‖P.grantGapNX i s K.w K.F l r- P.hearthNX i (l+r)‖ ≤ e:= (le_div_iff₀' hg).mp (u.2 l v r y)
   rw[←norm_smul,smul_sub,← civicSharesNX i _ s (K.centers i),ht] at hu
   change ‖P.grantGapNX i s X (P.frontMat Z n) l r - q • _‖≤ _
   rw [grantLargeNX i s X K.w (P.frontMat Z n) (Apron.admit (P.thinString Z s n) i) (ht ▸ he) (U.trans v) (U.trans y) (u.1.trans v) (u.1.trans y)]; exact hu
#print axioms heavenlyCoinNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
