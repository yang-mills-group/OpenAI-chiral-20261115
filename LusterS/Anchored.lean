import LusterS.Bruin
import YM.SU5.Gleam.Stow
import Refrain.Shrift
import Refrain.Kernel
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Almanac
open clocks
-- existence block multiple
lemma powers_cover {a b:ℕ}{L:Side}(h:0<b)(l:1<L.val)(p:b≤L.val^a):∃ i≤a,b≤ L.val^i ∧ L.val^i≤ L.val*b:=by
 induction a with
 | zero=> exact ⟨0,le_rfl,p, (by simp only [pow_zero]; exact Nat.mul_pos (by omega) h)⟩
 | succ a ih=>
    by_cases hz:b≤ L.val^a
    · obtain ⟨i,p,h,v⟩:=ih hz; exact ⟨i,by omega,h,v⟩
    exact ⟨a+1,le_rfl,p,(pow_succ' ..).trans_le (Nat.mul_le_mul_left _ (le_of_not_ge hz))⟩
end Almanac
end YM.Gleam.Luster
namespace YM.CF.Py.Rate.LocalLimit
open YM.Gleam.Luster.Almanac
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
open Preparation
lemma high_physical (P:Preparation) : ∀ᶠ s:ℕ in atTop, 8* walls P.R.L (Vale.hat P.R.L P.x s) ≤ P.R.L.val^ s:=by
 let L:=P.R.L; let a:ℝ:= L.val; have ha:a>1:=by unfold a; exact_mod_cast (show 1<L.val from le_trans (by decide) P.V.tallX)
 let K(s:ℕ):= Vale.hat P.R.L P.x s
 have ht:Tendsto (fun i:ℕ=> (8:ℝ)*K i/a^i) atTop (𝓝 0):=by
    let Y:=Vale.billX L; let v:=P.x; have hn:= tendsto_pow_const_div_const_pow_of_one_lt 1 ha
    have hf:= (tendsto_const_nhds (x:=v)).div_atTop (tendsto_pow_atTop_atTop_of_one_lt ha)
    have hk:= (hf.add (hn.mul_const Y)).const_mul 8
    simp only [mul_zero,add_zero,zero_mul] at hk; apply hk.congr; intro i; change 8*(P.x/a^i+((i:ℝ)^1/a^i)*Y)= _; unfold K hat Y L; ring
 filter_upwards [(stage_slope P.V P.x).eventually ((walls_b L).cost_p (b:=1) (by norm_num [tauA])), ht.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with i h hp
 change 8*K i/a^i≤ 1 at hp; rw [div_le_one (pow_pos (zero_lt_one.trans ha) _)] at hp
 change |(walls L (Vale.hat P.R.L P.x i):ℝ)| ≤ ( (Vale.hat P.R.L P.x i):ℝ)^(1:ℝ) at h; rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _),Real.rpow_one] at h
 change 8 * walls L (Vale.hat P.R.L P.x i) ≤ _
 have he:(8:ℝ)*(walls L (Vale.hat P.R.L P.x i))≤ a^i:=by linarith only [h,hp]
 unfold a L at he; change 8*(walls L (Vale.hat P.R.L P.x i))≤ P.R.L.val^i; exact_mod_cast he
lemma block_widths (P:Preparation): ∀ᶠ s in atTop,∀ m:Side,let N:=More (P.Ctor m s); ∃ W:Side, Odd W.val ∧ cliffs (Vale.hat P.R.L P.x s)≤ W.val ∧ W.val ≤ walls P.R.L (Vale.hat P.R.L P.x s) ∧ ∃ c:Side,∃ R': Ratio c N, 2*(R'.count.val+1)< N.val ∧ R'.count=W :=by
 let L:=P.R.L; have ht:1<L.val:=by unfold L; have h:=P.V.tallX; omega
 filter_upwards [high_physical P, (stage_slope P.V P.x).eventually (cliffs_loft.eventually_ge_atTop 1)] with s u v m N
 let x:=Vale.hat P.R.L P.x s; let b:=cliffs x
 have he0:0<b:=v
 have hl: b≤ walls L x:=Nat.le_mul_of_pos_left _ L.property
 obtain ⟨i,p,g,w⟩:= powers_cover he0 ht -- order? hb ht
   -- do
   (p:= (hl.trans ((Nat.le_mul_of_pos_left _ (by decide: (0:ℕ)<8)).trans u)))
 let W:=L^i; have he:W.val=L.val^i:=rfl
 let c:= More (P.Ctor m (s-i)); have H: N=c*W:=by
    unfold c N W Ctor cell Vale.mesh CSide Cube.More; simp only [L]; rw [show P.R.L^s=P.R.L^(s-i)*P.R.L^i by rw [←pow_add,Nat.sub_add_cancel p]]; ac_rfl
 let Q: Ratio c N:=⟨W, congrArg Subtype.val H⟩
 refine ⟨W, (by rw [he]; exact Odd.pow P.R.odd_side), g,w, c,Q,?_,rfl⟩
 change 2*(L.val^i+1)< N.val; apply lt_of_lt_of_le _ (show L.val^s≤N.val from (by let D:=Vale.mesh m L s; have h:L.val^s≤ D.val:=Nat.le_mul_of_pos_left _ m.property; change _ ≤ D.val*2 * P.block.val *2; exact h.trans (((Nat.le_mul_of_pos_right D.val two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)).trans (Nat.le_mul_of_pos_right _ two_pos))))
 change L.val^i ≤ walls L x at w; have hp:1 ≤ L.val^i:=one_le_pow₀ ht.le; change 8*walls L x ≤ L.val^s at u; omega
end YM.CF.Py.Rate.LocalLimit
