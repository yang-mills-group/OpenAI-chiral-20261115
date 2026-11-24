import YM.CF.BProof.Hill.Knee
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
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}
-- Bough spine geometry keeps Hue, lifts genuine fields. h rt fixed at hq; no size when comparing l0 theta step. Spans Estimate. Need access S.ρ uniforms.
open Bake PushA Episode Salt
variable {m:Side}{hx N0 n:ℕ}{T': Month x a order power N0 V W}
namespace Realm
variable (P:Realm V T' m n)
local notation "νγ"=>hat R.L x
abbrev γT(R:Patch):ℝ:=Vale.billX R.L/16
-- distinguish coherence benchmark from Billing.Track. indexes
include P
lemma γReal:0 < γT R:=by have h:=billx_T V; unfold γT; unfold ν_PS at h; linarith
lemma γGauge (p:0<x) (j:ℕ): (j:ℝ)* γT R ≤ νγ j/16:= by unfold γT hat; linarith
lemma mono_x{i j:ℕ}(v:i ≤ j): hat R.L x i ≤ hat R.L x j:=by unfold hat; have hp:= pitch R.L; gcongr
lemma pose_a (p:0<x)(u:8*W.z ≤ x){i:ℕ}(v:i ≤ n){β:ℝ}(h:|β-P.β i|≤ νγ i/8): matchedX (νγ i) β:=by
 obtain ⟨a,b⟩:=P.bounds_ref p u i v; let t:= νγ i; have z:0 < t:= lt_of_lt_of_le p (crown ..); change 0 < νγ i at z; rw [abs_le] at h; exact ⟨by linarith only [h.1,a,z],by linarith only [h.2,b,z]⟩
omit P
structure Threshold (R:Patch)(x:ℝ)(Lm:ℕ) : Prop where
 warm:0<x
 may (i:ℕ): (Lm:ℝ)*Real.sqrt (hat R.L x i) ≤ hat R.L x i/16 -- application uses LM=span b+1
lemma bounds(R:Patch)(Lm:ℕ):∀ᶠ x in atTop,Threshold R x Lm:=by
 filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (((Lm:ℝ)*16)^2)] with x p v; refine ⟨p,fun i=>?_⟩
 let t:= hat R.L x i; have u:= lt_of_lt_of_le p (crown R.L x i); have yu:0≤ t:=u.le; have he:(Lm:ℝ)*16 ≤Real.sqrt t:= (Real.le_sqrt (by positivity) yu).mpr (v.trans (crown ..)); change _ * Real.sqrt t ≤ t/_; have hv:=mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg t); nlinarith only [Real.sq_sqrt yu,hv]
include P
namespace Day
variable (z:StarPS n){i j k l:ℕ}
def ruler (P:Realm V T' m n): Air n 0:=⟨fun _=>γT R,P.β,0,fun _=>1,fun _=>P.γReal,fun _=>zero_lt_one⟩
lemma βapprox (t:0<x):|(ruler P).aim z i-P.β i|≤ νγ i/16:=by
 have he: |(ruler P).aim z i-P.β i-(0:ℝ)| ≤ (i-0:ℕ)*γT R:= (ruler P).deposit i (Nat.zero_le _) _ z fun _ _ _=>le_rfl; rw [sub_zero,Nat.sub_zero] at he; exact he.trans (P.γGauge t i)
lemma βcheck (p:0<x)(u:8*W.z≤x)(t:i ≤ n):matchedX (hat R.L x i) ((ruler P).aim z i):=by
 have he:=lt_of_lt_of_le p (crown R.L x i); exact P.pose_a p u t ((βapprox P z p).trans (by linarith))
variable (η:Threshold R x l)(v:8*W.z≤x)(c:ℝ)(L0:ℕ→ℝ)(h:∀ i,0<L0 i)
include η
lemma chg_pos (j:ℕ):0 <grant_B R.L (νγ j):= by apply Real.sqrt_pos.mpr; change 0< betaF SU.group (hat R.L x j) R.L; rw [←hat_succ]; exact lt_of_lt_of_le η.warm (crown ..)
-- aux suffix [i,n). χ guesses and top beta; c=true beta_i. grant_B positive.
def clipDay(i:ℕ):Air n i:= ⟨fun j=> grant_B R.L (hat R.L x j),P.β,c-P.β i,L0,chg_pos P η,h⟩
local notation "χκ"=> (clipDay P η c L0 h i)
include η v
lemma stable (t:i+l=n)(u:i ≤ j)(y:j ≤ n)(p:|c-P.β i|≤ νγ i/16): matchedX (hat R.L x j) ((clipDay P η c L0 h i).aim z j):=by
 let V:=Real.sqrt (νγ j); have hx(d:ℕ)(s:d<j):grant_B R.L (hat R.L x d) ≤ V:= Real.sqrt_le_sqrt (le_trans (le_of_eq ((hat_succ _ _ _).symm : betaF _ _ _= _)) (P.mono_x (show d+1 ≤ j from s)))
 have he:0 ≤ V:= Real.sqrt_nonneg _; have hh: |(χκ).aim z j - P.β j -(c-P.β i)|≤(j-i:ℕ)* V:= Air.deposit (χκ) j u _ z (fun j _ y=>hx j y)
 let Z:=η.may j; have hm: |(χκ).aim z j-P.β j-(c-P.β i)|≤νγ j/16:= hh.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show j-i≤ l from by omega)) he).trans Z); have h_v:=P.mono_x u; rw [abs_le] at hm p; apply P.pose_a η.warm v y; rw [abs_le]; exact ⟨by linarith only [hm.1,p.1,h_v],by linarith only [hm.2,p.2,h_v]⟩
end Day
end Realm
end Cupboard
end YM.CF.Py
