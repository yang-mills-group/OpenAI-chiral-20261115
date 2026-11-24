import YM.CF.Bloom.Screen
import YM.CF.Bloom.Apse
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Ione Salt
set_option maxHeartbeats 500000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(J:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
abbrev Shift_t (n:ℕ)(w:ℝ):ℝ:= n*w
variable (Y:ℕ)(hδ:0 < x)(hX:8*W.z ≤ x)(hp:Y≤ l0)(hM:(l0:ℝ) ≤ x*(plow x)^J)
include D hδ hX hp
lemma narrow_β : let t:= hat R.L x Y; (3/4:ℝ)*t ≤ B0 Y∧ B0 Y ≤ (3/2:ℝ)*t:=by
 intro t; let Z:=W.arm (T.large.trans ht) l0; have he:= W.pose (T.large.trans ht) l0
 have hk: Z.Running B0:= by intro i p; rw [D.fee i p]; change |B0 _+Z.move i-(B0 _+Z.move i)|≤_; simp
 obtain ⟨r,R'⟩:=V.roomZ; have hx:=Vale.spark hk he 0 Y (by omega); rw [Nat.zero_add,D.unit,abs_le] at hx; let u:=billX R.L; unfold t hat; have hh: (0:ℝ)≤ Y:=Nat.cast_nonneg _
 constructor <;> nlinarith only [mul_nonneg hh (pitch R.L),hx.1,hx.2,hδ,hX,mul_le_mul_of_nonneg_left r hh, mul_le_mul_of_nonneg_left R' hh] -- tune abs
include hM
lemma bond_β(q:ℝ) (h: |q-B0 Y| ≤ (l0-Y:ℕ) *rendK J x):matchedX (hat R.L x Y) q:=by
 let t:=hat R.L x Y; let e:=rendK J x; have he := lt_of_lt_of_le zero_lt_one (Scales.size x); have ht0:0< e:=by unfold e rendK; change 0<(1/16:ℝ)/_; apply div_pos; norm_num; exact pow_pos (show 0 < Esti.plow x from he) _
 have hy: ((l0-Y:ℕ):ℝ) *e ≤ x/16:=by
    have h_: ((l0-Y:ℕ):ℝ)≤ l0:=Nat.cast_le.mpr (by omega); refine (mul_le_mul_of_nonneg_right (h_.trans hM) ht0.le).trans_eq ?_; unfold e rendK; change 0<plow x at he; field_simp -- pow pos
 have hz : q-B0 Y ≤ x/16 ∧ - (x/16) ≤ q-B0 Y:= ⟨(le_abs_self _).trans (h.trans hy), (neg_le_neg (h.trans hy)).trans (neg_abs_le _)⟩
 obtain ⟨u,v⟩:=narrow_β V a p i N0 T M ht l0 B0 D Y hδ hX hp -- replace ht
 have h':x≤t:=crown ..
 unfold matchedX; change t/2 ≤ _∧ _ ≤ 2*t; change (3/4:ℝ)*t≤ _ at u; change _ ≤ (3/2:ℝ)*t at v; constructor<;>linarith only [h',hz.1,hz.2,u,v,hδ]
omit hM D hp hδ hX
local notation "H_F"=> hueR V a p i N0 T M ht l0 B0
abbrev pay_K (Q:GramM P)(y:ℝ) : GramM P:={Q with beta:=y}
structure CloseC{N:Side}(Q P:GramM N):Prop where
 width:Q.p=P.p
 path:Q.path=P.path
 taste:Q.J=P.J
 fund:Q.funds=P.funds
include T D
lemma sized_F (U':GramM (cell M B R.L (Y+1)))(v: CloseC (H_F (Y+1)) U')(q:Y<l0)(w:matchedX (hat R.L x (Y+1)) U'.beta) : StatV V (apt M B R.L Y) (V.L.mint (l0-1-Y) (kint M B R.L Y)) U W (pay_K (H_F Y) (U'.beta+(B0 Y-B0 (Y+1)))) U' (V.L.charge (l0-1-Y)) ((W.arm (T.large.trans ht) l0).shift Y) a (hat R.L x Y) p i:=by
 let Dc:= W.arm (T.large.trans ht) l0; have hp: Costume (H_F (Y+1)) (H_F (Y+1)):=⟨0,0,0,rfl⟩
 have he:= sized_s V a p i N0 T M ht l0 B0 D Y (H_F (Y+1)) hp q; rw [hat_succ] at w
 have hx: B0 Y - B0 (Y+1)= V.L.charge (l0-1-Y)+Dc.shift Y:=by rw [D.fee Y q]; change _+Dc.move _- _= Dc.move _; abel
 exact ⟨he.hunt, v.width ▸ he.down,v.taste ▸ he.dose,v.taste ▸ he.sound,he.foot,he.bill,v.width ▸ he.cult,he.care,v.path ▸ he.move,he.coinX,v.fund ▸ he.coinY, congrArg _ hx,w, he.fee,v.width ▸ he.fee',v.width ▸ he.year⟩ -- congrArg _
variable {Q': GramM (mid N B)}
end YM.CF.Py
