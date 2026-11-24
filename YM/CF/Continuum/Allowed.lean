import YM.CF.Py.Never
import YM.CF.Continuum.Boarded
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Period
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
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
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
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
open CF.Window
open Graph
-- labeled envelope cost, frame geometry first
variable {M : Side}
local notation "Bₓ" v=> cell (v*N') B R.L 0
local notation "seat″" x=> (seat_u V J x N0)

abbrev Allowed (x:ℝ)(M:Side):Prop:= (seat_u V J x N0).val ≤ M.val ∧ (((cell (M*N') B R.L 0).val):ℝ) ≤ maxTest x
lemma allowedSupport (t:Allowed V N0 J x M): (seat_u V J x N0*N').val ≤ (M*N').val∧ (cell (seat_u V J x N0*N') B R.L j).val ≤ (cell (M*N') B R.L j).val:=by
 have he: (seat_u V J x N0*N').val ≤ (M*N').val:=Nat.mul_le_mul_right _ t.1; refine ⟨he,?_⟩; change ((seat″ x)*N').val*_ *2* _ ≤ (M*N').val*_*2*_; gcongr

lemma by_series {α:ℕ→ℝ}{F:ℕ→Side}(t:Tendsto α atTop atTop)(he:∀ i,Allowed (B:=B) V N0 J (α i) (F i)): AdmittedSeries α (eur (fun i=> Bₓ (F i))):= by
  have ht:= front V N0 J t; apply admit_via_ceiling t (tendsto_atTop_mono (f:=eur (fun i=> Bₓ (seat″ (α i)))) ?_ ht.2.2) (C:=1) one_pos (Eventually.of_forall fun p=>?_)
  swap; · rw [one_mul]; exact (he _).2
  exact fun i=>Nat.cast_le.mpr (allowedSupport V N0 J (he i)).2

lemma ribbon (M:Side) : (((cell (M*N') B R.L 0).val):ℝ)=(M.val:ℝ)*(N'.val*2*B.val:ℝ):=by
 unfold cell; rw [show Vale.mesh (M*N') R.L 0=M*N' by simp [Vale.mesh]] -- def cell
 change (( (M.val * N'.val * 2 * B.val:ℕ) ):ℝ)=_; push_cast; ring
lemma logAllows {f:ℕ→ Side}{x:ℕ→ℝ}(t:Tendsto x atTop atTop)(he:∀ i, Allowed V N0 J (x i) (f i)): ∀ᶠ i in atTop,|Real.log (soaked (x i))|≤ massMeter (cell (f i*N') B R.L 0):=by
  filter_upwards [t.eventually_ge_atTop 1,(Real.tendsto_log_atTop.comp t).eventually_ge_atTop 1] with i u hx; let j₀:=f i; let M:=seat″ (x i); let Q₀:= Bₓ j₀; have he':radiusB (x i) ≤ M.val:=by
    unfold M seat_u grainZ; have h: radiusB (x i) ≤ (100+N0)*(1+radiusB (x i)):= le_trans (Nat.le_add_left ..) (Nat.le_mul_of_pos_left _ (by omega)); change _ ≤ J.h+(W.n+ (100+N0)*(1+radiusB (x i)))+1; omega -- n fold
  have hv: Real.log (x i)^2 ≤ (Q₀.val:ℝ):=le_trans (Nat.le_ceil _) (Nat.cast_le.mpr ((he'.trans (he i).1).trans (le_trans (Nat.le_mul_of_pos_right _ N'.property) (amplit (f i*N') B R.L 0))))
  change 1 ≤ Real.log (x i) at hx; unfold soaked; rw [Real.log_inv,Real.log_sqrt (by linarith),abs_neg,abs_of_nonneg (by linarith)]; let v:= massMeter Q₀; have h:0<(Q₀.val:ℝ):=by positivity
  have z:=matter_meter Q₀; nlinarith [pow_le_pow_right₀ (a:=(Q₀.val:ℝ)) (Nat.one_le_cast.mpr Q₀.property) (show 1 ≤ 4 by omega)]
private lemma ratioT (C : ℝ) (m:ℕ) : ∀ᶠ x:ℝ in atTop, C* (Real.log x)^m ≤ maxTest x:=by
 have ht:= (bigEnough m).const_mul C; rw [mul_zero] at ht; filter_upwards [ht.eventually (ge_mem_nhds one_pos), Real.tendsto_log_atTop.eventually_gt_atTop 0] with x l u; exact (div_le_one (by unfold maxTest; positivity)).mp (by rw [mul_div_assoc]; exact l)

-- exhibit every extra POWER of the standard radius; not every length at a fixed pivot.
noncomputable def pushPast (x:ℝ)(k:ℕ):Side:=⟨(seat_u V J x N0).val * (1+radiusB x)^k,mul_pos (seat_u V J x N0).property (pow_pos (by omega) _)⟩
lemma covers (k:ℕ):∀ᶠ x in atTop, Allowed V N0 J x (pushPast V N0 J x k):=by
  let m:ℝ:= N'.val*2*B.val; have hp:0< m:=by unfold m; positivity
  let A:ℕ:= (100+N0); let L(x:ℝ):=Real.log x; let Rb(x):ℝ:=radiusB x; let C':ℝ:= J.h+W.n+1; let C0:=(C'+3*A)*m*3^k
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,ratioT C0 (2+2*k)] with x u p; let M:=seat″ x; let G:=1+Rb x; have he:1≤G:=by unfold G Rb; apply le_add_of_nonneg_right; positivity
  have hv:1 ≤ L x^2:= one_le_pow₀ u; have hz:G≤3*L x^2:=by have hm:Rb x≤ L x^2+1:=(Nat.ceil_lt_add_one (sq_nonneg _)).le; unfold G; linarith
  refine ⟨(Nat.le_mul_of_pos_right _ (pow_pos (by omega : 0 < 1+radiusB x) k)), le_trans ?_ p⟩
  rw [ribbon]; let Q:= C'+A*G; have hl: (M.val:ℝ)=Q:=by change (( (J.h+grainZ V W N0 x+1:ℕ) ):ℝ)=_; unfold Q C' G Rb A grainZ; push_cast; ring
  have h':Q≤ (C'+3*A)*L x^2:=by
    change C'+_*G≤_; refine le_trans (add_le_add (le_mul_of_one_le_right ?_ hv) (mul_le_mul_of_nonneg_left hz (by positivity))) ?_; · unfold C'; positivity
    exact le_of_eq (by ring)
  change ((( (M.val*(1+radiusB x)^k:ℕ)):ℝ)* m)≤_; push_cast; rw [hl]; apply le_trans (b:=((C'+3*A)* (L x)^2)*(3*(L x)^2)^k*m) ?_ (le_of_eq ?_); · gcongr
  unfold C0 L; rw [pow_add,pow_mul, mul_pow]; ring
lemma original : ∀ᶠ x:ℝ in atTop,Allowed V N0 J x (seat_u V J x N0):= (covers V N0 J 0).mono fun x p=> (show pushPast V N0 J x 0=seat″ x from (by apply Subtype.ext; simp [pushPast])) ▸ p
end YM.CF.Py.Period
