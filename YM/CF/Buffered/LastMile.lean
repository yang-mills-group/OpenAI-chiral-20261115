import YM.CF.Buffered.History
import YM.CF.Continuum.LaurelBeam
import YM.CF.Volume.Extensive
import YM.CF.Py.Costs

/-!
# Proving the needed level-zero `rec-delta` from the budget estimate in that lemma

We use existing extensive (exponential in the volume) bounds and fuel
sensitivity, no analyticity argument. In fact do NOT restrict our
rec-delta calculation to m with m⁵≤n. If the budget error per site times
volume isn't small, we pay the triangle inequality by those extensive
bounds. `BudgetCompared` states exactly what's needed from the preceding
budget estimate in that lemma; conditional on it not on rec bounds with it
already used; don’t claim to prove budget comparison by gluing or
shooting. Will derive also extensive absolute bounds, signed-lower from
donor throughout the cone, estimates on marked ratio differences.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 540000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Py Haro
open Advance

namespace Burn
open Graph (recX exPrice taxY past principal_min)
def trial (B : Side) (β t W Λ v C : ℝ) := taxY (More (CSide 1 B)) β t W Λ + exPrice (CSide 1 B) v v C
lemma expense_units (B L m : Side) (β t W Λ v C : ℝ) : taxY (More (cell m B L 0)) β t W Λ + exPrice (cell m B L 0) v v C=trial B β t W Λ v C * (m.val:ℝ)^4 := by
 unfold trial exPrice Graph.pittance taxY Graph.doorF Graph.lark cell; rw [Vale.mesh,pow_zero,mul_one]
 unfold CSide More; push_cast; norm_num; ring
section
variable {m B L : Side} {u h v β d e t κ C r W μ Λ : ℝ}
  {j k : ℕ} {o : Odd L.val} {S : Pricing j L o (Thread j)}
  (U : Grasp S B d) {l : Loom (CSide m B)} (p : Roof _ u d k l)
  {X Y : GramM (CSide m B)}
variable (hp : U.roundZ ≤ (CSide m B).val) (z : X.path.Bounds X.funds μ W Λ)
local notation "N" => CSide m B
local notation "Γ" => taxY (More N) X.beta X.p.threshold W Λ + exPrice N v v C
include p hp z
lemma fromBudget (x : Graph.Ledger h v v r C X) (y : Graph.Ledger h v v r C Y) (he : Graph.Diff.ξX X Y κ h)
   (a : CloseC X Y) (f:X.beta=Y.beta) (w:X.slip=0) (g:Y.slip=0) (u : 1≤h) (s : 0≤r) (B' : 0≤ X.beta) (v₀ : 0≤v) :
   Delta U X Y l (Real.exp (taxY (More (CSide m B)) X.beta X.p.threshold W Λ + exPrice (CSide m B) v v C)*(4 * Graph.Diff.rankV (CSide m B) κ)) := by
 let d' := Graph.Diff.rankV (CSide m B) κ; have hd' : 0 ≤ d':= le_trans (Pastry.pitch (zero_le_one.trans u) _) (Graph.toeE he.1 (zero_le_one.trans u) 1)
 intro i; by_cases hz:d' ≤ 1/2
 · let τ := past X i.1; let A := changeM (m:=m) U (l i) X.J.M; let F:= Real.exp (Γ)
   have hx : past Y i.1=τ := by unfold τ Graph.past; rw [f, a.path,a.width,a.fund]
   have hM: ‖A‖=1 := (sea_g hp _ (p.paid i) X.J.M).2; have hF:= Graph.Diff.mile_diff X Y u j a.width w g a.taste x y l i he hz ((U.broadness _ hp X.J.M).projection _ (p.paid i)) s v₀
   have hA: Graph.beam X U l i-Graph.beam Y U l i= acts (Graph.mile j X l i-Graph.mile j Y l i) A := by rw [act_sub]; unfold Graph.beam; rw [←a.taste]
   rw [Graph.porch,Graph.porch,hx]; change ‖τ • _ - τ • _‖ ≤ _; rw [←smul_sub,hA,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_add]; apply (mul_le_mul (b:=Real.exp (taxY (More N) X.beta X.p.threshold W Λ)) (d:=Real.exp (exPrice N v v C)*(3*d')) (Real.exp_le_exp.mpr (neg_le.mp (principal_min _ _ _ z B' i.1))) ((Graph.spentS _ _ A).trans (by rw [hM,mul_one]; exact hF)) (norm_nonneg _) (Real.exp_pos _).le).trans; rw [←mul_assoc]; gcongr; norm_num
 have he' : Y.path.Bounds Y.funds μ W Λ := by rw [←a.path,←a.fund]; exact z
 have hv := Graph.recPointTax Y l p U hp y he' s u (by rwa [←f]) i; rw [←a.width,←f] at hv
 refine (norm_sub_le ..).trans ((add_le_add (Graph.recPointTax _ _ p U hp x z s u B' _) hv).trans ?_); change Real.exp (Γ) +Real.exp (Γ) ≤ Real.exp (Γ)*(4*d'); have hr: 2 ≤ 4*d' := by linarith
 rw [←mul_two]; gcongr
end

open Graph.Diff
def tol (n b₀ : ℕ) := (2:ℝ)^ (-(3*(depth b₀ n:ℝ))/4)

variable {K : Calibration} {m : Side} {n : ℕ} {X Y : Vestal m K.B K.R.L} {O : K.T.q ≤ m.val} {S: Cape m K.B K.R.L} {q r : ℕ→ Haro.SpaceM} {β θ ν : ℕ→ℝ}
-- level zero (hat = x, slip both zero, all nonbudgets from same hue at step 0; since Y independently paying offsets)
def leaf₀ (K: Calibration) := dleaf K.R.L (hat K.R.L K.x 0)
def BudgetCompared (K:Calibration) {m:Side} (n:ℕ) (X Y : Vestal m K.B K.R.L) := LotR (Y 0) K.h (leaf₀ K) (leaf₀ K) ∧ ξX (X 0) (Y 0) (tol n K.b₀) K.h -- zero slips in both LotR
variable (U : Shots K.V K.T K.J K.η O S n X Y q r β θ ν K.h K.R0 K.δ)
include U
local notation "uX" => X 0
local notation "uY" => Y 0
local notation "v'" => leaf₀ K
def trial₀ (K: Calibration) : ℝ := trial K.B K.x (K.T.a 0).threshold K.K.top.paths K.V.W.bar (leaf₀ K) (cashU K.W.C)
lemma bills₀ (p : CloseC (X 0) (Y 0)) (f : BudgetCompared K n X Y) :
 Delta K.P (X 0) (Y 0) (S 0) (Real.exp (trial₀ K*(m.val:ℝ)^4)*(4*rankV (K.c m) (tol n K.b₀))) := by
 let W := cashU K.W.C; let Λ := levelQ K.W.C
 have hw := f.1
 let S':= U.sharp; have hT:= S'.note.owns 0 (Nat.zero_le n)
 have h:= (S'.note.note 0 (Nat.zero_le n)).lot_p le_rfl le_rfl; let g:= S'.roof 0; let t:= g.paid
 have ht:Roof _ K.J.k K.e K.J.n (S 0) := {t with paid:=fun i=>(t.paid i).shrink K.J.hr.le}
 have hv : InterestX K.W.C _ (X 0).J := by rw [←hT.taste]; exact (K.W.arm ..).sound _
 have hz : (X 0).path.Bounds (X 0).funds K.K.top.width K.K.top.paths K.V.W.bar := by rw [←hT.path, ←hT.fund]; exact K.V.L.mood (n-0)
 have hi:= K.positive_h; have hb:=U.cap_pivot
 have hu:= fromBudget K.P ht (K.J.gran.trans g.size) hz (frostQ h (by linarith) hv) (frostQ hw (by linarith) (show InterestX K.W.C _ (Y 0).J from by rw [←p.taste]; exact hv)) f.2 p (hb.trans U.pivot.symm) h.live hw.live hi (level_p _).le (by rw [hb]; exact le_trans (Real.exp_pos _).le K.base) (hush_h h (by linarith))
 rw [hb,show (X 0).p= K.T.a 0 from hT.width.symm,expense_units] at hu; exact hu
lemma sharp_extensive (i:Orbit (K.c m)) : ‖recX K.P (X 0) (S 0) i‖ ≤ Real.exp (trial₀ K * (m.val:ℝ)^4) := by
 let X':=U.sharp; have H:=X'.note.owns 0 (Nat.zero_le n); let g:= X'.roof 0; let t:=g.paid
 have ht:Roof _ K.J.k K.e K.J.n (S 0) := {t with paid:=fun i=>(t.paid i).shrink K.J.hr.le}
 have hi:= K.positive_h; have hb:=U.cap_pivot
 have hv : InterestX K.W.C _ (X 0).J := by rw [←H.taste]; exact (K.W.arm ..).sound _
 have hz : (X 0).path.Bounds (X 0).funds K.K.top.width K.K.top.paths K.V.W.bar := by rw [←H.path, ←H.fund]; exact K.V.L.mood (n-0)
 have hy: ‖recX K.P (X 0) (S 0) i‖ ≤ Real.exp (taxY (More (cell m K.B K.R.L 0)) (X 0).beta (X 0).p.threshold K.K.top.paths K.V.W.bar + exPrice (cell m K.B K.R.L 0) (leaf₀ K) (leaf₀ K) (cashU K.W.C)):=
    Graph.recPointTax (X 0) (S 0) ht K.P (K.J.gran.trans g.size) (frostQ ((X'.note.note 0 (Nat.zero_le n)).lot_p le_rfl le_rfl) (by linarith) hv) hz (level_p _).le hi (by rw [hb]; exact le_trans (Real.exp_pos _).le K.base) i
 rw [hb,show (X 0).p= K.T.a 0 from H.width.symm,expense_units] at hy; exact hy

def loss (K:Calibration) := 4 * ((4:ℝ)*K.B.val)^4
-- ms rec-delta for the actual offset stripped densities at stop 0 (any size m with paired histories)
theorem rec_delta (h : BudgetCompared K n X Y) : Delta K.P (X 0) (Y 0) (S 0) (bill m.val n K.b₀ (trial₀ K+loss K)) := by
 have t:=U.sharp.note.owns 0 (Nat.zero_le n); have v:=U.hue 0 (Nat.zero_le n)
 let D:ℝ := loss K*m.val^4; let G := trial₀ K*m.val^4; let M : ℝ := 2^ (-(depth K.b₀ n :ℝ)/2)
 have hM : 0≤ M:= by unfold M; positivity
 have hz : tol n K.b₀≤M:=Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have u:0≤(depth K.b₀ n:ℝ):= Nat.cast_nonneg _; linarith)
 have hd:0≤D:=by unfold D loss; positivity
 have hp:4*rankV (K.c m) (tol n K.b₀) ≤ M*Real.exp D:=by
    apply mul_le_mul hz ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp D)) hd hM |>.trans' -- need rewrite rankV
    unfold Graph.Diff.rankV D loss Calibration.c cell; rw [Vale.mesh, pow_zero, mul_one]; unfold CSide More; push_cast; apply le_of_eq; ring
 intro i; apply le_trans ((bills₀ U ⟨t.width.symm.trans v.width,t.path.symm.trans v.path,t.taste.symm.trans v.taste,t.fund.symm.trans v.fund⟩ h) i)
 unfold bill; rw [add_mul,Real.exp_add]; change _≤ M*_
 rw [mul_left_comm M]; exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
end Burn

/- Alternative history input not assuming ∆ on densities. -/
structure Comparisons (K:Calibration) where
 loom : ∀ m: Side, Cape m K.B K.R.L
 sharp : ∀ m: Side, ℕ → Vestal m K.B K.R.L
 warm : ∀ m: Side, ℕ → Vestal m K.B K.R.L
 B₀ : ℕ→ℕ→ℝ
 wave : ℕ→ℕ→SpaceM
 tilt : ℕ→ℕ→ℝ
 wave' : ℕ→ℕ→SpaceM
 tilt' : ℕ→ℕ→ℝ
 c' : ℝ
 paired : ∀ᶠ n in atTop, ∀ m:Side, ∀ a: K.Allowed m n,
   Shots K.V K.T K.J K.η (K.monthSize m a.1) (loom m) n (sharp m n) (warm m n) (wave n) (wave' n) (B₀ n) (tilt n) (tilt' n) K.h K.R0 K.δ ∧
   Burn.BudgetCompared K n (sharp m n) (warm m n) ∧ -- at stop 0
   Burn.presrec m.val c'≤ ‖vac0 K.P (warm m n 0) (loom m 0)‖
 lawn : ∀ m, K.takes m → ∀ j:ℕ, LoomLaw (loom m j) K.w
def Comparisons.hist {K : Calibration} (p : Comparisons K) : Histories K :=
 { p with m' := Burn.trial₀ K+Burn.loss K, paid:= p.paired.mono fun _ h m t=>⟨(h m t).1,Burn.rec_delta (h m t).1 (h m t).2.1,(h m t).2.2⟩ }
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Comparisons.hist
