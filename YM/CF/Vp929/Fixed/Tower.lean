import YM.CF.Vp929.Ledger.Roof
import YM.CF.Vp929.Analysis.Pivot
import YM.CF.Vp929.Fixed.Move

set_option autoImplicit false
set_option maxHeartbeats 1200000
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V : Grace K R L) {d : ℝ} {B N : Side} {U : Grasp V.U B d}
variable (W : GivenX V U) (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ → ℝ) (B1 N0 : ℕ)
def trunk (B₁ k : ℕ) := k^4+k+1+B₁
variable {F_:(s:Side)→Scree.Loom s→ Prop}
/-- Full signed denominator estimate at a single fixed x. -/
structure DActual (P:Prescription R B)(e:ℝ) (x : ℝ) (Λ:(s:Side)→Scree.Loom s → Prop) : Prop where
  earn : ∃ T : Month x 1 6 2 N0 V W, (∃ z,Usable (D:=D) V W J N0 z e T)∧ MeterQ V 1 2 6 N0 J q h R0 D x T ∧ 1 ≤ x ∧ ∃ M₀ : Side, ∃ k σ : ℕ → ℕ,
    let n := trunk B1 ∘ k
    let A := fun i=> rung R (M₀*N) (σ i)
    StrictMono k ∧ StrictMono n ∧ StrictMono σ ∧ StrictMono (fun i=> (A i).val) ∧
    ∃ E : ℝ, 0 ≤ E ∧ ∀ i,
      (∃ M : Side, A i=M*N ∧ J.h≤ M.val) ∧ 61 ≤ (A i).val ∧
      ∃ h' : T.q ≤ (A i).val, ∃ (W0 : Cape (A i) B R.L) (ρ : ℕ→ℝ), CanCape J q (A i) W0 ∧ (∀ j, Λ _ (W0 j)) ∧ (∀ j, 0 < ρ j) ∧
      ∃ X : ∀ l : ℕ, Parcel J q h D C R0 T h' W0 ρ (commonQ R B (M₀*N)) l,
      (∀ l, (X l).Prepared P e) ∧
      ∀ᶠ t in atTop, Real.exp (-E* sites (cell (A i) B R.L 0)) ≤ ‖compensated U ((X (n t)).gram 0) (W0 0)‖
variable {V W J q h D C R0 B1 N0} {delay x z τ : ℝ} {P : Prescription R B} {T : Month x 1 6 2 N0 V W}
include V in
lemma rung_ladder (m : Side) : StrictMono (fun k=> (rung R m k).val) := by
  refine strictMono_nat_of_lt_succ fun n=>?_ ; change (Vale.mesh m R.L n).val < (mesh m R.L (n+1)).val; rw [mesh_succ]; exact lt_mul_of_one_lt_right (mesh m R.L n).property (show 1 < R.L.val by have he:=V.tallX; omega)
lemma trunk_up (B1) : StrictMono (trunk B1) := by
  intro i j p; unfold trunk; gcongr
variable (g : Service V U W J q h D C R0 P N0 delay) (u : Retag V U W J h N0 delay) (hh : 1≤h)
local notation "X" => (x+τ*Rx x)
local notation "m0" => (oYY V N0 J x)
local notation "A" => rung R (oYY V N0 J x)
local notation "dX" m => sites (cell m B R.L 0)
local notation "pQ" => commonQ R B (oYY V N0 J x)
variable (w : Usable (D:=D) V W J N0 z delay T)
private def tower_spots (x : ℝ) (N0) (J : Robes N V W) (n) := mesh (seat_u V J x N0) R.L n
lemma factors (J : Robes N V W) (n : ℕ) : rung R (oYY V N0 J x) n=tower_spots x N0 J n * N := Month.ruler ..
lemma tall (J : Robes N V W) (n : ℕ) : J.h ≤ (tower_spots x N0 J n).val := (show J.h ≤ (seat_u V J x N0).val by change _≤J.h+_+1; omega).trans (mesh_ge ..)
include w in
lemma available (u:ℕ) : T.q ≤ (A u).val := w.walk.size.trans (mesh_ge ..)
section
variable (b1 : ℕ → ℕ) (hb1 : StrictMono b1) (S : (i:ℕ) → Cape ((rung R (oYY V N0 J x)) i) B R.L)
    (v : ∀ i, CanCape J q ((rung R (oYY V N0 J x)) i) (S i))
    (Z : ∀ i k, Record (Actual T (available w i) (S i) (commonQ R B (oYY V N0 J x)) k) P)
include g u w hh Z v hb1
private lemma bought (rF:RackedΛ F_ J) (pF:∀ i j,F_ _ (S i j)) {s:ℝ} (t : 0≤τ) (p : τ≤1/8) {Tμ : Month (x+τ*Rx x) 1 6 2 N0 V W}
    (w' : Usable (D:=D) V W J N0 z delay Tμ) (hτ : ∃ᶠ i in atTop, ∀ᶠ k in atTop, Real.exp (s * sites (cell (rung R (oYY V N0 J x) i) B R.L 0)) /2 ≤ ‖(Z i (trunk B1 (b1 k))).f τ‖) : DActual V W J q h D C R0 B1 N0 P delay X F_ := by
  classical
  obtain ⟨σ,r,hr⟩:= extraction_of_frequently_atTop (hτ.and_eventually ((rung_ladder (V:=V) m0).tendsto_atTop.eventually_ge_atTop Tμ.q)); let M₁:= seat_u V J x N0; let n:= trunk B1 ∘ b1; let c:=(s-(dleaf R.L x/1000+dleaf R.L X/1000)); have hn:StrictMono n:= (trunk_up B1).comp hb1
  let E':= |c| + Real.log 4; have hc:0≤Real.log 4:=Real.log_nonneg (by norm_num)
  refine ⟨⟨Tμ,⟨z,w'⟩,meter w' g rF,(w'.walk.prices _ le_rfl).grade,M₁,b1,σ,hb1,hn,r,(rung_ladder (V:=V) m0).comp r,E',add_nonneg (abs_nonneg _) hc,?_⟩⟩
  intro i; let m:= A (σ i); have hm:61≤ m.val:= w.walk.large.trans (mesh_ge ..); obtain ⟨η,D'⟩:= hr i; change Tμ.q≤ m.val at D'
  obtain ⟨Y,pY,e⟩:= move_real g u hh w w' t p (v (σ i)) (fun j=> commonFreq w.walk.tiny le_rfl) (available w _) D' hm (Z (σ i)) hn η
  refine ⟨⟨_, factors J _,tall J _⟩,hm,D', S _,rho X C R m B,v _,pF _,fun _=> Real.exp_pos _, Y,pY,e.mono ?_⟩
  intro t h; let V':= dX m; have p:1≤V':=sites_pos _
  refine le_trans ?_ h; change Real.exp (- E' * V') ≤ Real.exp (c*V')/4
  nth_rw 1 [← Real.exp_log (by norm_num : (0:ℝ)<4)]; rw [← Real.exp_sub]; apply Real.exp_monotone; unfold E'; nlinarith [(abs_nonneg c),(neg_abs_le c)]
end
include g u w hh
/-- The a.e. auxiliary interval of successful pivots (permits must still be identified at the
new budgets). Choice of cape on each rung does not
finance the analytic selection. -/
theorem interval_choice (pF:RackedΛ F_ J) {B1 : ℕ} (p0 : ∃ u > (0:ℝ), ∀ (Xb : GramM (cell (oYY V N0 J x) B R.L 0)) (S:Scree.Loom (cell (oYY V N0 J x) B R.L 0)), RoomAt (h:=h) J N0 x Xb S → u ≤ ‖compensated U Xb S‖)
    (hP : ((R.L.val:ℝ)^4)⁻¹ < VolumeRate.propagation) : ∀ᵐ τ ∂VolumeRate.choiceMeasure,
     ∀ Tμ : Month (x+τ*Rx x) 1 6 2 N0 V W, Usable (D:=D) V W J N0 z delay Tμ → DActual V W J q h D C R0 B1 N0 P delay (x+τ*Rx x) F_ := by
  classical
  have hp(n:ℕ) : ∃ S : Cape (A n) B R.L, CanCape J q (A n) S ∧ ∀ i, F_ _ (S i) := by rw [factors J]; exact hardCape pF q (tall J n)
  choose S p τp using hp; let n:=trunk B1; have hhN:StrictMono n:= trunk_up _
  have he(i k:ℕ) := actual_can (h:=h) (ht:=available w i) w (p i) (w.walk.large.trans (mesh_ge ..)) (fun j=> commonFreq w.walk.tiny (n:=j) le_rfl) k
  let Z(i k:ℕ):= Classical.choice (Branch.history g hh (he i k)); obtain ⟨a,H⟩:= uniform_slit g u hh hP w.walk pF p0
  let v(i):= dX (A i); let f(i k):= (Z i (n k)).f; let D(i):=hat R.L x i; let L:= Vale.billX R.L; have hx:0<L:=(w.walk.prices _ le_rfl).slope; have ht:Tendsto (fun i=> hat R.L x (n i)) atTop atTop:= (show Tendsto (hat R.L x) atTop atTop from tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hx)).comp hhN.tendsto_atTop
  have K(i): ∀ᶠ k in atTop, DifferentiableOn ℂ (f i k) (ball 0 1) ∧ (∀ z ∈ ball (0:ℂ) 1, ‖f i k z‖ ≤ Real.exp (Branch.stopEarn T*v i)) ∧ ∃ y:ℝ,|y|≤1/8 ∧ Real.exp (-a*v i) ≤ ‖f i k y‖ := by
    filter_upwards [ht.eventually_ge_atTop (4*i*L), hhN.tendsto_atTop.eventually_gt_atTop 0] with k hk v
    refine ⟨(Z i (n k)).ana,(Z i (n k)).budget,H i (n k) _ v ?_ rfl (he ..) (unchanged_rep P (ActualSpine ..) T) (Z ..)⟩
    rw [show hat R.L x (n k+i) = hat R.L x (n k)+i*L from by unfold hat L; push_cast; ring]; nlinarith [show (0:ℝ) ≤ ↑i from by positivity]
  obtain ⟨φ,hφ,Hφ⟩:= VolumeRate.paid_points v (fun _=> sites_pos _) (stopEarn T) (-a) f K
  filter_upwards [Hφ,ae_restrict_mem measurableSet_Ioc] with x hx e Tμ hv; obtain ⟨a,ha⟩:=hx
  exact bought g u hh w φ hφ S p Z pF τp (Set.mem_Ioc.mp e).1.le (Set.mem_Ioc.mp e).2 hv ha
end YM.CF.Py.Rate
