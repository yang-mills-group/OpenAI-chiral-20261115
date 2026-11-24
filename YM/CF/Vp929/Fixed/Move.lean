import YM.CF.Vp929.Fixed.Delivery
import YM.CF.Vp929.Stage.Limsup

/-! Move the estimate to the new-pivot budget and actual launch. -/
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x z : ℝ} {D C R0 : ℝ → ℝ} (h' : ℝ) {delay : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {N0 B1 : ℕ} {q : Chi}
variable {n T' : ℕ → ℕ} {P : Prescription R B}
section
variable (g : Service V U W J q h D C R0 P N0 delay) (u : Retag V U W J h N0 delay) (hh : 1≤ h)
    {T : Month x 1 6 2 N0 V W} {τ : ℝ} {Tμ : Month (x+τ*Rx x) 1 6 2 N0 V W}
    (w : Usable (D:=D) V W J N0 z delay T) (w' : Usable (D:=D) V W J N0 z delay Tμ) (e : 0 ≤ τ) (pτ : τ ≤ 1/8)
local notation "ℓ" => R.L
local notation "Y" => (x+τ*Rx x)
local notation "r" => (Rx x)
local notation "vol" => sites (cell m B R.L 0)
variable {S : Cape m B R.L} (p : CanCape J q m S) {f : ℕ → ℝ} (WQ : ∀ i, Frequency R.L (cell m B R.L i) (f i)) (ht : T.q ≤ m.val) (hy : Tμ.q ≤ m.val) (hM : 61 ≤ m.val)
variable {A : ℝ} (Z : ∀ k, Record (Actual T ht S f k) P)
local notation "c" => (A - (dleaf R.L x/1000+dleaf R.L Y /1000))
include p WQ w w' hh g u hM e pτ
/-- The preceding branch at the physical pivot: for each positive depth `k`, represent the
 reference launch, computed at this beta, at the new Month. `b'` remains the vector of bets of
 the reference record on the positive slit and *already satisfies* the analytic branch equations
 at the new pivot (with these top corrections). The bottom offset comparison price. -/
lemma switched (k:ℕ) (hk:0<k) {b':Bet k} (hb':Solved P (Actual T ht S f k) (τ* Rx x) b') :
     ∃ Z':Branch W m k (x+τ*Rx x) N0,
        Z'.Bon J q h D delay ∧ Z'.Represents P (T.a k) ∧ Z'.toSpine=ActualSpine Tμ hy S f k ∧
        Z'.T=Tμ ∧ Solved P Z' 0 b' ∧
        Real.exp (- ( (dleaf R.L x/1000+dleaf R.L (x+τ*Rx x) /1000) * vol))*‖(Actual T ht S f k).bottom b' P‖ ≤ ‖Z'.bottom b' P‖ := by
  classical
  let v : 1≤x:= (w.walk.prices _ le_rfl).grade; have hR:0<r:=Rx_pos v; have hτ:τ*r ≤ r/8:=by nlinarith
  have e':0≤ τ*r:=by positivity
  have τl : |τ*r| ≤ r/8 := by rw [abs_of_nonneg e']; exact hτ
  let X(k):= Actual T ht S f k; let Uμ(k):=Actual Tμ hy S f k; have hu(k) := actual_can (h:=h) (ht:=hy) w' p hM WQ k
  have E : (X k).toSpine = (Uμ k).toSpine := rfl
  let Yμ:= hat R.L Y k; let x₁:= hat R.L x k; have E':Yμ=x₁+τ*r:=hat_up _; have H:x₁≤Yμ:=by linarith
  have t':= T.boot k
  have h₀ : Yμ≤4/3*x₁:=by
    have h:= (w.walk.prices x le_rfl).peri; have _:1≤x:= v
    unfold Rx at E' hτ; nlinarith [Vale.crown R.L x k]
  obtain ⟨L,Ht⟩:= Branch.retag_build u g (Uμ k).toSpine (hu k).can w'.walk.prices w'.walk.late (z:=W.z) (W.pose _ k) w'.music₀ (w.walk.late.trans (Vale.crown R.L x k)) H h₀ (T.a k) ⟨t'.1,t'.2.1,t'.2.2.1,t'.2.2.2.1,t'.2.2.2.2⟩ (w.walk.pole k) (w.walk.isle k)
  let A':= (⟨(Uμ k).toSpine,Tμ,L⟩:Branch W m k Y N0); obtain ⟨p',q'⟩:= Branch.pay_switch g (zero_le_one.trans hh) hk (actual_can (ht:=ht) w p hM WQ k) (Branch.unchanged_rep P (ActualSpine T ht S f k) T) (τ*r) (A':=A') Ht.1 Ht.2 E.symm e' hτ hb'
  exact ⟨A',Ht.1,Ht.2,rfl,rfl,p',q'⟩

section
variable {ht}
omit p WQ w w' u hM e pτ
include g hh
/-- Insensitivity on all fixed levels. Uses *new-pivot* permits/budgets only, comparing e.g.
 the branch with switched-budget representation of the old launch (`Z'` in `switched`) and the
 branch with true new launch (`X`). This is with the actual canonical transfer step, for any
 such branches sharing the spine. Our bounds include all of FleetS. -/
lemma offset_removed_late (ε:ℝ)(pε:0<ε)(j:ℕ) : ∀ᶠ k in atTop,
   ∀ (Z':Branch W m k Y N0) (b':Bet k) (X:Parcel J q h D C R0 Tμ hy S (rho Y C R m B) f k),
      Z'.Bon J q h D delay → Solved P Z' 0 b' → Z'.toSpine=ActualSpine Tμ hy S f k → Z'.T=Tμ →
      X.Prepared P delay → let Z:=Branch.gram P Z' b'
      |(Z j).beta-(X.gram j).beta| ≤ ε ∧
        (∀ y, ‖field U (Z j) (Z'.loom j) y - field U (X.gram j) (S j) y‖ ≤ ε) ∧
        ‖compensated U (Z j) (Z'.loom j) - compensated U (X.gram j) (S j)‖ ≤ ε :=by
  filter_upwards [Branch.limsup g hh (m:=m) Tμ ε pε j] with k e
  intro Z' b' X w w' u t hg Z
  obtain ⟨gk,b₀,h,s⟩:=hg
  rw [s.gramZ]; exact e Z' (Actual Tμ hy S f k) b' b₀ 0 t rfl u w gk w' h
end
/-- In `n` the common UV subsequence, increase allowance (even past that of `l`), using
 `offset_removed_late` at this period with ε the desired exp lower at rate A (here weakened
 for offset comparison in `switched`), divided by four. -/
lemma move_real (t : StrictMono n) (l : ∀ᶠ k in atTop, Real.exp (A * sites (cell m B R.L 0)) /2 ≤ ‖(Z (n k)).f τ‖) :
   ∃ X : ∀ k, Parcel J q h D C R0 Tμ hy S (rho (x+τ*Rx x) C R m B) f k, (∀ k,(X k).Prepared P delay) ∧
     ∀ᶠ t in atTop, Real.exp ( (A - (dleaf R.L x/1000+dleaf R.L Y/1000)) * vol) /4 ≤ ‖compensated U ((X (n t)).gram 0) (S 0)‖ := by
  classical
  let v : 1≤x:= (w.walk.prices _ le_rfl).grade; have hR:0<r:=Rx_pos v; have hτ:τ*r ≤ r/8:=by nlinarith
  have e':0≤ τ*r:=by positivity
  have τl : |τ*r| ≤ r/8 := by rw [abs_of_nonneg e']; exact hτ
  let X(k):= Actual T ht S f k; let Uμ(k):=Actual Tμ hy S f k; have hu(k) := actual_can (h:=h) (ht:=hy) w' p hM WQ k
  choose b hb using fun k=> Branch.existsSolve g (hu k) (z:=0) (by rw [abs_zero]; exact Rx_pos (w'.walk.prices _ le_rfl).grade)
  choose Deliver hW using fun k=> Parcel.send hy (hu k) g (hb k)
  let G:= Real.exp (c*vol); have hG:0<G:=Real.exp_pos _
  have vp(k): Parcel.Prepared P delay (Deliver k):= ⟨hu k,b k,hb k,hW k⟩
  refine ⟨ Deliver, vp,?_⟩
  filter_upwards [l,t.tendsto_atTop.eventually (offset_removed_late (f:=f) (S:=S) g hh hy (G/4) (by linarith) 0), t.tendsto_atTop.eventually (eventually_gt_atTop 0)] with i hi hi' nI
  let k:= n i; have hk : 0<k:=nI
  have E : (X k).toSpine = (Uμ k).toSpine := rfl
  obtain ⟨b',hb'⟩:= existsSolve g (actual_can (ht:=ht) w p hM WQ k) (z:=τ*r) (by linarith)
  have hb₁:= (Z k).real τ ((Branch.range_scale v).mpr (by linarith)) b' hb'
  change Real.exp (A*vol)/2 ≤ ‖(Z k).f τ‖ at hi; rw [hb₁] at hi
  obtain ⟨Z',Hv,Hr,Hs,Hy,Ht,q'⟩:= switched g u hh w w' e pτ p WQ ht hy hM k hk hb'
  let K':= Z'.bottom b' P; let G':=compensated U ((Deliver k).gram 0) (S 0)
  have ha: ‖K'- G'‖ ≤ G/4 := (hi' Z' b' (Deliver k) Hv Ht Hs Hy (vp k)).2.2
  have hp: G/2 ≤ ‖K'‖ := le_trans (b:= _) ((mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le).trans' (by apply le_of_eq; unfold G; rw [←mul_div_assoc (Real.exp _) (Real.exp _),←Real.exp_add]; congr 2; ring)) q'
  exact (show G/4 ≤ ‖G'‖ from by linarith [norm_sub_norm_le K' G'])
end
end YM.CF.Py.Rate
