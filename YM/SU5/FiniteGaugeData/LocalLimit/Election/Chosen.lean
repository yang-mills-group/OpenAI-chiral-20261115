import YM.CF.Vp929.Fixed.Tower
/-!
# The physical branch election underlying DActual

Need to use the same analytic step below the heat burn. `Parcel` data alone
would not ensure this. Expose here that the UV histories selected in the proof
of `Rate.dactual` can be chosen on the actual `Branch`, to track it precisely.
`positioned` is `Vp929/Fixed/Move.move_real` with this strengthening.
-/
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
namespace LocalLimit

/-- The same objects as in `Parcel`, with wave of the Service and with
representation certificate of the Gram data. -/
structure FromShot {T : Month x 1 6 2 N0 V W} {W0 : Cape m B R.L} {f ρ : ℕ→ℝ}
    {ht : T.q ≤ m.val} {k : ℕ} (P : Prescription R B) (delay : ℝ)
    (X : Parcel J q h D C R0 T ht W0 ρ f k) : Prop where
  paid : Bon J q h D delay (Actual T ht W0 f k)
  issued : ∃ b, Solved P (Actual T ht W0 f k) 0 b ∧ X.gram = Branch.gram P (Actual T ht W0 f k) b ∧ X.wave = Branch.wave P (Actual T ht W0 f k) b

lemma deliver {T : Month x 1 6 2 N0 V W} {S : Cape m B R.L} {f : ℕ → ℝ}
    {ht : T.q ≤ m.val} {k : ℕ} (g : Service V U W J q h D C R0 P N0 delay)
    (hp : Bon J q h D delay (Actual T ht S f k)) {b} (hs : Solved P (Actual T ht S f k) 0 b) :
    ∃ p : Parcel J q h D C R0 T ht S (rho x C R m B) f k, p.gram = Branch.gram P (Actual T ht S f k) b ∧ FromShot P delay p := by
  obtain ⟨A,e⟩ := Parcel.send ht hp g hs
  exact ⟨A,e.gramZ,⟨hp,b,hs,e.gramZ,e.waveZ⟩⟩

lemma agrees_pilot {T : Month x 1 6 2 N0 V W} {S : Cape m B R.L} {f ρ : ℕ → ℝ}
    {ht : T.q ≤ m.val} {k : ℕ} (A : Parcel J q h D C R0 T ht S ρ f k) (i : ℕ) (p : i≤k) : A.pilot i=(ActualSpine T ht S f k).pilot x i := by
  let F := ActualSpine T ht S f k
  induction i with
  | zero => exact A.due.unit.trans F.pilot_zero.symm
  | succ i ih => exact add_right_cancel ((A.due.fee i p).symm.trans ((ih (by omega)).trans (F.pilot_move i)))

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
lemma positioned (t : StrictMono n) (l : ∀ᶠ k in atTop, Real.exp (A * sites (cell m B R.L 0)) /2 ≤ ‖(Z (n k)).f τ‖) :
   ∃ X : ∀ k, Parcel J q h D C R0 Tμ hy S (rho (x+τ*Rx x) C R m B) f k,
     (∀ k, FromShot P delay (X k)) ∧
     ∀ᶠ t in atTop, Real.exp ( (A - (dleaf R.L x/1000+dleaf R.L Y/1000)) * vol) /4 ≤ ‖compensated U ((X (n t)).gram 0) (S 0)‖ := by
  classical
  let v : 1≤x:= (w.walk.prices _ le_rfl).grade; have hR:0<r:=Rx_pos v; have hτ:τ*r ≤ r/8:=by nlinarith
  have e':0≤ τ*r:=by positivity
  have τl : |τ*r| ≤ r/8 := by rw [abs_of_nonneg e']; exact hτ
  let X(k):= Actual T ht S f k; let Uμ(k):=Actual Tμ hy S f k; have hu(k) := actual_can (h:=h) (ht:=hy) w' p hM WQ k
  choose b hb using fun k=> Branch.existsSolve g (hu k) (z:=0) (by rw [abs_zero]; exact Rx_pos (w'.walk.prices _ le_rfl).grade)
  choose Deliver hW hf using fun k=> deliver g (hu k) (hb k)
  let G:= Real.exp (c*vol); have hG:0<G:=Real.exp_pos _
  refine ⟨Deliver,hf,?_⟩
  filter_upwards [l,t.tendsto_atTop.eventually (Branch.limsup g hh (m:=m) Tμ (G/4) (by linarith) 0), t.tendsto_atTop.eventually (eventually_gt_atTop 0)] with i hi hi' nI
  let k:= n i; have hk : 0<k:=nI
  have E : (X k).toSpine = (Uμ k).toSpine := rfl
  obtain ⟨b',hb'⟩:= existsSolve g (actual_can (ht:=ht) w p hM WQ k) (z:=τ*r) (by linarith)
  have hb₁:= (Z k).real τ ((Branch.range_scale v).mpr (by linarith)) b' hb'
  change Real.exp (A*vol)/2 ≤ ‖(Z k).f τ‖ at hi; rw [hb₁] at hi
  let Yμ:= hat R.L Y k; let x₁:= hat R.L x k; have E':Yμ=x₁+τ*r:=hat_up _; have H:x₁≤Yμ:=by linarith
  have t':= T.boot k
  have h₀ : Yμ≤4/3*x₁:=by -- r small
    have h:= (w.walk.prices x le_rfl).peri; have _:1≤x:= v --  at v
    unfold Rx at E' hτ; nlinarith [Vale.crown R.L x k]
  obtain ⟨L,Ht⟩:= Branch.retag_build u g (Uμ k).toSpine (hu k).can w'.walk.prices w'.walk.late (z:=W.z) (W.pose _ k) w'.music₀ (w.walk.late.trans (Vale.crown R.L x k)) H h₀ (T.a k) ⟨t'.1,t'.2.1,t'.2.2.1,t'.2.2.2.1,t'.2.2.2.2⟩ (w.walk.pole k) (w.walk.isle k)
  let A':= (⟨(Uμ k).toSpine,Tμ,L⟩:Branch W m k Y N0); obtain ⟨p',q'⟩:= Branch.pay_switch g (zero_le_one.trans hh) hk (actual_can (ht:=ht) w p hM WQ k) (Branch.unchanged_rep P (ActualSpine T ht S f k) T) (τ*r) (A':=A') Ht.1 Ht.2 E.symm e' hτ hb'
  let K':= A'.bottom b' P; let f':= (Uμ k).bottom (b k) P; have ha: ‖K'- f'‖ ≤ G/4 := (hi' A' (Uμ k) b' (b k) 0 rfl rfl rfl Ht.1 (hu k) p' (hb k)).2.2
  have hp: G/2 ≤ ‖K'‖ := le_trans (b:= _) ((mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le).trans' (by apply le_of_eq; unfold G; rw [←mul_div_assoc (Real.exp _) (Real.exp _),←Real.exp_add]; congr 2; ring)) q'
  rw [hW _]; exact (show G/4 ≤ ‖f'‖ from by linarith [norm_sub_norm_le K' f'])
end
end LocalLimit
end YM.CF.Py.Rate
