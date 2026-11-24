import YM.CF.Vp929.Ladder.Bare

/-! Compare a branch to one starting a step earlier (or at same mesh, budget switched). -/
set_option autoImplicit false
set_option maxHeartbeats 900000
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m m' n n' N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x x' delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k k' : ℕ} {P : Prescription R B}
open Complex in
lemma compensate_cost {Z v v' : ℂ} (r : ℝ) (u : v.re - v'.re ≤ r) : Real.exp (-r)* ‖Complex.exp (-v')*Z‖ ≤ ‖Complex.exp (-v)*Z‖ := by
  simp only [norm_mul,norm_exp,neg_re]; rw [←mul_assoc,←Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith)) (norm_nonneg _)

namespace Branch
local notation "M" => cell m B R.L
local notation "X" => hat R.L x
local notation "Rₓ" => (strip x/8)
abbrev bottom (A : Branch W m k x N0) (b : Bet k) (P : Prescription R B) := compensated U (A.gram P b 0) (A.loom 0)

variable {u : BudgetPoint} (H : Service V U W J q h D C R0 P N0 delay)
  (hh : 0≤h) (hk : 0<k) {A : Branch W m k x N0} (a : Bon J q h D delay A)
  (p : Represents P A u)
local notation "S" => sites (M 0)
include hk H p a hh
lemma pay_next {A' : Branch W m' k' x N0} (a' : Bon J q h D delay A') (p' : Represents P A' u)
    (e : Under A.toSpine A'.toSpine 1) (hw : |A'.last.move 0| + billX R.L/512 ≤ (strip x/8)/8)
    {b' : Bet k'} (z : ℝ) (t : |z|≤ Rₓ / 8) (ht : Solved P A' z b') :
    ∃ (v : ℝ) (b : Bet k), |v|≤ Rₓ/4 ∧ Solved P A v b ∧ Real.exp (- ((dleaf R.L x/1000+dleaf R.L (X 1)/1000 + (C x)/(R.L.val:ℝ)^4)*S))*‖A'.bottom b' P‖ ≤ ‖A.bottom b P‖ := by
  let w:= A'.last.move 0; let Z:= A'.toSpine.pilot; let Bₓ:= A.toSpine.pilot
  have E : k+1=k':=e.height; have hk':0<k':=by omega
  let G:= A'.fee P; have he: Z x 1=x-w:= by linarith [show Z x 0=Z x 1+w from A'.toSpine.pilot_move 0,show Z x 0=x from A'.toSpine.pilot_zero]
  let v:= (b'.read 1).re-x
  have hy: IsFixedPt (updateBet (Z x) G z) b':= ht.fixp; have hy₁ : b'.read 1= Z x 1+(z:ℂ)+G 0 b':= by
    rw [Bet.read_of_le _ hk']; refine Eq.trans (congrFun hy.symm ⟨1,(by omega)⟩) ?_; simp [updateBet]
  have hRt:0<strip x:= strip_pos (a.prices x le_rfl).grade
  have hD:‖G 0 b'‖ ≤ D x := by
    have h:= (a'.posts H).bound 0 hk' b' (a'.area H ht.toRealQ 1); simpa [G] using h
  have h₁: |v| ≤ Rₓ / 4 := by
    have hv:= abs_le.mp t; have t':= abs_le.mp ((Complex.abs_re_le_norm (G 0 b')).trans hD); have he:= he; unfold v; rw [hy₁,Complex.add_re,Complex.add_re,Complex.ofReal_re,Complex.ofReal_re]; exact abs_le.mpr ⟨by linarith [le_abs_self w,(a.prices _ le_rfl).slow,t'.1,hv.1],by linarith [neg_le_abs w,(a.prices _ le_rfl).slow,t'.2,hv.2]⟩
  let b:Bet k := fun i=> b'.read (i.val+1); have hx(i)(hi:i≤k): b.read i=b'.read (i+1):=by rw [Bet.read_of_le _ hi]
  have hs : b' ∈ A'.BetaArea (1/4) 0 := ht.fixp ▸ (a'.posts H).into ht.paid (by rw [hat_zero,Complex.norm_real, Real.norm_eq_abs]; linarith)
  have bq : A.RealQ b := by
    refine ⟨fun i _ hi=>?_, fun i hi=> by rw [hx i hi]; exact ht.im (i+1) (by omega)⟩
    have hx:= hx i hi; let I:=Z x (i+1); let Y:=Bₓ x i; have hg: I-Y= -w:=by linarith only [he,e.pilot x x i hi]
    have ha:‖(I:ℂ)-Y‖ ≤ strip (X i)/2:=by rw [← Complex.ofReal_sub,hg,Complex.norm_real,Real.norm_eq_abs,abs_neg]; linarith only [hw,hRt,(a.prices _ le_rfl).slope,(a.prices x le_rfl).increase _ (Vale.crown R.L x i)]
    have hp:= (a.clocks i).ratio; rw [←hat_step] at hp; have t:= hs (i+1) (by omega) (by omega); change ‖b'.read (i+1)-(I:ℂ)‖ ≤ _ at t
    rw [hx,show b'.read (i+1)-_= b'.read (i+1) - (I:ℂ) + ((I:ℂ)-(Y:ℂ)) by dsimp only [Y,Bₓ]; ring]; apply (norm_add_le ..).trans; linarith
  have htop:= commonTop e bq ht.toRealQ hx p p'
  have ha:= same_descent hh H e a a' bq ht hx htop 0 hk.le
  have hβ : b.read 0=(x:ℂ)+(v:ℂ):=by nth_rw 1 [← bq.coeRe 0 (by omega)]; rw [hx 0 (by omega)]; dsimp only [v]; push_cast; ring
  refine ⟨v,b,h₁,solved_descent hh H e a a' bq ht hx htop hβ,?_⟩
  have hv:= (ha.1.partition U).trans (a'.partition H ht 0 hk').symm; unfold bottom compensated
  have e₁:= ((a'.active_law H ht.toRealQ 0 hk').2.2.2); have e₂:= ((ha.2 hk).2.2); rw [hat_zero] at e₁ e₂
  rw [hv]; apply compensate_cost
  let w:=(R.L.val:ℝ)^4; have hw:0<w:=by unfold w; exact pow_pos (Nat.cast_pos.mpr R.L.property) _
  have hI:sites (cell m' B R.L 0)=S/w:=by
    rw [eq_div_iff hw.ne',← sites_step]
    exact congrArg (fun m=> sites (mid m B)) (e.mesh 0).symm
  rw [hI] at e₁; have η:= (abs_le.mp e₁).1; change _ ≤ (A'.gram P b' 0).v.re-(A'.gram P b' (0+1)).v.re at η
  simp only [div_eq_mul_inv,w] at *; linarith only [(abs_le.mp e₂).2,η]

/-- Switch the same branch to paying the new Month, keeping the old reference top. -/
lemma pay_switch (z : ℝ) {A' : Branch W m k (x+z) N0} (a' : Bon J q h D delay A') (p' : Represents P A' u)
    (e : A'.toSpine=A.toSpine)
    {b : Bet k} (hz : 0 ≤ z) (t : z ≤ Rₓ/8) (ht : Solved P A z b) :
    Solved P A' 0 b ∧ Real.exp (- ((dleaf R.L x/1000+dleaf R.L (x+z)/1000)*S))*‖A.bottom b P‖ ≤ ‖A'.bottom b P‖ := by
  have hs : b ∈ A.BetaArea (1/4) 0 := ht.fixp ▸ (a.posts H).into ht.paid (by rw [hat_zero,Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg hz]; linarith)
  have he:= Under.refl A.toSpine; nth_rw 1 [←e] at he
  have bq : A'.RealQ b := by
    refine ⟨fun i _ hi=> ?_, ht.im⟩
    let y:= hat R.L (x+z) i; have v: strip (X i) ≤ strip y:= (a.clocks i).increase _ (by dsimp only [y]; rw [hat_up]; exact le_add_of_nonneg_right hz)
    have hg:= hs i (Nat.zero_le _) hi; let I:= A.toSpine.pilot x i; have hI : A'.toSpine.pilot (x+z) i= I+z := by rw [e]; unfold I Spine.pilot; ring
    rw [hI,Complex.ofReal_add,←sub_sub]; apply (norm_sub_le ..).trans; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]; linarith [(a.prices x le_rfl).increase _ (Vale.crown R.L x i), strip_pos (a.prices x le_rfl).grade]
  have he':= commonTop he bq ht.toRealQ (fun i _=> rfl) p' p
  have hv : b.read 0=((x+z:ℝ):ℂ)+((0:ℝ):ℂ):= by rw [Bon.anchor ht]; simp
  have ha:= same_descent hh H he a' a bq ht (fun i _=>rfl) he' 0 hk.le
  refine ⟨ solved_descent hh H he a' a bq ht (fun i _=>rfl) he' hv, ?_⟩; unfold bottom compensated
  rw [ha.1.partition U]; apply compensate_cost; have hp:= (abs_le.mp ((ha.2 hk).2.2)).2; simp only [zero_add,hat_zero] at hp; linarith
end Branch
end YM.CF.Py.Rate
