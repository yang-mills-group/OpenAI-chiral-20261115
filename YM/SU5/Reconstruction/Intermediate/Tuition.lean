import YM.SU5.Reconstruction.Intermediate.Solver
/-! Limsup‐bound adaptation to intermediate solver election. Note s not necessarily at top, indexing ℳ.c tape differs from Donor$ demands on spend.W.Reusing same Service trajectory.Q. -/
set_option autoImplicit false
set_option quotPrecheck false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {x delay : ℝ} {C R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
    (A : Branch W m k x N0)
local notation "Ω" => cell m B R.L
local notation "Xc" => A.T.a
local notation "Xh" => hat R.L x
local notation "Xs" => A.last.Q
local notation "Xr" => A.loom
local notation "X₀" => A.toSpine.address
local notation "Yb" i => dleaf R.L (hat R.L x i)
local notation "Xm" => A.last.move
namespace Intermediate
variable (s:ℕ) {D:ℝ→ℝ} {h:ℝ} (F:Room s→ Corr (cell m B R.L s))
variable (u:Room s) (H : Service V U W J q h D C R0 P N0 delay) (pP:ResponsiveService J q N0 h delay P) (a:Bon J q h D delay A) (hh:1≤h)(τ:s ≤ k)(pS:Qualified A s D h F)
variable (r:Settles P A s D F u)
local notation "Z" => cooled P A s D F
local notation "X" i:max => (Z).guess i u
local notation "β" => temper A s D
open VolumeRate
variable (b : Bet k) (t : Solved P A 0 b)
local notation "Y" i:max => A.gram P b i
local notation "C₁" i:max => A.chargeLevel P b i
local notation "C₂" i:max => (Z).G i u
include H pP a hh τ pS r t
lemma same_shelf (n i:ℕ)(e:i+n<s): Cost (Xc i) h (dleaf R.L (Xh i)*decline n) (C₁ i-C₂ i) ∧ |(Y i).beta-β i u|≤ strip (Xh i)*decline n:= by
 induction n generalizing i with
 | zero =>
    have g:i<s:=e; have s0:= (lt_of_lt_of_le g τ).le; have he:= (Intermediate.earns P A s a F H pP τ hh pS i g).1.cost u
    have hx:= a.charged H t.toRealQ i s0
    constructor
    · exact (hx.toCost.sub he.toCost).mono (by simp only [decline,pow_zero,mul_one]; linarith [(a.clocks i).leaf])
    have hs:=t.paid i (Nat.zero_le _) s0; rw [←t.toRealQ.coeRe i s0,←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hs
    have hk:= budget A s a i u; have hy:= abs_sub_le (Y i).beta (A.toSpine.pilot x i) (β i u); rw [abs_sub_comm (A.toSpine.pilot x i) (β i u)] at hy -- abs |...? rw may choose RHS? inspect
    change |(Y i).beta-A.toSpine.pilot x i| ≤ _ at hs
    simp only [decline,pow_zero,mul_one]; linarith
 | succ n ih=>
    have η: 0≤decline n:=by unfold decline; positivity
    have stars (j) (w : j+1+n<s) : Cost (Xc j) h (dleaf R.L (Xh j) * ((decline n+decline n)/4)) (C₁ j-C₂ j) ∧
         |(A.fee P j b).re-(Z).posted j u| ≤ 100* D (Xh j)*(decline n+decline n) := by
      have hx:j+1<s:=by omega
      have he := hx.trans_le τ; have hs : j<s:=by omega
      obtain ⟨f,g⟩:= ih (j+1) w
      rw [a.corr_successor H t.toRealQ j (by omega), (Z).step j hs u,←a.fee_eq H t.toRealQ j (by omega)]
      refine (a.certified H j (by omega)).stars _ _ _ _ _ _ ?_ η η (hat_step j ▸ f) (hat_step j ▸ g)
      rintro l p; obtain rfl|p:= p
      · exact ⟨hat_step j ▸ (a.beta_ok H t.toRealQ _ he.le).1, hat_step j ▸ a.charged H t.toRealQ _ he.le⟩
      rw [Set.mem_singleton_iff] at p; subst l
      exact ⟨hat_step j ▸ (accepted A s a _ he.le u).1, hat_step j ▸ (Intermediate.earns P A s a F H pP τ hh pS _ hx).1.cost u⟩
    constructor
    · exact (stars i (by omega)).1.mono (by unfold decline; rw [pow_succ]; exact le_of_eq (by ring))
    have hi:i ≤ k:=by omega
    have he:b.read i=(A.toSpine.pilot x i:ℂ)+↑(0:ℝ)+∑ j∈range i,A.fee P j b:=by
      rw [Bet.read_of_le _ hi]; exact congrFun t.fixp.symm _
    have hU:(Y i).beta-β i u=∑ j∈range i,((A.fee P j b).re-(Z).posted j u) := by
        rw [show temper A s D i u=A.toSpine.pilot x i+∑ j∈range i, predict s (D ∘ hat R.L x) u j from rfl]; rw [Finset.sum_sub_distrib]; change (b.read i).re- _ = _; rw [he,Complex.add_re,Complex.add_re,Complex.ofReal_re,Complex.re_sum, show ∑ j∈range i,(Z).posted j u= _ from Finset.sum_congr (g:=fun j=> predict s (D ∘ hat R.L x) u j) rfl (fun j v=>r j (by have he:= mem_range.mp v; omega))]; simp only [Complex.ofReal_re]; ring
    rw [hU]
    refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum fun j v=> (stars j (by have he:= mem_range.mp v; omega)).2).trans ?_)
    rw [←Finset.sum_mul, ←Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pilotMargin A a i) (by norm_num : (0:ℝ) ≤ 100)) (add_nonneg η η)).trans (le_of_eq ?_)
    unfold decline; rw [pow_succ]; ring
end Intermediate
end LocalLimit
end YM.CF.Py.Rate
