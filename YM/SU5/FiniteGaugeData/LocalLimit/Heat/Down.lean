import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Query
import YM.CF.Vp929.Stage.Limsup

/-!
# The lower steps of a comparison election, still offshell

The recurrence records the *guess*, not assuming agreement with the posted output.
The returned shift/ray can be used in a Brouwer solve.
-/
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
    {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
    (A : Branch W m k x N0)
local notation "Ω" => cell m B R.L
local notation "Xc" => A.T.a
local notation "Xh" => hat R.L x
local notation "Xs" => A.last.Q
local notation "Xr" => A.loom
local notation "X₀" => A.toSpine.address
local notation "Yb" i => dleaf R.L (hat R.L x i)
local notation "Xm" => A.last.move
variable {T : Type} [TopologicalSpace T] [Frst : FirstCountableTopology T]

-- recursion parameters chosen downwards from an input level
structure Cooling (s : ℕ) (F : T → Corr (cell m B R.L s)) (β : ℕ → T → ℝ) where
  G : ∀ j : ℕ, T → Corr (cell m B R.L j)
  v : ℕ → T → ℂ
  fromTop : G s = F
  fromZero : v s = 0
  step (i : ℕ) (p : i<s) (t : T) : G i t = (A.op P i).realArr (β (i+1) t) (G (i+1) t)
  offsets (i : ℕ) (p : i<s) (t : T) : v i t = (A.op P i).offset (β (i+1) t) (G (i+1) t) (v (i+1) t)

namespace Cooling
section
omit [TopologicalSpace T] [FirstCountableTopology T]
variable (s : ℕ) (F : T → Corr (cell m B R.L s)) (β : ℕ → T → ℝ)
private def Gq (i : ℕ) (t : T) : Corr (cell m B R.L i) :=
  if _ : i<s then (A.op P i).realArr (β (i+1) t) (Gq (i+1) t)
  else if h : s=i then h ▸ F t else 0
 termination_by s-i

private def offset_v (i : ℕ) (t : T) : ℂ :=
  if _ : i<s then (A.op P i).offset (β (i+1) t) (Gq P A s F β (i+1) t) (offset_v (i+1) t)
  else 0
 termination_by s-i

def descends : Cooling P A s F β := by
  refine ⟨Gq P A s F β,offset_v P A s F β,?_,?_,fun i p t=>?_,fun i p t=>?_⟩
  · ext1 t; rw [Gq, dif_neg (lt_irrefl (s:ℕ)),dif_pos rfl]
  · ext1 t; rw [offset_v,dif_neg (lt_irrefl (s:ℕ))]; rfl
  · rw [Gq,dif_pos p]
  rw [offset_v,dif_pos p]

end
variable {A P} {s : ℕ} {F : T → Corr (cell m B R.L s)} {β : ℕ → T → ℝ} (Z : Cooling P A s F β)
abbrev posted (i : ℕ) (t:T) := (A.op P i).posted (β (i+1) t) (Z.G (i+1) t)
abbrev wave (i : ℕ) (t:T) := (A.op P i).wave (β (i+1) t) (Z.G (i+1) t)
abbrev guess (i : ℕ) (t:T) := construct (Xc i) (V.L.path (k-i)) K.top.clip (Xs i) (β i t) (Z.G i t) (Z.v i t)
abbrev launch (i : ℕ) (t:T) := construct (Xc i) (V.L.path (k-i)) K.top.clip (Xs i)
        (β (i+1) t+Xm i - Z.posted i t) (Z.G i t) (Z.v i t)

variable (Y : Service V U W J q h D C R0 P N0 delay) (p : ResponsiveService J q N0 h delay P)
    (a : Bon J q h D delay A) (hs : s≤k) (hh : 1 ≤ h)
    (he : ∀ i ≤ s, Continuous (β i) ∧ ∀ t:T, enters (hat R.L x i) (β i t))
    (ht : Cleared W h (dleaf R.L (hat R.L x s)) (A.T.a s) (A.last.Q s) (k-s) (A.loom s) F (β s) 0)
include Frst Y p a Z hh hs he ht

-- single-step assertions independent of reach to top once charged recurrence established
omit ht
private lemma one_step (i : ℕ) (g : i < s)
    (u : Cleared W h (Yb (i+1)) (Xc (i+1)) (Xs (i+1)) (k-(i+1)) (Xr (i+1)) (Z.G (i+1)) (β (i+1)) (Z.v (i+1))) :
    Cleared W h ((Yb i)/1000) (Xc i) (Xs i) (k-i) (Xr i) (Z.G i) (β i) (Z.v i) ∧ Continuous (Z.posted i) ∧
      Continuous (Z.wave i) ∧ ∀ t, |Z.posted i t| ≤ D (Xh i) ∧ ‖Z.wave i t‖ ≤ R0 (Xh i) ∧
        |(Z.v i t).re-(Z.v (i+1) t).re| ≤ C (Xh i)*sites (cell m B R.L i) ∧
        ∀ y:Orbit (cell m B R.L i), Rue.FleetS (A.T.a i).threshold y.1 → denZ (Z.launch i t) U (A.loom i) y =
           stove U (A.loom i) (Z.guess (i+1) t) (A.loom (i+1)) (X₀ i).G ((X₀ i).step V) q J.d (Z.wave i t).val y := by
  have hi : i < k := lt_of_lt_of_le g hs
  let j:= i+1
  have Q := a.request i hi
  have hz : (X₀ i).lag=k-j := (by dsimp only [Spine.address,j]; omega)
  obtain ⟨hp,hq,H,hm⟩ := step_query hh (a.clocks i) Q (a.certified Y i hi)
      (p _ _ _ _ _ _ (a.late.trans (Vale.crown ..)) Q) (hat_step i ▸ hz.symm ▸ u)
      (he j g).1 (hat_step i ▸ (he j g).2) (he i g.le).1
  refine ⟨?_,hp,hq,?_⟩
  · change Cleared _ _ _ _ _ ((X₀ i).lag+1) _ _ _ _ at hm
    rw [show k-i = (X₀ i).lag+1 by rw [hz]; unfold j; omega, funext (Z.step i g), funext (Z.offsets i g)]; exact hm
  intro t; specialize H t
  refine ⟨H.1,H.2.1, by rw [Z.offsets i g]; exact H.2.2.1,?_⟩
  have hL : Z.launch i t= (X₀ i).buildOut V (Xc i) (β (i+1) t+Xm i-Z.posted i t) ((A.op P i).realArr (β (i+1) t) (Z.G (i+1) t)) ((A.op P i).offset (β (i+1) t) (Z.G (i+1) t) (Z.v (i+1) t)) := by
    rw [launch,Z.step i g,Z.offsets i g,Location.buildOut,hz]; congr 2; unfold j; omega
  have ht : Z.guess (i+1) t= (X₀ i).buildIn V (Xc (i+1)) (β j t) (Z.G (i+1) t) (Z.v (i+1) t) := by rw [guess,Location.buildIn,hz]; rfl
  rw [hL,ht]; exact H.2.2.2
include ht
lemma charged (i : ℕ) (v : i ≤ s) :
    Cleared W h (Yb i) (Xc i) (Xs i) (k-i) (Xr i) (Z.G i) (β i) (Z.v i) := by
  rcases v.eq_or_lt with u|u
  · subst i; rw [Z.fromTop,Z.fromZero]; exact ht
  have hx := (Z.one_step Y p a hs hh he _ u (charged _ u)).1
  exact hx.up _ (div_le_self (a.clocks i).leaf.le (by norm_num))
 termination_by s-i

theorem paid (i : ℕ) (v : i<s) :
    Cleared W h ((Yb i) / 1000) (Xc i) (Xs i) (k-i) (Xr i) (Z.G i) (β i) (Z.v i) ∧ Continuous (Z.posted i) ∧
      Continuous (Z.wave i) ∧ ∀ t, |Z.posted i t| ≤ D (Xh i) ∧ ‖Z.wave i t‖ ≤ R0 (Xh i) ∧
        |(Z.v i t).re-(Z.v (i+1) t).re| ≤ C (Xh i)*sites (cell m B R.L i) ∧
        ∀ y:Orbit (cell m B R.L i), Rue.FleetS (A.T.a i).threshold y.1 → denZ (Z.launch i t) U (A.loom i) y =
           stove U (A.loom i) (Z.guess (i+1) t) (A.loom (i+1)) (X₀ i).G ((X₀ i).step V) q J.d (Z.wave i t).val y :=
  Z.one_step Y p a hs hh he _ v (Z.charged Y p a hs hh he ht _ v)
end Cooling
end LocalLimit
end YM.CF.Py.Rate
