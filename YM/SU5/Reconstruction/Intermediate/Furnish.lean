import YM.SU5.Reconstruction.Intermediate.Solver
import YM.CF.Buffered.Shooting
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
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false

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
variable (D)
abbrev staff : Vestal m B R.L := fun i=> X i
abbrev salary (i:ℕ) := (cooled P A s D F).wave i u
variable {D}
-- temperature range
include a τ in
lemma boundedOf {i:ℕ}(p:i ≤ s) : 0≤ temper A s D i u ∧ temper A s D i u ≤ 2*Xh i :=
 let g:= a.clocks i
 let b:= matched_of_enters g (accepted A s a i (p.trans τ) u).2
 ⟨(by linarith [b.1, g.grade]),b.2⟩
include H pP a hh τ pS
open FullBill
lemma envelope_ready {i:ℕ}(p:i ≤ s): Envelope (denZ (staff P A s D F u i) U (Xr i)) := by
 let y:= (cooled P A s D F).G i
 have he:= (resources P A s a F H pP τ hh pS i p).cost u
 have hv:= (a.can.cape i).paid; exact denInt W {hv with paid:=fun i=>(hv.paid i).shrink J.hr.le} _ (J.gran.trans (a.can.cape i).size) _ _ (he.toCost.lot (β i u) ((Z).v i u))

open Buffered
local notation "Wb" => steps V m B k
private lemma placedF (i:ℕ)(g:i<s): X (i+1) = (X₀ i).buildIn V (Xc (i+1)) (β (i+1) u) ((Z).G (i+1) u) ((Z).v (i+1) u) := by
 unfold Cooling.guess Location.buildIn; congr 2; change k-(i+1)=k-1-i; omega
private lemma placedC (i:ℕ)(g:i<s): X i = (X₀ i).buildOut V (Xc i) (β i u) ((Z).G i u) ((Z).v i u) := by
 unfold Cooling.guess Location.buildOut; congr 2; change k-i=k-1-i+1; omega
private lemma ready_input (i:ℕ)(g:i<s) : Charged (Xc (i+1)) (Xs (i+1)) K.j R.L.val h (3*dleaf R.L (Xh i)) ((cooled P A s D F).G (i+1) u) := by
 have hp:= a.clocks i; apply ((resources P A s a F H pP τ hh pS _ g).cost u).mono; have hv:= hp.leaf_mono (Xh (i+1)) (hat_mono (by omega)); linarith [hp.leaf]
include r
lemma cashier : Buffered.Granted U (staff P A s D F u) A.loom q J.d s (salary P A s D F u) (Wb) R.J:= by
 refine ⟨?_, ?_, ?_, ?_, fun i _=>a.can.isle i,?_⟩
 · intro i _; unfold steps; rw [V.L.patch_x]; exact V.L.cloth
 · intro i _; exact Hom.rat_eq (show (Vale.apt m B R.L i).count= _ from (V.L.lent_L ..).symm)
 · intro i _; exact congrArg Patch.J (V.L.patch_x (x:=kint m B R.L i) (k-1-i)) -- check
 · intro i g
   change Nonempty (Girt.BaseL U _ (X (i+1)) _ _ _ _)
   rw [placedF P A s F u H pP a hh τ pS _ g]
   have hp:= ready_input P A s F u H pP a hh τ pS i g
   let Y:= X (i+1); have hi:= (a.request i (lt_of_lt_of_le g τ)); let T:= hi.statv (β (i+1) u) ((Z).G (i+1) u) 0 ((Z).v (i+1) u) ((hat_step i) ▸ matched_of_enters (a.clocks (i+1)) (accepted A s a (i+1) (le_trans g τ) u).2)
   exact rig V U W J q hi.rocket _ hi.roof _ T.sound (X₀ i).count (ward_m (V.L.mood ((X₀ i).lag)) (hp.toCost.lot _ _))
 intro i g y v; have h' := ((Intermediate.earns P A s a F H pP τ hh pS i g).2.2.2 u).2.2.2 y (show Rue.FleetS (Xc i).threshold y.1 from v)
 rw [Settles.pays P A s F r _ g] at h'; exact h'.symm
lemma reserves_bind {i:ℕ}(p:i<s): partitionZ (X i) U (Xr i) = partitionZ (X (i+1)) U (Xr (i+1)):= by
 have he:∀ y,Rue.FleetS (Xc i).threshold y.1 → Scree.stove U (Xr i) (X (i+1)) (Xr (i+1)) (X₀ i).G (Wb i) q J.d (salary P A s D F u i).val y=denZ (X i) U (Xr i) y:=fun y h=> (cashier P A s F u H pP a hh τ pS r).wears _ p y h
 rw [placedC P A s F u H pP a hh τ pS _ p,placedF P A s F u H pP a hh τ pS _ p] at he ⊢
 exact Request.balance (a.request i (lt_of_lt_of_le p τ)) ( (hat_step i) ▸ matched_of_enters (a.clocks (i+1)) (accepted A s a _ (le_trans p τ) u).2) (ready_input P A s F u H pP a hh τ pS _ p) _ (fun y h=> (he y h).symm) -- resolve
lemma fromPivot {i:ℕ}(e:i≤ s): partitionZ (X 0) U (Xr 0)=partitionZ (X i) U (Xr i):=by induction i with | zero=>rfl | succ i ih=> exact (ih (by omega)).trans (reserves_bind P A s F u H pP a hh τ pS r e)
end Intermediate
end LocalLimit
end YM.CF.Py.Rate
