import YM.CF.Paxos.Port
import YM.CF.Buffered.FixedPeriod

/-!
# History hypotheses on physical cutoff data

CapP is the actual Py.Brioche on this data. Donor in `Shots`: needed
history conditions on the paired donor at this period, including on smaller
(`-`) tori after gluing; wear, budget, same non-wave schedule inputs, no
hypothesis that offset or wave outputs agree Cap vs donor. Report in
The construction uses history-building, p-delt and pc-low. E.g.
warm LotR needs just finite expenditure, not Provide-K-profile bounds. Less
restrictive here than manuscript choice; no *existence* result attempted in
this file. All history equations / inequalities used stated on the concrete
choices. See the corollary proof, 'any ... with the prescription'.

Use `Transfer` and `FixedPeriod` on these data as in the proof.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
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
variable {K:Teller SU.group} {R:Patch} {L:ChartRatio SU.group} (V:Grace K R L)
variable {B m M : Side} {d x : ℝ} {P: Grasp V.U B d} {W: GivenX V P} {a : ℝ} {p i N0 : ℕ} (T:Month x a i p N0 V W) (J:Robes M V W) (η:Chi)
def steps (m B : Side) (n : ℕ) : Steps m B R.L := fun j=> V.L.op (n-1-j) (kint m B R.L j)
variable (O: T.q ≤ m.val) (S: Cape m B R.L) (n : ℕ) (X Y : Vestal m B R.L) (q r : ℕ → Haro.SpaceM) (β θ ν : ℕ→ℝ) (h : ℝ) (R0 δ : ℝ→ℝ)
local notation "A" => steps V m B n
structure Shots : Prop where
  sharp : Brioche V a p i N0 T m O n β J η h R0 δ X S q θ
  -- matched per-period hot data; use ms general n, not Tar/trunkY specialization
  hue (j) (t:j≤n) : CloseC (hueR V a p i N0 T m O n β j) (Y j)
  wear (j:ℕ) (t:j<n) (w:Orbit (cell m B R.L j)) (l:Rue.FleetS (Y j).p.threshold w.1) : Scree.stove P (S j) (Y (j+1)) (S (j+1)) (apt m B R.L j) (steps V m B n j) η J.d (r j).val w=denZ (Y j) P (S j) w
  matchY (j) (t:j ≤ n) : matchedX (hat R.L x j) (Y j).beta
  shiftY(j:ℕ) : j<n → ((Y (j+1)).beta - β (j+1)) - ((Y j).beta - β j) = ν j
  pivot : (Y 0).beta=x
  earnY(j:ℕ)(t:j≤ n) : ∃ w a, LotR (Y j) h w a
  -- same launch with I and offset modification, recall strengthened pins (not
  -- claiming to infer original Lives_B from glued choices)
  topForm : ∃ E : RegBudget (cell m B R.L n), ∃ s : ℝ, Y n=Chaff.fulvia E s (Vale.launch V.L (Y n).beta (T.a n) _)
  heat : ∃ p : Donor P Y S n, p.clip=K.top.clip ∧ p.heat=(Pressure.radiusB (hat R.L x n):ℝ)
namespace Shots
variable {V T J η O S n X Y q r β θ ν h R0 δ}
-- inspect argument order
variable (g : Shots V T J η O S n X Y q r β θ ν h R0 δ)
include g
lemma cap_pivot : (X 0).beta=x:=g.sharp.note.color.trans g.sharp.day.unit
lemma cap_launch : X n=Vale.launch V.L (X n).beta (T.a n) _ := by
  nth_rw 1 [g.sharp.note.boot, Py.hue_top]; rfl
lemma cap_density (p' : K.top.clip.direct≤1) (x : Orbit (cell m B R.L n)) : denZ (X n) P (S n) x=Vale.capP (K:=K) P (X n).beta (T.a n) x.1 := (Brioche.hot V O J η h g.sharp p').2 _
include g
lemma cap_grant : Granted P X S η J.d n q A R.J := by
  let w:=g.sharp
  refine ⟨fun k _ => (Brioche.drives V O J η h w k).2, fun k _ => (Brioche.drives V O J η h w k).1, fun k _=> congrArg Patch.J (V.L.patch_x (x:=kint m B R.L k) ..), fun k u=> Brioche.us V O J η h w k u, fun k u=> ?_, fun k u=> w.note.wear k u⟩
  have he:(X k).p= T.a k:= (w.note.owns k u).width.symm; rw [he]; exact w.mark k
-- check on these same, possibly glued, data. Adapts `Tar/Joust.purse` grant calculation.
lemma warm_grant : Granted P Y S η J.d n r A R.J := by
  let w:=g.sharp; refine ⟨fun k _=>(Brioche.drives V O J η h w k).2,fun k _=>(Brioche.drives V O J η h w k).1,fun k _=> congrArg Patch.J (V.L.patch_x (x:=kint m B R.L k) ..), fun j u=> ?_, fun k u=> ?_, g.wear⟩
  · let G':=(apt m B R.L j); let T':=(V.L.mint (n-1-j) (kint m B R.L j)); let s:= A j
    have hQ := sized_F (N:=mesh m R.L j) (P:=mesh m R.L (j+1)) (B:=B) (S:=s) (T:=T') V a p i N0 T m O n β w.day j _ (g.hue _ u) u (g.matchY _ u)
    obtain ⟨t,u',f⟩:=g.earnY _ u; exact rig V P W J η (w.roof j) (S _) (w.roof _).paid _ hQ.sound rfl (ward_m (show (Y (j+1)).path.Bounds (Y (j+1)).funds _ _ _ from by rw [hQ.move,hQ.coinY]; exact hQ.hunt.up) f)
  have he:(Y k).p=T.a k:= (g.hue k u).width.symm; rw [he]; exact w.mark k
lemma atComparison {b₀ : ℕ} {C Mg : ℝ} (u : 0<n) (v : Delta P (X 0) (Y 0) (S 0) (Burn.bill m.val n b₀ Mg)) (t : Burn.presrec m.val C ≤ ‖vac0 P (Y 0) (S 0)‖) (F G : ℕ → Vestal m B R.L) (p₁ : F n=X) (p₂ : G n=Y) : AtUV P S F G b₀ C Mg n := by subst X Y; exact ⟨v,t,(g.warm_grant.paid 0 u).1,(g.cap_grant.paid 0 u).1,(g.cap_grant.paid 0 u).2⟩
end Shots
end YM.CF.Buffered
