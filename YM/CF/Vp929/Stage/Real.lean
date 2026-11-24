import YM.CF.Vp929.Stage.Branch

/-! Queries and real outputs from a branch. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
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
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
namespace Branch
variable (A : Branch W m k x N0)
local notation "M" => cell m B R.L
local notation "X" => hat R.L x
local notation "B'" => A.toSpine.pilot x
local notation "Y" => A.toSpine.address

structure RealQ (b : Bet k) : Prop where
  paid : b ∈ A.BetaArea 1 0
  im : b.Real
structure Solved (z : ℝ) (b : Bet k) : Prop extends RealQ A b where
  fixp : IsFixedPt (updateBet B' (A.fee P) z) b
abbrev chargeLevel (b : Bet k) (i : ℕ) := (A.corr P b i).1
def offset (b : Bet k) (i : ℕ) : ℂ := if _ : i<k then (A.op P i).offset (b.read (i+1)).re (A.chargeLevel P b (i+1)) (offset b (i+1)) else 0
termination_by k-i
abbrev gram (b : Bet k) (i : ℕ) := construct (A.T.a i) (V.L.path (k-i)) K.top.clip (A.last.Q i) (b.read i).re (A.chargeLevel P b i) (A.offset P b i)
abbrev wave (b : Bet k) (i : ℕ) : SpaceM := (A.op P i).wave (b.read (i+1)).re (A.chargeLevel P b (i+1))
abbrev active (b : Bet k) (i : ℕ) := (A.op P i).output V (Y i) (A.T.a i) (b.read (i+1)).re (A.chargeLevel P b (i+1)) (A.offset P b (i+1))
lemma gram_fine (b : Bet k) (i : ℕ) (hi : i<k) : A.gram P b (i+1)=(Y i).buildIn V (A.T.a (i+1)) (b.read (i+1)).re (A.chargeLevel P b (i+1)) (A.offset P b (i+1)) := by
  unfold gram Location.buildIn; dsimp [Spine.address]; congr 2; omega

variable {A P} {b : Bet k}
lemma RealQ.coeRe (p : RealQ A b) (i : ℕ) (hi : i≤k) : ((b.read i).re:ℂ)=b.read i := by apply Complex.ext <;> simp [p.im i hi]
namespace Bon
variable (a : Bon J q h D delay A) (p : Service V U W J q h D C R0 P N0 delay) (g : RealQ A b)
include a p g
lemma area (i) : b∈ A.BetaArea 3 i := (a.posts p).expand_area g.paid _
lemma both_real (i : ℕ) (hi : i≤k) : A.corr P b i=(A.chargeLevel P b i,0) := Prod.ext rfl (a.corr_real p i hi (a.area p g i) (fun j _ w=> g.im j w))
lemma charged (i) (hi : i≤ k): A.ChargedAt h i (A.chargeLevel P b i) (dleaf R.L (X i)/1000):= (a.costs p i hi (a.area p g i)).1
lemma beta_ok (i) (hi : i≤k) : entersReal (X i) (b.read i).re ∧ enters (X i) ((b.read i).re:ℂ) := by
  rw [g.coeRe i hi]; have H:= ((a.clocks i).enroll (a.pilots i hi).1 (a.pilots i hi).2 (a.area p g i i le_rfl hi)); exact ⟨H.2.2,H.1⟩
lemma corr_successor (i : ℕ) (hi : i<k) : A.chargeLevel P b i = (A.op P i).realArr (b.read (i+1)).re (A.chargeLevel P b (i+1)) := by
  unfold Operation.realArr; rw [← a.both_real p g (i+1) hi, g.coeRe (i+1) hi]; exact congrArg Prod.fst (A.corr_step P b i hi)
lemma fee_eq (i : ℕ) (hi : i<k) : ((A.op P i).posted (b.read (i+1)).re (A.chargeLevel P b (i+1)):ℂ)= A.fee P i b := by
  unfold Operation.posted; rw [← a.both_real p g (i+1) hi, g.coeRe (i+1) hi]; exact Complex.ext rfl ((a.posts p).real _ hi b (a.area p g _) (fun j _ h=>g.im j h)).symm
lemma active_eq (i : ℕ) (hi : i<k) : A.active P b i = construct (A.T.a i) (V.L.path (k-i)) K.top.clip (A.last.Q i) ((A.active P b i).beta) (A.chargeLevel P b i) (A.offset P b i) := by
  rw [a.corr_successor p g i hi]; rw [offset.eq_1 P A b i]
  dsimp only [active,Operation.output,Location.buildOut,Spine.address]; rw [dif_pos hi, show k-1-i+1=k-i by omega]
lemma success (i : ℕ) (hi : i<k) (e : (A.active P b i).beta=(b.read i).re) : A.active P b i=A.gram P b i := by nth_rw 1 [a.active_eq p g i hi]; exact congrArg (fun x=> construct _ _ _ _ x _ _) e
lemma active_law (i : ℕ) (hi : i<k) :
    ‖A.wave P b i‖ ≤ R0 (X i) ∧ Canonical (A.freq i) (A.active P b i) K.j ∧
    (∀ y, Rue.FleetS (A.T.a i).threshold y.1 → denZ (A.active P b i) U (A.loom i) y =
            stove U (A.loom i) (A.gram P b (i+1)) (A.loom (i+1)) (Y i).G ((Y i).step V) q J.d (A.wave P b i).val y) ∧
    |(A.offset P b i).re-(A.offset P b (i+1)).re| ≤ C (X i)*sites (M i) := by
  rw [A.gram_fine P b i hi]; rw [offset.eq_1 P A b i]; rw [dif_pos hi]
  exact ((a.certified p i hi).real _ _ _ (hat_step i ▸ (a.beta_ok p g (i+1) hi).2) (a.flow (a.charged p g (i+1) hi))).2.2

omit g
variable {z : ℝ} (s : Solved P A z b)
include s
lemma paysStep (i : ℕ) (hi : i<k) : (A.active P b i).beta=(b.read i).re := by
  let F:= updateBet B' (A.fee P) z b; have H (j) (u : j ≤ k) : b.read j = (B' j:ℂ)+(z:ℂ)+∑ l∈range j,A.fee P l b := by
    rw [Bet.read_of_le b u]; exact congrFun (show b=F from s.fixp.symm) _
  have he : (b.read (i+1)).re=(b.read i).re-A.last.move i+(A.op P i).posted (b.read (i+1)).re (A.chargeLevel P b (i+1)) := by
    apply Eq.trans (b:= (b.read i-(A.last.move i:ℂ)+A.fee P i b).re)
    · rw [H (i+1) hi,H i hi.le,Finset.sum_range_succ]; rw [A.toSpine.pilot_move i]; apply congrArg; push_cast; ring
    rw [← a.fee_eq p s.toRealQ i hi]; simp
  change ((b.read (i+1)).re + A.last.move i - _) = _; linarith
lemma partition (i : ℕ) (hi : i<k) : partitionZ (A.gram P b i) U (A.loom i) = partitionZ (A.gram P b (i+1)) U (A.loom (i+1)) := by
  let t:= A.active P b i; let g:= s.toRealQ
  have he:= (a.active_law p g i hi).2.2.1; rw [A.gram_fine P b i hi] at he
  rw [← a.success p g i hi (a.paysStep p s i hi), A.gram_fine P b i hi]
  have h:= matched_of_enters (a.clocks (i+1)) (a.beta_ok p g (i+1) hi).2
  exact Request.balance (a.request i hi) (hat_step i ▸ h) (a.flow (a.charged p g (i+1) hi)) (A.wave P b i) he
omit a p in
lemma anchor : b.read 0 = (x:ℂ)+(z:ℂ) := by
  rw [Bet.read_of_le b (by omega)]; let j:Fin (k+1) := 0; calc
    _ = updateBet B' (A.fee P) z b j := congrFun s.fixp.symm j
    _ = _ := by simp [updateBet,j, A.toSpine.pilot_zero]

omit s
include g
lemma isSolved (he : b.read 0=(x:ℂ)+(z:ℂ)) (t : ∀ i<k, (A.active P b i).beta=(b.read i).re) : Solved P A z b := by
  refine ⟨g,funext fun ⟨i,h⟩=> Eq.symm ?_⟩; unfold updateBet; dsimp only; let D:= A.fee P
  rw [← Bet.read_of_le b (i:=i) _]; swap; · omega
  induction i with
  | zero=> rw [he,A.toSpine.pilot_zero]; simp
  | succ i ih=>
     have ht:i<k:=by omega
     have e:= t i ht; let zY:= (A.op P i).posted (b.read (i+1)).re (A.chargeLevel P b (i+1)); change (b.read (i+1)).re + A.last.move i - zY = _ at e
     have E: b.read (i+1)= b.read i-(A.last.move i:ℂ)+A.fee P i b := by
       apply Complex.ext
       · rw [← a.fee_eq p g i ht]; simp; linarith
       rw [← a.fee_eq p g i ht]; simp [g.im _ ht,g.im _ ht.le]
     rw [E, ih (by omega), sum_range_succ]; rw [A.toSpine.pilot_move i]; push_cast; ring
end Bon
end Branch
end YM.CF.Py.Rate
