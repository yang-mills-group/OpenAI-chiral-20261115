import YM.CF.Vp929.Stage.Spine
import YM.CF.Vp929.Budget.Arith
import YM.CF.Vp929.Analysis.Shooting

/-!
# Branches

Recursive construction of corrections at independently guessed betas; the last fee and charge
are NOT variables in this continuation.
-/
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
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi)
  (h : ℝ) (D C R0 : ℝ → ℝ) (delay : ℝ) {x : ℝ} {N0 k : ℕ} (P : Prescription R B)

structure Branch (W : GivenX V U) (m : Side) (k : ℕ) (x : ℝ) (N0 : ℕ) extends Spine W m k where
  T : Month x 1 6 2 N0 V W
  start : ℂ → Pair (Corr (cell m B R.L k))

namespace Branch
variable (A : Branch W m k x N0)
local notation "M" => cell m B R.L
local notation "X" => hat R.L x
local notation "B'" => A.toSpine.pilot x
abbrev op (i : ℕ) := P _ _ (A.toSpine.address i) (X i) (A.T.a i) (A.T.a (i+1))
abbrev BetaArea (a : ℝ) (l : ℕ) : Set (Bet k) := area (fun i=> strip (X i)) B' a l
abbrev ChargedAt (i : ℕ) (F : Corr (M i)) (δ : ℝ) := Charged (A.T.a i) (A.last.Q i) K.j R.L.val h δ F
abbrev allCorr (i : ℕ) (F : Pair (Corr (M i))) : Prop := Both (Charged (A.T.a i) (A.last.Q i) K.j R.L.val h (dleaf R.L (X i)/1000)) F

def corr (b : Bet k) (i : ℕ) : Pair (Corr (M i)) :=
  if hi : i<k then (A.op P i).arrays (b.read (i+1)) (corr b (i+1))
  else if ht : k=i then ht ▸ A.start (b.read i) else 0
termination_by k-i

theorem corr_step (b) (i) (hi : i<k) : A.corr P b i=(A.op P i).arrays (b.read (i+1)) (A.corr P b (i+1)) := by rw [corr,dif_pos hi]
theorem corr_top (b) : A.corr P b k=A.start (b.read k) := by rw [corr,dif_neg (lt_irrefl _),dif_pos rfl]

def fee (i : ℕ) (b : Bet k) := (A.op P i).Δ (b.read (i+1)) (A.corr P b (i+1))

structure Bon : Prop where
  can : A.toSpine.Can J q A.T
  late : delay ≤ x
  prices : ∀ y ≥ x, Prices R.L D y
  pilots (i : ℕ) : i ≤ k → (3/4:ℝ) * X i ≤ B' i ∧ B' i ≤ 3/2*X i
  cap (b : ℂ) (hb : enters (X k) b) : A.allCorr h k (A.start b) ∧ (b.im=0 → (A.start b).2=0)
  film (S : Set ℂ) : IsOpen S → ∀ b : ℂ → ℂ, (∀ z∈S, enters (X k) (b z)) → DifferentiableOn ℂ b S → HoloCorr S (A.start ∘ b)

namespace Bon
variable {A J h q D delay} (a : Bon J q h D delay A)
variable {P R0 C} (p : Service V U W J q h D C R0 P N0 delay)
include a
lemma request (i : ℕ) (hi : i<k) : Location.Request V U W J q (A.toSpine.address i) N0 (X i) (A.T.a i) (A.T.a (i+1)) := a.can.request i hi
include p in
lemma certified (i : ℕ) (hi : i<k) : Certified V U W J q h (X i) (A.T.a i) (A.T.a (i+1)) (R0 (X i)) (D (X i)) (C (X i)) (A.toSpine.address i) (A.op P i) := p.provides _ _ _ _ _ _ (a.late.trans (Vale.crown ..)) (a.request i hi)
lemma clocks (i : ℕ) : Prices R.L D (X i) := a.prices _ (Vale.crown ..)
lemma entersBet {b : Bet k} {l i : ℕ} (e : b ∈ A.BetaArea 3 l) (v : l ≤ i) (u : i ≤ k) : enters (X i) (b.read i) := ((a.clocks i).enroll (a.pilots i u).1 (a.pilots i u).2 (e i v u)).1
lemma flow {i} {l} (e : ChargedAt h A (i+1) l (dleaf R.L (X (i+1))/1000)) :
    ChargedAt h A (i+1) l (3*dleaf R.L (X i)) := e.mono (by
      have he:= (a.clocks i).leaf_mono (X (i+1)) (hat_mono (by omega))
      linarith [(a.clocks i).leaf])
omit a in
private lemma area_higher {b : Bet k} {i j : ℕ} {u : ℝ} (e : b ∈ A.BetaArea u i) (p : i ≤ j) : b ∈ A.BetaArea u j := fun l v s=> e l (p.trans v) s
include p
lemma costs (i : ℕ) (hi : i ≤ k) {b} (hb : b∈ A.BetaArea 3 i) : A.allCorr h i (A.corr P b i) := by
  rcases hi.eq_or_lt with e|e
  · subst i; rw [corr_top]; exact (a.cap _ (a.entersBet hb le_rfl le_rfl)).1
  have g:= costs (i+1) e (area_higher hb (Nat.le_succ i))
  rw [corr_step P A b i e]
  exact ((a.certified p i e).cost (b.read (i+1)) (A.corr P b (i+1)) (hat_step i ▸ a.entersBet hb (Nat.le_succ i) e) ⟨a.flow g.1,a.flow g.2⟩).1
termination_by k-i
lemma corr_real (i : ℕ) (hi : i ≤ k) {b} (hb : b∈ A.BetaArea 3 i)
    (r : ∀ l : ℕ, i ≤ l → l ≤ k → (b.read l).im=0) : (A.corr P b i).2=0 := by
  rcases hi.eq_or_lt with e|e
  · subst i; rw [corr_top]; exact (a.cap _ (a.entersBet hb le_rfl le_rfl)).2 (r _ le_rfl le_rfl)
  have h:=area_higher hb (Nat.le_succ i); let t:= b.read (i+1)
  have g:= a.flow (a.costs p _ e h).1
  have E:A.corr P b (i+1)= ((A.corr P b (i+1)).1,0) := Prod.ext rfl (corr_real _ e h (fun j v w=>r j (Nat.le_trans (by omega) v) w))
  have he: (t.re:ℂ)=b.read (i+1) := by apply Complex.ext <;> simp [t,r _ (Nat.le_succ i) e]
  rw [corr_step P A b i e]; nth_rw 1 [E]; rw [← he]; exact ((a.certified p i e).real _ _ 0 (hat_step i ▸ (he ▸ a.entersBet hb (Nat.le_succ i) e)) g).1
termination_by k-i
lemma corr_holo (S : Set ℂ) (hs : IsOpen S) {b : ℂ → Bet k} (u : DifferentiableOn ℂ b S)
    (i : ℕ) (hi : i ≤ k) (h : Set.MapsTo b S (A.BetaArea 3 i)) : HoloCorr S fun z=> A.corr P (b z) i := by
  have hv (i) : DifferentiableOn ℂ (fun z=> (b z).read i) S := differentiableOn_pi.mp u _
  rcases hi.eq_or_lt with e|e
  · subst i; simp only [corr_top]; exact a.film S hs (fun z=>(b z).read k) (fun z hz=> a.entersBet (h hz) le_rfl le_rfl) (hv _)
  have H : Set.MapsTo b S (A.BetaArea 3 (i+1)):= fun z hz=> area_higher (h hz) (Nat.le_succ i)
  simp only [A.corr_step P _ i e]; apply ((a.certified p i e).analytic S hs (fun z=> (b z).read (i+1)) (fun z=> A.corr P (b z) (i+1)) _ (hv _) (corr_holo S hs u (i+1) e H)).1
  intro z hz; have ht:= a.costs p _ e (H hz); exact ⟨hat_step i ▸ a.entersBet (H hz) le_rfl e,a.flow ht.1,a.flow ht.2⟩
termination_by k-i

lemma posts : Posts (fun i=> strip (X i)) (fun i=> D (X i)) B' (A.fee P) := by
  refine ⟨fun i=> strip_pos (a.clocks i).grade,fun i=>(a.clocks i).bank,fun i j q=> (a.clocks i).increase _ (hat_mono q),fun i=> ?_, prices_sum a.prices, ?_, ?_, ?_⟩
  · rw [hat_step]; exact (a.clocks i).fast
  · intro i hi b hb; have t:= a.costs p (i+1) hi hb; exact ((a.certified p i hi).cost _ _ (hat_step i ▸ a.entersBet hb le_rfl hi) ⟨a.flow t.1,a.flow t.2⟩).2
  · intro i hi b hb r
    let t:= b.read (i+1); have E:A.corr P b (i+1) = ((A.corr P b (i+1)).1,0) := Prod.ext rfl (a.corr_real p _ hi hb r)
    have he: (t.re:ℂ)=b.read (i+1) := by apply Complex.ext <;> simp [t,r _ (Nat.lt_succ_self i) hi]
    unfold fee; nth_rw 1 [E]; rw [← he]; exact ((a.certified p i hi).real _ _ 0 (hat_step i ▸ (he ▸ a.entersBet hb le_rfl hi)) (a.flow (a.costs p _ hi hb).1)).2.1
  intro S hs i hi f hf g; unfold fee; apply ((a.certified p i hi).analytic S hs (fun z=> (f z).read (i+1)) (fun z=> A.corr P (f z) (i+1)) _ (differentiableOn_pi.mp g _) (a.corr_holo p S hs g _ hi hf)).2
  intro z hz; have t:=a.costs p _ hi (hf hz); exact ⟨hat_step i ▸ a.entersBet (hf hz) le_rfl hi,a.flow t.1,a.flow t.2⟩
end Bon
end Branch
end YM.CF.Py.Rate
