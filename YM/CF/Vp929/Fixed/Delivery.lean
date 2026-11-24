import YM.CF.Vp929.Fixed.Calendar

set_option autoImplicit false
set_option maxHeartbeats 1100000
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
/-- An actual MeterQ cutoff (with canonical tests at every step). -/
structure Parcel where
  pilot : ℕ → ℝ
  gram : Vestal m B R.L
  wave : ℕ → SpaceM
  fee : ℕ → ℝ
  due : Due V 1 2 6 N0 T m ht k pilot
  pull : Pull_P V 1 2 6 N0 T m ht k pilot J q h R0 D S gram wave fee
  pay (i : ℕ) (u : i<k) : ‖Complex.exp (gram (i+1)).v‖*ρ i ≤ ‖Complex.exp (gram i).v‖
  -- record the upper bound too (e.g. for downstream fixed level use)
  perSite (i : ℕ) (u : i<k) : |(gram i).v.re-(gram (i+1)).v.re| ≤ C (hat R.L x i)*sites (cell m B R.L i)
  balance (i : ℕ) (u : i≤k) : partitionZ (gram i) U (S i)=partitionZ (gram k) U (S k)
  canonical (i : ℕ) (u : i<k) : Frequency R.L (cell m B R.L i) (f i) ∧ Canonical (f i) (gram i) K.j
abbrev rho (X : ℝ) (c : ℝ→ℝ) (R : Patch) (m B : Side) (i : ℕ) := Real.exp (-(c (hat R.L X i))*sites (cell m B R.L i))
def CanCape {V : Grace K R L} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (m : Side) (S : Cape m B R.L) := ∀ j:ℕ,RocketV V (mesh m R.L j) (mesh m R.L (j+1)) U W J (S j) (apt m B R.L j) q
lemma cape_exists {m : Side} (hh : J.h ≤ m.val) : ∃ S : Cape (m*N) B R.L, CanCape J q (m*N) S := by choose X hx using fun i=> form_t V U W J q hh i; exact ⟨X,hx⟩
abbrev ActualSpine := (⟨W.arm (T.large.trans ht) k,S,f⟩: Spine W m k)
abbrev Actual := Branch.unchanged (ActualSpine T ht S f k) T
variable {J q h D C R0 T S ρ f k}
local notation "M" => cell m B R.L
local notation "X" => hat R.L x
lemma hardCape {F_:(s:Side)→Scree.Loom s→Prop}(pF:RackedΛ F_ J) (q:Chi){C:Side}(u:J.h≤ C.val) :∃ S:Cape (C*N) B R.L, CanCape J q (C*N) S ∧ ∀ i,F_ _ (S i):=by
 have he(i):∃ WV:Scree.Loom (cell (C*N) B R.L i), RocketV V (mesh (C*N) R.L i) (mesh (C*N) R.L (i+1)) U W J WV (apt (C*N) B R.L i) q ∧ F_ _ WV:=by
    refine gowns pF q (mesh C R.L i) _ _ (Month.ruler ..) (Grace.Robes.stretch J u _) ?_ _ rfl
    rw [Month.ruler, mesh_succ]
 choose S P H using he; exact ⟨S,P,H⟩
lemma actual_can {z delay : ℝ} {ht : T.q ≤ m.val} (p : Usable (D:=D) V W J N0 z delay T) (hh : CanCape J q m S)
    (g : 61 ≤ m.val) (v : ∀ i, Frequency R.L (cell m B R.L i) (f i)) (k) :
    (Actual T ht S f k).Bon J q h D delay := Branch.unchanged_build ⟨ht,g,hh,v,p.walk.pole,p.walk.isle⟩ p.walk.prices p.walk.late (W.pose (T.large.trans ht) k) p.music₀

namespace Parcel
variable {delay : ℝ} {P : Prescription R B}
open Branch
variable (a : Bon J q h D delay (Actual T ht S f k)) (H : Service V U W J q h D C R0 P N0 delay)
    {b} (s : Solved P (Actual T ht S f k) 0 b)
include a H s
private lemma pilot_match (i : ℕ) (hi : i≤k) : matchedX (hat R.L x i) ((ActualSpine T ht S f k).pilot x i) := by
  have e:= a.pilots i hi; change 3/4*hat _ _ _≤ (ActualSpine T ht S f k).pilot x i ∧ _ at e
  constructor <;> linarith [(a.clocks i).grade,e.1,e.2]
/-- Exactly the prepared history: expose that the `Parcel` uses the same transfer
 map (not just a Wear identity). Needed e.g. to use Lemma limsup on a cutoff at which comparing
 real trajectories chosen by the stage prescription. -/
structure Exact (P:Prescription R B)(p:Parcel J q h D C R0 T ht S ρ f k) (b:Bet k) : Prop where
   pilotZ : p.pilot = (ActualSpine T ht S f k).pilot x
   gramZ : p.gram = Branch.gram P (Actual T ht S f k) b
   waveZ : p.wave = (Actual T ht S f k).wave P b
   feeZ : p.fee = fun i => ((Actual T ht S f k).fee P i b).re

section
variable {ht}
/-- With this `P`, a genuine prepared history. -/
def Prepared (P:Prescription R B) (e:ℝ) (p:Parcel J q h D C R0 T ht S ρ f k) :=
   Bon J q h D e (Actual T ht S f k) ∧ ∃ b, Solved P (Actual T ht S f k) 0 b ∧ Exact ht P p b
end
lemma send : ∃ p : Parcel J q h D C R0 T ht S (rho x C R m B) f k, Exact ht P p b := by
  let X₁:= Actual T ht S f k; let Z:= Branch.gram P X₁ b; let E:= X₁.toSpine; let g:= E.pilot x
  let μ(i):=(X₁.fee P i b).re; let T':=s.toRealQ
  have p i (v:i≤k): matchedX (hat R.L x i) (Z i).beta := matched_of_enters (a.clocks i) (a.beta_ok H T' _ v).2
  have h0 : g 0=x:= Spine.pilot_zero _; have he(i)(hi:i<k): X₁.active P b i=Z i:= a.success H T' i hi (a.paysStep H s i hi)
  have hx (i)(p:i<k) := a.active_law H T' i p
  have hG : Pull_P V 1 2 6 N0 T m ht k g J q h R0 D S Z (X₁.wave P b) μ := by
    refine ⟨fun i hi=>?_,fun i v=> (hx i v).1,fun i v=>?_,fun i _=>⟨rfl,rfl,rfl,rfl⟩,fun i v=>?_,p,fun i hi=>?_,?_,?_⟩
    · intro V q; let h:= ((hx i hi).2.2.1 V q).symm; rw [he i hi] at h; exact h
    · exact (Complex.abs_re_le_norm _).trans ((a.posts H).bound _ v _ (a.area H T' (i+1)))
    · exact ((a.charged H T' i v).mono (by linarith [(a.clocks i).leaf])).laurel ..
    · let p:= (a.paysStep H s i hi); change (Z (i+1)).beta+E.last.move i-(X₁.op P i).posted _ _ = _ at p
      have he: μ i= (X₁.op P i).posted (b.read (i+1)).re (X₁.chargeLevel P b (i+1)) := by have hx:= congrArg Complex.re (a.fee_eq H T' i hi).symm; rw [Complex.ofReal_re] at hx; exact hx
      linarith only [he,p, E.pilot_move (x:=x) i]
    · change (b.read 0).re=_; rw [Bon.anchor s,Complex.add_re,Complex.ofReal_re, Complex.ofReal_zero,Complex.zero_re,add_zero]; exact h0.symm
    · have hB:Z k=Vale.launch V.L (b.read k).re (T.a k) _ := unchanged_boot ..; rw [hB,hue_top]; rfl
  refine ⟨⟨g,Z,X₁.wave P b,μ,⟨h0,fun i _=>E.pilot_move _, pilot_match ht a H s⟩,hG,fun i hi=>?_,fun i hi=>(hx i hi).2.2.2,fun i v=>?_,fun i hi=> ?_⟩,⟨rfl,rfl,rfl,rfl⟩⟩
  · have he: |(Z i).v.re-(Z (i+1)).v.re| ≤ _:= (hx i hi).2.2.2
    rw [rho,Complex.norm_exp,Complex.norm_exp,←Real.exp_add]; exact Real.exp_monotone (by linarith [(abs_le.mp he).1])
  · have h(i j:ℕ)(s0:i≤j)(s1:j≤k) : partitionZ (Z i) U (S i)=partitionZ (Z j) U (S j):=by
      induction j with | zero => rw [show i=0 by omega] | succ j ih=> rcases s0.eq_or_lt with u|u; rw [u]; exact (ih (by omega) (by omega)).trans (a.partition H s j s1)
    exact h i k v le_rfl
  have hA:= (hx i hi).2.1; rw [he i hi] at hA; exact ⟨a.can.frequencies _,hA⟩
end Parcel
variable {z delay : ℝ} (p : Usable (D:=D) V W J N0 z delay T) {P : Prescription R B} (H : Service V U W J q h D C R0 P N0 delay)
include p H
lemma meter {F_:(s:Side)→Scree.Loom s→Prop}(pF:RackedΛ F_ J) : MeterQ V 1 2 6 N0 J q h R0 D x T := by
  refine ⟨p.walk.bank,p.walk.pole,p.walk.isle,fun m hm ht hv=>?_⟩; let MY:= m*N; obtain ⟨S,hS,_⟩:=hardCape pF q hm; let Y:=commonQ R B MY
  have he:=p.native MY ht; have hf(i:ℕ):Frequency R.L (cell MY B R.L i) (Y i):=by
    have h:= commonFreq he (n:=i) (k:=0) (n':=i) le_rfl; rw [show rung R MY 0=MY by simp [rung,Vale.mesh]] at h; exact h
  refine ⟨ S, rho x C R MY B, fun _=> Real.exp_pos _, hS, fun k=>?_⟩
  have hg:=(actual_can (h:=h) (ht:=ht) p hS hv hf k); obtain ⟨b,s⟩:= Branch.existsSolve H hg (z:=0) (by rw [abs_zero]; exact Branch.Rx_pos (p.walk.prices x le_rfl).grade)
  obtain ⟨Z,e⟩:= Parcel.send ht hg H s; exact ⟨Z.pilot,Z.gram,Z.wave,Z.fee,Z.due,Z.pay,Z.pull,Z.pull.sift,Z.balance⟩
end YM.CF.Py.Rate
