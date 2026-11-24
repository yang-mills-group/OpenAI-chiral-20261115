import YM.CF.Mew.Pot
import YM.CF.Bloom.Apse
import YM.CF.Song.Agape

/-! Arrays and analytics in the Volume manuscript. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
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
open Ione Beau Haro Cascade
open scoped Mew

/-- Currency pair: regular and force budgets. Keep slip identically zero. -/
abbrev Corr (s : Side) := RegBudget s × ForceBudget s
abbrev construct {s : Side} (p : BudgetPoint) (A : PathData SU.group) (clip : Clip) (I : Interest s)
    (b : ℝ) (F : Corr s) (v : ℂ) : GramM s := ⟨p,A,clip,b,I,F.1,0,F.2,v⟩

section Cost
variable {s : Side} (p : BudgetPoint) (I : Interest s) (j L : ℕ) (h a : ℝ)
/-- Incidence tests with real-linear sweep laws. -/
structure Cost (F : Corr s) : Prop where
  inc : IncX Utrue F.1 p h a
  dark : Dark Utrue F.2 p h a
structure Charged (F : Corr s) : Prop extends Cost p h a F where
  dawn : Ionic p L F.1
  warp : Sour.BondL.mintv (treeΘ p L) j I.M F.1
lemma Charged.laurel {n m : Side} {I : Interest (mid n m)} (A : PathData SU.group) (f : Clip)
    (b : ℝ) (v : ℂ) {F : Corr (mid n m)} (hp : Charged p I j L h a F) : Laurel (construct p A f I b F v) j h a a L :=
  ⟨hp.inc,rfl,hp.dark,hp.dawn,hp.warp⟩
end Cost

/-! Complexify real array spaces by pairs. Use the analytical projections of the appendix
(second projection taken in conjugate variables). Our balls use both component payments separately;
this equivalent pricing only changes constants. Use several-argument holomorphy only along analytic
curves (including complex lines); avoids topologizing the off-payment array values. -/

abbrev Pair (α : Type*) := α × α
namespace Pair
variable {X : Type*} [AddCommGroup X] [Module ℂ X]
abbrev plus (u : Pair X) := u.1 + Complex.I • u.2
abbrev minus (u : Pair X) := u.1 - Complex.I • u.2
end Pair

variable {s m B : Side} (p : BudgetPoint) (S : Set ℂ)
open scoped ComplexConjugate
/-- Holo on configurations, not asking for holomorphy in the gauge argument. -/
def Holo {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (f : ℂ → Pair X) : Prop :=
  DifferentiableOn ℂ (fun z=> Pair.plus (f z)) S ∧
  DifferentiableOn ℂ (fun z=> Pair.minus (f (starRingEnd ℂ z))) ((starRingEnd ℂ) ⁻¹' S)
def HoloCorr (f : ℂ → Pair (Corr s)) : Prop :=
  (∀ i v, Holo S fun z=> ((f z).1.1 i v, (f z).2.1 i v)) ∧
   ∀ i v, Holo S fun z=> ((f z).1.2 i v, (f z).2.2 i v)
lemma plus_reg (f : Pair (Corr s)) (i) (v) : (Pair.plus f).1 i v = Pair.plus (f.1.1 i v,f.2.1 i v) := rfl
lemma plus_force (f : Pair (Corr s)) (i) (v) : (Pair.plus f).2 i v = Pair.plus (f.1.2 i v,f.2.2 i v) := rfl
lemma holoCorr_const (f : Pair (Corr s)) : HoloCorr S fun _=> f :=
  ⟨fun _ _=> ⟨differentiableOn_const _,differentiableOn_const _⟩,fun _ _=>⟨differentiableOn_const _,differentiableOn_const _⟩⟩

def Both {X : Type*} (P : X → Prop) (u : Pair X) := P u.1 ∧ P u.2
lemma holoCorr_congr {f g : ℂ → Pair (Corr s)} (h : HoloCorr S f) (e : Set.EqOn g f S) : HoloCorr S g := by
  constructor
  · intro i v; constructor
    · apply (h.1 i v).1.congr; intro x hx; simp only [e hx]
    apply (h.1 i v).2.congr; intro x hx; simp only [e hx]
  intro i v; constructor
  · apply (h.2 i v).1.congr; intro x hx; simp only [e hx]
  apply (h.2 i v).2.congr; intro x hx; simp only [e hx]

abbrev sites (s : Side) : ℝ := ((More s).val:ℝ)^4
lemma sites_pos (s : Side) : 1 ≤ sites s := one_le_pow₀ (by exact_mod_cast (More s).property)
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {d : ℝ}
    {V : Grace K R L} (U : Grasp V.U B d)
/-- Offset-removed field and partition. -/
abbrev field (X : GramM (mid m B)) (S : Scree.Loom (mid m B)) := fun x=> Complex.exp (-X.v) • denZ X U S x
abbrev compensated (X : GramM (mid m B)) (S : Scree.Loom (mid m B)) := Complex.exp (- X.v) * partitionZ X U S
/-- An expression of the holomorphic parameter extension (of the offset-removed field), keeping
masks real. Written directly with `denZ` on the real part of beta, so real compatibility is also
transparent. -/
def cfield (I : Interest (mid m B)) (l : ℕ) (S : Scree.Loom (mid m B)) (F : Pair (Corr (mid m B)))
    (b : ℂ) := fun x : Orbit (mid m B) => Complex.exp (- Complex.I * (b.im:ℂ) *
    (Push.BetaTransport.kinetic (V.L.path l) K.top.clip p x.1:ℂ)) • denZ (construct p (V.L.path l) K.top.clip I b.re (Pair.plus F) 0) U S x
def cpartition (I : Interest (mid m B)) (l : ℕ) (S : Scree.Loom (mid m B)) (F : Pair (Corr (mid m B)))
    (b : ℂ) := ∫ x, beamZ (mid m B) (cfield p U I l S F b x) ∂city _
lemma cfield_real (I : Interest (mid m B)) (l : ℕ) (S : Scree.Loom (mid m B)) (F : Corr (mid m B))
    (b : ℝ) (v : ℂ) : cfield p U I l S (F,0) b = field U (construct p (V.L.path l) K.top.clip I b F v) S := by
  funext x; unfold cfield field; simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_smul,Pair.plus,smul_zero,add_zero]
  unfold denZ; rw [smul_smul,←Complex.exp_add]; congr 2; unfold GramM.betaL GramM.H0; dsimp [construct]; ring
lemma integral_beam (X : GramM (mid m B)) (S : Scree.Loom (mid m B)) :
    (∫ x, beamZ _ (field U X S x) ∂city _) = compensated U X S := by
  unfold compensated partitionZ; rw [←integral_const_mul]; simp only [beamZ,field,inner_smul_right]
lemma cpartition_real (I : Interest (mid m B)) (l : ℕ) (S : Scree.Loom (mid m B)) (F : Corr (mid m B))
    (b : ℝ) (v : ℂ) : cpartition p U I l S (F,0) b = compensated U (construct p (V.L.path l) K.top.clip I b F v) S := by
  rw [cpartition,cfield_real p U I l S F b v]; exact integral_beam ..
end YM.CF.Py.Rate
