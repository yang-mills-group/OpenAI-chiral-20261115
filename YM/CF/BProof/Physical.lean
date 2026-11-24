import YM.CF.Paxos.Port

/-! # Interface to eq:num of VOLUME_PROOF

In this development physical marks (slot tests in VolumeD-sew) take `Pane`, not `Orbit`.
Their arguments include **one** common Gauge field, and the operators act on the exterior
space over `Single` (`Fin 3 × (Ten ⊕ Fin 5)` color slots). For the offset-removed
numerator we integrate the marked denZ ket on its **one** Orbit space. This file also
records the precise history interface, on the true side, using the actual ridge histories.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Function Filter Lattice Wilson Finset MeasureTheory RG
open Vault Push.SectorMeasure Skye Scree Cube Fock Tulip Vale Vale.Grace Dial Spire Lat Paige Rush Scroll Drapes
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

section Numerator

abbrev Obs (N : Side) := Pane N → FC (Single N)

variable {N : Side}

-- follow Girt.sailW (use Borel explicitly, avoid instance surprises)
local instance (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩

/-- Span of **all** modes above these gauge sites (node embedding), as a coordinate subset. -/
def modes (S : Support (More N)) : Finset (Single N) := univ.filter fun j => node j.1.1 ∈ S
@[simp] theorem mem_modes (S : Support (More N)) (i : Single N) : i ∈ modes S ↔ node i.1.1 ∈ S := mem_filter.trans (by simp)

/-- Bounded Borel kernels on physical link variables only, with all-even operator sector
supported in the indicated set. No covariance required (D marks need not have it). -/
structure Allowed (S : Support (More N)) (F : Obs N) : Prop where
  bounded : RG.Envelope F
  reads : Lattice.LocalOn S F
  modes_use : ∀ U, Sector (modes S) false (F U)

def Paid (F : Obs N) (L : ℝ) := ∀ U, ‖F U‖ ≤ L

/-- Reflection arguments will use pairwise commutation for the product word. -/
theorem Allowed.commute {S T : Support (More N)} {F G : Obs N} (h : Allowed S F)
    (g : Allowed T G) (d : Disjoint S T) : Commute F G := by
  show F * G = G * F
  funext U
  have hm : Disjoint (modes S) (modes T) := Finset.disjoint_left.mpr fun _ ha hb =>
    disjoint_left.mp d ((mem_modes ..).1 ha) ((mem_modes ..).1 hb)
  change F U * G U = G U * F U
  simpa [Sector.grainB] using Sector.apart (h.modes_use U) (g.modes_use U) hm

variable {C B L : Side} {j : ℕ} {ho : Odd L.val}
  {Y : Pricing j L ho (Thread j)} {d : ℝ}
variable (D : GramM (mid C B)) (P : Grasp Y B d) (T : Loom (mid C B))

/-- Offset removed before integrating. -/
def ket₀ (x : Orbit (mid C B)) : Phys (mid C B) := Complex.exp (-D.v) • denZ D P T x

theorem ket₀_eq (x : Orbit (mid C B)) :
    ket₀ D P T x =
      Complex.exp (- (D.path.inChannels D.funds D.p D.beta x.1 : ℝ) - Pec.pigment D.J.I (T x)) •
        acts (tank (spar j D.J.M (T x)) (D.board x)) (relV P D.J (T x)) := by
  unfold ket₀ denZ GramM.betaL GramM.H0
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  abel

def read₀ (F : Obs (mid C B)) (z : Orbit (mid C B)) : ℂ :=
  beamZ _ (acts (F z.1) (ket₀ D P T z))

def numerator (F : Obs (mid C B)) : ℂ := ∫ z, read₀ D P T F z ∂city _

theorem read₀_envelope (hen : RG.Envelope (denZ D P T))
    (F : Obs (mid C B)) (h : RG.Envelope F) : RG.Envelope (read₀ D P T F) := by
  let K := Phys (mid C B)
  apply Girt.pole_w (X:=K) _ (fun x => inner ℂ (mateK (mid C B)) x) (continuous_const.inner continuous_id)
  apply Girt.kitE (F ∘ Prod.fst) (ket₀ D P T) (fun (G : Op _) (v : K) => acts G v) (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd)
  · exact Girt.snap (X:=fun x : Orbit (mid C B) => x.1) h measurable_fst
  exact Girt.pole_w (denZ D P T) (fun x : K => Complex.exp (-D.v) • x) (Continuous.const_smul continuous_id (Complex.exp (-D.v))) hen

theorem numerator_one : numerator D P T 1 = Complex.exp (-D.v) * partitionZ D P T := by
  have h : read₀ D P T 1 = fun z => Complex.exp (-D.v) * beamZ (mid C B) (denZ D P T z) := by
    ext1 x; unfold read₀ ket₀ beamZ; simp only [Pi.one_apply,act_one,inner_smul_right]
  rw [numerator,h,partitionZ, integral_const_mul]
end Numerator

section Hist
open Py Precision Pressure

-- same pre-argument types and history choices as in the manuscript
variable {N B : Side} {K : Teller SU.group} {P : Patch} {R : ChartRatio SU.group}
  (V : Grace K P R) {d : ℝ} {U : Grasp V.U B d} {W : GivenX V U} {x : ℝ} (J : Robes N V W)
  {N₀ : ℕ} (X : Month x 1 6 2 N₀ V W) (M : Side) (h : ℝ) (q : Chi) (R₀ δ : ℝ → ℝ)

def Admits := M.val ≥ J.h ∧ X.q ≤ (M*N).val ∧ 61 ≤ (M*N).val

-- distinguish period from per-depth history. label positions all actual valuation sizes.
structure Run (n : ℕ) (Y : Cape (M*N) B P.L) (ρ : ℕ → ℝ) where
  admitted : Admits V J X M
  D : Vestal (M*N) B P.L
  reference : ℕ → ℝ
  wave : ℕ → Haro.SpaceM
  shift : ℕ → ℝ
  law : Brioche V 1 2 6 N₀ X (M*N) admitted.2.1 n reference J q h R₀ δ D Y wave shift
  offset (j : ℕ) (hj : j < n) : ‖Complex.exp (D (j+1)).v‖*ρ j ≤ ‖Complex.exp (D j).v‖

structure FamilyRun where
  ρ : ℕ → ℝ
  repair : Cape (M*N) B P.L
  positive : ∀ j, 0 < ρ j
  run : ∀ n, Run V J X M h q R₀ δ n repair ρ

theorem families (u : MeterQ V 1 2 6 N₀ J q h R₀ δ x X) (hv : Admits V J X M) :
    Nonempty (FamilyRun V J X M h q R₀ δ) := by
  obtain ⟨Y,ρ,hp,H,L⟩ := u.ridge M hv.1 hv.2.1 hv.2.2
  choose B0 Z Q Ω HH HO HH' hM HL using L
  exact ⟨ρ,Y,hp,fun n => ⟨hv,Z n,B0 n,Q n,Ω n,⟨HH' n,HH n,u.tint,u.pole,hM n,H,HL n⟩,HO n⟩⟩
end Hist
end YM.CF.BProof
