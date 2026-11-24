import YM.SU5.Exchange.Stack.Nest
import Quarry.Bra

/-! # Single opening lens on the signed integrand. Root can be interleaved with any
 spectators at disjoint support. Uses real Mark (first Pane) with replacement at the
 bra sheared by real exponent movement at the actual Grams. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet
open Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill
open Kennel TreasuryFog
open Buffered Advance

variable {C B L : Side} {e : ℝ} {j q l m : ℕ} {h : Odd L.val} {H : Pricing j L h (Thread j)}
    (P : Grasp H B e) (R : GramM (mid C B)) (K : Scree.Loom (mid C B))
    {o : Seat (mid C B)} {x : Site (mid C B)}
local notation "N" => mid C B
variable (u : Orbit (mid C B))
    (dS : IsStarProjection (spar j R.J.M (K u)))
    {V : phy (mid C B)} {F : Bag (mid C B)} {r c v a b:ℝ}

/-- Evaluation of actual unperturbed symbol cassette. -/
def engineKet {n : Side} (R : GramM n) (u : Orbit n) : Wave (Dwell n) :=
  Cadre.poseL _ (fueled R.p R.K u)

lemma den_rise : denZ R P K u = pilotH P R K u dS (engineKet R u) := by
  have h := showUp P K u dS 0 R.K
  rw [add_zero, show exponentL R.p 0 u.1 = 0 by simp [exponentL,numbE], exp_zero,one_mul] at h
  exact h

variable (Ω : Nest P R K q l o a b V F r c)
include Ω
lemma Nest.opens : pilotH P R K u dS (acts (giveB F u) (engineKet R u)) =
    acts (V u) (denZ R P K u) := by
  rw [den_rise P R K u dS]
  unfold giveB; rw [Finset.sum_apply]
  exact Ω.science u dS _

/-- Price against spectator operator at the LEFT. Replace only when bra equivalence
 in this test is known. Nothing drops the force inputs when forming the birth operator. -/
lemma Nest.withinBra (f : Buffered.Mark (mid C B)) (g : FC (Single (mid C B)))
    (h : AtBra (g * f (drawn K u)) (g * V u)) :
    letterRead (g * f (drawn K u)) (denZ R P K u) =
     letterRead g (pilotH P R K u dS (acts (giveB F u) (engineKet R u))) := by
  rw [h.read, Nest.opens P R K u dS Ω]
  change inner ℂ (mateK N) (acts (g * V u) _) = inner ℂ _ (acts g (acts (V u) _))
  rw [act_mul]

/-- In particular: no spectator. -/
lemma Nest.atRoot (f : Buffered.Mark (mid C B)) (h : AtBra (f (drawn K u)) (V u)) :
    letterRead (f (drawn K u)) (denZ R P K u) =
     letterRead 1 (pilotH P R K u dS (acts (giveB F u) (engineKet R u))) := by
  simpa only [one_mul] using Nest.withinBra P R K u dS Ω f 1 (by simpa only [one_mul] using h)

omit Ω
/-- The (129) opening bill; denominator & mark match will be kept as conclusions
    also after taking it along the Course. Keeps real grammar **and** commutation of
    the Y° on physical support. -/
structure Opening (P:Grasp H B e) (R:GramM (mid C B)) (K:Scree.Loom (mid C B))
    (q l : ℕ) (o : Seat (mid C B)) (a b : ℝ)
    (S : Support (More (mid C B))) (f : Buffered.Mark (mid C B)) (V : phy (mid C B))
    (F : Bag (mid C B)) (r c : ℝ) : Prop where
  realf : RealStencil f S
  bra (x:Orbit N) : AtBra (f (drawn K x)) (V x)
  also (x:Orbit N) : Sector (modesIn N S) false (V x)
  cost : Nest P R K q l o a b V F r c

variable {S : Support (More (mid C B))} {f : Buffered.Mark (mid C B)}
variable (O : Opening P R K q l o a b S f V F r c)
include O
lemma Opening.tail (G : FC (Single (mid C B))) {t : Support (More (mid C B))} (w : Disjoint S t)
    {β : Bool} (g : Sector (modesIn (mid C B) t) β G) : AtBra (G*f (drawn K u)) (G*V u) := by
  rw [←(sectorComm ((O.realf.foot.allV _).sector) g w).eq, ←(sectorComm (O.also u) g w).eq]; exact (O.bra u).tail _
omit O
variable {J : Axis → SOp (mid C B)} {X : SOp (mid C B)} {k : ℕ} {t pA pB : ℝ}
    (A : Trunk (node x) X k pA pB e) (δ : ∀ i, Trunk (node x) (J i) k pA pB e)
    (D : Roof (mid C B) t e q K) (ht : R.p.threshold ≤ t) (he : 0 < e)
    (size : k + q ≤ R.p.B) (ha : 0 ≤ pA) (width : 4*m ≤ R.p.B) (high : 6 ≤ R.p.B)
include A δ D ht he size ha width high
lemma openWard (z : ℂ) (C0 : Nest P R K q l (node x) a b
        (z • puffLine K R.p x J X m) F r c) :
    Opening P R K q l (node x) a b (port R.p x) (z • wardMark R.p K x m J X)
      (z • puffLine K R.p x J X m) F r c :=
  ⟨(wardStencil R.p K x A D ht he size ha δ high (by omega)).scale z,
   fun u => (wardBra R.p K x m A D ht he size δ u).scale_z z,
   fun u => (wardSector R.p K x m A D ht he size δ high width u).scale z,
   C0⟩

end YM.CF.Swell
