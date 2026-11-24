import YM.CF.Vp929.Budget.Correction
import YM.CF.Py.Wall

/-! API of transfer and re-tag. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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
variable {s : Side} (L : Side)
/-- delay in construction can fit arbitrarily small positive allowed q. To not add
an integer root to the API, use the stronger smallness exp(-L) itself. This is still
post-L pre-pivot and doesn't change the test rule. The two frequencies from RATE are
equal since the grids differ by a factor two; here require both mesh checks. -/
structure Frequency (s : Side) (q : ℝ) : Prop where
  pos : 0 < q
  small : q ≤ Real.exp (- (L.val:ℝ))
  gauge : ∃ n : ℕ, q = n*(2*Real.pi / (More s).val)
  matter : ∃ n : ℕ, Odd n ∧ q = n*(Real.pi / s.val)

def projectorMind : Op SU.Slot →ₗ[ℝ] SpaceM :=
  SpaceM.projectionOnto _ (exists_isCompl SpaceM).choose_spec
def transverse (q : ℝ) : tangD s := fun i=> if i.2=1 then
  (Real.sin (q*(lift i.1 0:ℝ)) / q) • AnalyticBridge.VerifiedReset.spike SU.group else 0
def gaugeTest (q : ℝ) (F : RegBudget s) (p : BudgetPoint) : ℝ :=
  (sites s)⁻¹ * iteratedDeriv 2 (fun x : ℝ=> (pane (exponentL p F (increment 1 (x • transverse q)))).re) 0
def signs (b : Bool) : ℝ := if b then 1 else -1
def waveTest (q : ℝ) (F : RegBudget s) (k : ℕ) (M : Male) : SpaceM :=
  projectorMind (Tap.spaX ((16*q)⁻¹ • ∑ η : Axis → Bool, signs (η 0) •
                  Tap.potion k M (heroP (StackL F univ)) (fun i=> q*signs (η i))) 0)
def Canonical (q : ℝ) (X : GramM s) (j : ℕ) := gaugeTest q X.F X.p = 0 ∧ waveTest q X.F j X.J.M = 0

/-- Imaginary room. -/
def strip (x : ℝ) := x/(1+Real.log x)^30
/-- beta analytic payment domain. -/
def enters (y : ℝ) (b : ℂ) : Prop := 53/100*y ≤ b.re ∧ b.re ≤ 7/4*y ∧ |b.im| ≤ 3*strip y
/-- beta domain for equations starE and starT. -/
def entersReal (y b : ℝ) : Prop := 54/100*y ≤ b ∧ b ≤ 173/100*y

variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V : Grace K R L)
variable {d : ℝ} {m n N B : Side} (U : Grasp V.U B d) (W : GivenX V U) (J : Robes N V W) (q : Chi)
/-- Step data shared even across change of Month. -/
structure Location (B m n : Side) where
  lag : ℕ
  G : Ratio (mid m B) (mid n B)
  count : G.count=R.L
  sizes : (Domain n B).val = (Domain m B).val*R.L.val
  input : Interest (mid n B)
  output : Interest (mid m B)
  fee : ℝ
  coarse : Scree.Loom (mid m B)
  fine : Scree.Loom (mid n B)
  freq : ℝ
include V
namespace Location
variable (u : Location (R:=R) B m n)
abbrev step := V.L.op u.lag u.sizes
abbrev movement := V.L.charge u.lag + u.fee
abbrev buildIn (p : BudgetPoint) (b : ℝ) (F : Corr (mid n B)) (v : ℂ) := construct p (V.L.path u.lag) K.top.clip u.input b F v
abbrev buildOut (p : BudgetPoint) (b : ℝ) (F : Corr (mid m B)) (v : ℂ) := construct p (V.L.path (u.lag+1)) K.top.clip u.output b F v
@[ext]
lemma extFields {a b : Location (R:=R) B m n} (H : a.lag=b.lag) (H₀ : a.output=b.output) (H₁ : a.input=b.input)
    (p : a.fee=b.fee) (q : a.coarse=b.coarse) (r : a.fine=b.fine) (s : a.freq=b.freq) : a=b := by
  have he : ∀ x y : Ratio (mid m B) (mid n B), x.count=y.count → x=y := by rintro ⟨x,h⟩ ⟨y,r⟩ q; congr
  have e:= he _ _ (a.count.trans b.count.symm); cases a; cases b; congr
structure Boot (x : ℝ) (p : BudgetPoint) : Prop where
  threshold : p.threshold=temp x
  B : p.B=radiusB x
  exponent : p.supportExponent=1
  power : p.power=2
  order : p.order=6
/-- Inputs furnished by a rung (Month etc.). Stage grant independent of horizon. -/
structure Request (N0 : ℕ) (x : ℝ) (p p' : BudgetPoint) : Prop where
  rocket : RocketV V m n U W J u.coarse u.G q
  roof : Roof _ J.k J.roomX J.n u.fine
  fineSize : J.h ≤ (mid n B).val
  sound : InterestX W.C _ u.output
  statv (b : ℝ) (F : Corr (mid n B)) (slip : RegBudget (mid n B)) (v : ℂ) : matchedX (x+billX R.L) b → StatV V u.G (V.L.mint u.lag u.sizes) U W
    (u.buildOut V p (b+u.movement V) 0 0) { u.buildIn V p' b F v with slip := slip } (V.L.charge u.lag) u.fee 1 x 2 6
  boot : Boot x p
  boot' : Boot (x+billX R.L) p'
  size : N0 * radiusB x ≤ (Domain m B).val
  size₂ : 60 < (Domain m B).val
  frequency : Frequency R.L (mid m B) u.freq
  pole : p.threshold ≤ J.k
  pole' : p'.threshold ≤ J.k
  isle : Rue.IsleB SU.group p.threshold
  isle' : Rue.IsleB SU.group p'.threshold
end Location

/-- Step operations ignoring array values if never called on valid domains; output corrections and scalar extraction determined even off Wear, and do NOT depend on fine offset. -/
structure Operation (s s' : Side) where
  arrays : ℂ → Pair (Corr s') → Pair (Corr s)
  Δ : ℂ → Pair (Corr s') → ℂ
  offset : ℝ → Corr s' → ℂ → ℂ
  wave : ℝ → Corr s' → SpaceM
namespace Operation
abbrev realArr (A : Operation s m) (b : ℝ) (F : Corr m) := (A.arrays b (F,0)).1
abbrev posted (A : Operation s m) (b : ℝ) (F : Corr m) := (A.Δ b (F,0)).re
def output (u : Location (R:=R) B m n) (A : Operation (mid m B) (mid n B)) (p : BudgetPoint) (b : ℝ) (F : Corr (mid n B)) (v : ℂ) : GramM (mid m B) :=
  u.buildOut V p (b + u.movement V - A.posted b F) (A.realArr b F) (A.offset b F v)
end Operation
variable (h x : ℝ) (p p' : BudgetPoint)
structure Certified (R0 D C : ℝ) (u : Location (R:=R) B m n)
    (A : Operation (mid m B) (mid n B)) : Prop where
  cost (b : ℂ) (F) (hb : enters (x+billX R.L) b) (hp : Both (Charged p' u.input K.j R.L.val h (3*dleaf R.L x)) F) :
    Both (Charged p u.output K.j R.L.val h (dleaf R.L x/1000)) (A.arrays b F) ∧ ‖A.Δ b F‖ ≤ D
  analytic (S : Set ℂ) (hs : IsOpen S) (b : ℂ → ℂ) (F)
    (hp : ∀ z ∈ S, enters (x+billX R.L) (b z) ∧ Both (Charged p' u.input K.j R.L.val h (3*dleaf R.L x)) (F z))
    (hb : DifferentiableOn ℂ b S) (hF : HoloCorr S F) : HoloCorr S (fun z=> A.arrays (b z) (F z)) ∧ DifferentiableOn ℂ (fun z=> A.Δ (b z) (F z)) S
  real (b : ℝ) (F : Corr (mid n B)) (v : ℂ) (hb : enters (x+billX R.L) b)
    (hp : Charged p' u.input K.j R.L.val h (3*dleaf R.L x) F) :
    let Z:= A.output V u p b F v
    let X:= u.buildIn V p' b F v
    (A.arrays b (F,0)).2=0 ∧ (A.Δ b (F,0)).im=0 ∧ ‖A.wave b F‖ ≤ R0 ∧ Canonical u.freq Z K.j ∧
    (∀ y, Rue.FleetS p.threshold y.1 → denZ Z U u.coarse y = stove U u.coarse X u.fine u.G (u.step V) q J.d (A.wave b F).val y) ∧
    |(A.offset b F v).re-v.re| ≤ C*sites (mid m B)
  stars (a c b b' : ℝ) (F F' : Corr (mid n B))
    (hv : ∀ t ∈ ({(b,F),(b',F')} : Set (ℝ × Corr (mid n B))), entersReal (x+billX R.L) t.1 ∧
      Charged p' u.input K.j R.L.val h (dleaf R.L (x+billX R.L) / 1000) t.2)
    (he : 0≤a) (hk : 0≤c)
    (hl : Cost p' h (dleaf R.L (x+billX R.L)*a) (F-F')) (hδ : |b-b'| ≤ strip (x+billX R.L)*c) :
    Cost p h (dleaf R.L x*((a+c)/4)) (A.realArr b F - A.realArr b' F') ∧ |A.posted b F - A.posted b' F'| ≤ 100*D*(a+c)

/-- Same map choices for all calls in the ladder and comparison, at valid tags. -/
abbrev Prescription (R : Patch) (B : Side) := ∀ (m n:Side), Location (R:=R) B m n → ℝ → BudgetPoint → BudgetPoint → Operation (mid m B) (mid n B)
structure Service (D C R0 : ℝ → ℝ) (P : Prescription R B) (N0 : ℕ) (delay : ℝ) : Prop where
  provides : ∀ (m n) (u : Location (R:=R) B m n) x p p', delay ≤ x → Location.Request V U W J q u N0 x p p' → Certified V U W J q h x p p' (R0 x) (D x) (C x) u (P m n u x p p')
  compare : ∀ (m n) (u : Location (R:=R) B m n) x x' p₀ p₁ p₀' p₁', delay ≤ x → delay ≤ x' → Location.Request V U W J q u N0 x p₀ p₁ → Location.Request V U W J q u N0 x' p₀' p₁' → ∀ (b : ℝ) (F F' : Corr (mid n B)) (v v' : ℂ), enters (x+billX R.L) b → enters (x'+billX R.L) b → Charged p₁ u.input K.j R.L.val h (3*dleaf R.L x) F → Charged p₁' u.input K.j R.L.val h (3*dleaf R.L x') F' →
    let A:= P m n u x p₀ p₁; let A':= P m n u x' p₀' p₁'
    let Z:= A.output V u p₀ b F v; let Z':= A'.output V u p₀' b F' v'
    denZ (u.buildIn V p₁ b F v) U u.fine =ᵐ[city _] denZ (u.buildIn V p₁' b F' v') U u.fine →
    A.wave b F = A'.wave b F' ∧ Z.beta=Z'.beta ∧ ∀ y,Rue.FleetS p₀.threshold y.1 → Rue.FleetS p₀'.threshold y.1 → denZ Z U u.coarse y = denZ Z' U u.coarse y

/-- Top-cut switching, priced on a larger month. Only comparisons where the physical (wider)
aperture and retagged (narrower) budget are legitimate sizes are needed. -/
def aperture (x : ℝ) (b : ℂ) := x/3 ≤ b.re ∧ ‖b‖ ≤ 3*x
def Retag (N0 : ℕ) (delay : ℝ) := ∀ x y, delay ≤ x → x≤y → y≤4/3*x →
    ∀ (m : Side) (S : Scree.Loom (mid m B)) (p p' : BudgetPoint), Location.Boot x p → Location.Boot y p' →
    p.threshold ≤ J.k → p'.threshold ≤ J.k → Rue.IsleB SU.group p.threshold → Rue.IsleB SU.group p'.threshold →
    Roof _ J.k J.roomX J.n S → J.h ≤ (mid m B).val → 60 < (Domain m B).val → N0 * radiusB y ≤ (Domain m B).val →
    ∃ T : ℂ → Pair (Corr (mid m B)), (∀ b, aperture x b → Both (Charged p' (vanilla _) K.j R.L.val h (dleaf R.L y/1000)) (T b)) ∧
      (∀ (Z : Set ℂ), IsOpen Z → ∀ b : ℂ → ℂ, (∀ z ∈ Z, aperture x (b z)) → DifferentiableOn ℂ b Z → HoloCorr Z (T ∘ b)) ∧
      ∀ b : ℝ, aperture x b → (T b).2 = 0 ∧ ∀ v, Rue.FleetS p.threshold v.1 → Rue.FleetS p'.threshold v.1 → denZ (Vale.launch V.L b p _) U S v = denZ
          (construct p' (V.L.path 0) K.top.clip (vanilla _) b (T b).1 0) U S v

end YM.CF.Py.Rate
