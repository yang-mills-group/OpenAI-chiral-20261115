import ExactRunning.Scenes.Frame

/-!
# Local regularity for parametric films

Predicate to pass analyticity of Fourier symbols (`Film`) to
`Film.figure` (log|det| Hessian summand), at a base point with zero
external momentum and a given internal momentum. As opposed to
`tableau_Medium`, the purpose is to allow simultaneous variation
of additional parameters such as mass.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

variable {γ : Type} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {x : Y}

def Memobic (A : Y → CompM α β) (x : Y) :=
  ∀ i j, ContDiffAt ℝ ω (fun z => A z i j) x

namespace Memobic
variable {U V : Y → CompM α β}

lemma mul {W : Y → CompM β γ} (h : Memobic U x) (k : Memobic W x) :
    Memobic (fun z => U z * W z) x := by
  intro i j; simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (h i l).mul (k l j)

lemma park (W : CompM α β) (x : Y) : Memobic (fun _ => W) x := fun _ _ => contDiffAt_const

lemma add (h : Memobic U x) (k : Memobic V x) :
    Memobic (fun z=> U z + V z) x := fun i j => (h i j).add (k i j)

lemma sub (h : Memobic U x) (k : Memobic V x) :
    Memobic (fun z=> U z - V z) x := fun i j => (h i j).sub (k i j)
lemma neg (h : Memobic U x) :
    Memobic (fun z => -U z) x := fun i j => (h i j).neg
lemma scale (h : Memobic U x) {c : Y → ℂ} (hc : ContDiffAt ℝ ω c x) :
    Memobic (fun z => c z • U z) x := fun i j => hc.mul (h i j)

lemma transpose (h : Memobic U x) :
    Memobic (fun z => (U z)ᵀ) x := fun i j => h j i

variable {P : Y→Matrix α α ℂ} (hp : Memobic P x)
include hp
lemma det : ContDiffAt ℝ ω (fun z => (P z).det) x := by
  simp only [Matrix.det_apply]
  refine ContDiffAt.sum fun i _ => ?_
  simp only [Units.smul_def,zsmul_eq_mul]; refine ContDiffAt.mul contDiffAt_const ?_
  suffices ht : ∀ S : Finset α,ContDiffAt ℝ ω (fun z => ∏ j∈S,P z (i j) j) x from ht univ
  intro S; induction S using Finset.induction with
  | empty => simp; exact contDiffAt_const
  | insert a l he IH => simp_rw [Finset.prod_insert he]; exact (hp _ _).mul IH

lemma inv (h : IsUnit (P x).det) : Memobic (fun z => (P z)⁻¹) x := by
  intro i j; simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply]
  refine ((hp.det.inv h.ne_zero).smul ?_)
  simp_rw [Matrix.adjugate_apply]; apply Memobic.det
  intro k l; simp only [Matrix.updateRow_apply]; split; exact contDiffAt_const
  exact hp _ _

lemma trace : ContDiffAt ℝ ω (fun z => (P z).trace) x :=
  ContDiffAt.sum fun i _ => hp i i

end Memobic

structure Slide (x : Y) (p : Momentum) where
  run : Y → Momentum
  smooth : ContDiffAt ℝ ω run x
  hits : run x = p
instance {r : Momentum} : CoeFun (Slide x r) (fun _ => Y → Momentum) := ⟨Slide.run⟩

namespace Slide
variable {r : Momentum}
/-- Add an external (centered) shift. -/
def drift (v : Slide x r) (b : Slide x 0) : Slide x r :=
  ⟨fun y => v y + b y,v.smooth.add b.smooth,by rw [b.hits,v.hits, add_zero]⟩
def neg (u : Slide x 0) : Slide x 0 := ⟨fun y => -u y,u.smooth.neg,by rw [u.hits,neg_zero]⟩
end Slide

structure Livens (F : Y → Film ι α β) (x : Y) (r : Momentum) : Prop where
  tab (v : Slide x r) : Memobic (fun y => (F y).tab (v y)) x
  spot (i : ι) (a : Slide x 0) (v : Slide x r) :
    Memobic (fun y => (F y).spot i (a y) (v y)) x
  arch (i j : ι) (a b : Slide x 0) (v : Slide x r) :
    Memobic (fun y => (F y).arch i j (a y) (b y) (v y)) x

namespace Livens
variable {r : Momentum} {F T : Y → Film ι α β}

lemma simple {K : Y → CompM α β} (h : Memobic K x) :
    Livens (fun y => Film.cardF (ι:=ι) fun _ => K y) x r :=
  ⟨fun _ => h, fun _ _ _ => Memobic.park 0 _, fun _ _ _ _ _ => Memobic.park 0 _⟩

lemma plus (h : Livens F x r) (k : Livens T x r) :
    Livens (fun y => (F y).plus (T y)) x r :=
  ⟨fun v => (h.tab v).add (k.tab v),
    fun i a v => (h.spot i a v).add (k.spot i a v),
    fun i j a b v => (h.arch i j a b v).add (k.arch i j a b v)⟩

lemma weight {c : Y → ℂ} (h : Livens F x r) (g : ContDiffAt ℝ ω c x) :
    Livens (fun y => (F y).weight (c y)) x r :=
  ⟨fun v => (h.tab v).scale g, fun i a v => (h.spot i a v).scale g,
    fun i j a b v => (h.arch i j a b v).scale g⟩

lemma pay [Fintype γ] [DecidableEq γ] {K : Y → Film ι β γ} (h : Livens F x r) (k : Livens K x r) :
    Livens (fun y => (F y).pay (K y)) x r :=
  ⟨fun v => (h.tab v).mul (k.tab v),
   fun i a v => ((h.spot i a v).mul (k.tab v)).add ((h.tab (v.drift a)).mul (k.spot i a v)),
   fun i j a b v => by

    have g1 := (h.spot j b (v.drift a)).mul (k.spot i a v)
    have g2 := (h.spot i a (v.drift b)).mul (k.spot j b v)
    exact ((((h.arch i j a b v).mul (k.tab v)).add g1).add g2).add
      ((h.tab (v.drift (a.drift b))).mul (k.arch i j a b v))⟩

section
variable {U : Y → Film ι α α} (h : Livens U x r)
include h

lemma cup (hd : IsUnit ((U x).tab r).det) (v : Slide x r) :
    Memobic (fun y => (U y).coupon (v y)) x :=
  (h.tab v).inv (by rw [v.hits]; exact hd)

lemma vip (hd : IsUnit ((U x).tab r).det) (i : ι) (a : Slide x 0) (v : Slide x r) :
    Memobic (fun y => (U y).vSpot i (a y) (v y)) x :=
  (((h.cup hd (v.drift a)).mul (h.spot i a v)).mul (h.cup hd v)).neg

lemma back (hd : IsUnit ((U x).tab r).det) :
    Livens (fun y => (U y).back) x r :=
  ⟨h.cup hd, h.vip hd,
    fun i j a b v => by

      have g1 := (h.vip hd j b (v.drift a)).mul (h.spot i a v)
      have g2 := (h.vip hd i a (v.drift b)).mul (h.spot j b v)
      exact ((((g1.add g2).add
        ((h.cup hd (v.drift (a.drift b))).mul (h.arch i j a b v)))).mul
        (h.cup hd v)).neg ⟩

lemma figure (hd : IsUnit ((U x).tab r).det)
    (i j : ι) (a : Slide x 0) (v : Slide x r) :
    ContDiffAt ℝ ω (fun y => (U y).figure i j (a y) (v y)) x := by
  have hi := h.cup hd (v.drift (a.neg.drift a))
  have h2 := ((hi.mul (h.spot i a.neg (v.drift a))).mul (h.cup hd (v.drift a))).mul
    (h.spot j a v)
  exact ((hi.mul (h.arch i j a.neg a v)).sub h2).trace
end

variable {σ : ℝ}

section
variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {z : Z} {p q v : Z → Momentum}
private lemma avenue {σ : ℝ} (h : Avenue σ (p z) (v z))
    (hp : Continuous p) (hv : Continuous v) :
    ∀ᶠ w in 𝓝 z, Avenue σ (p w) (v w) := by
  let l := Work.F07.stripOpen (α:=Axis) σ
  filter_upwards [(hp.tendsto z) (l.mem_nhds h.side),
    (hv.tendsto z) (l.mem_nhds h.basic),
    ((hv.add hp).tendsto z) (l.mem_nhds h.added)] with w a b c using ⟨a,b,c⟩

private lemma boulevard {σ : ℝ} (h : Boulevard σ (p z) (q z) (v z))
    (hp : Continuous p) (hq : Continuous q) (hv : Continuous v) :
    ∀ᶠ w in 𝓝 z, Boulevard σ (p w) (q w) (v w) := by
  filter_upwards [avenue h.oneWay hp hv, avenue h.second hq hv,
    ((hv.add (hp.add hq)).tendsto z) ((Work.F07.stripOpen _).mem_nhds h.total)] with w a b c using ⟨a,b,c⟩

private lemma into [FiniteDimensional ℂ Z] [NormedSpace ℝ Z] [IsScalarTower ℝ ℂ Z]
    (g : Z → CompM α β) {u : Y → Z} (h : ContDiffAt ℝ ω u x)
    (hh : ∀ᶠ a in 𝓝 (u x), BillD g a) :
    Memobic (fun y => g (u y)) x := by
  intro i j
  apply ContDiffAt.comp (g:=fun z => g z i j) x _ h
  apply ContDiffAt.restrict_scalars ℝ (𝕜':=ℂ)
  apply AnalyticAt.contDiffAt
  apply PolyDisc.finiteD
  exact hh.mono fun _ he => he i j
end

lemma of_play {L : Film ι α β} (h : Play L σ) (hσ : 0<σ) (hr : star r=r) :
    Livens (fun _ => L) x r := by
  have a : r ∈ strip σ := Work.F07.realStrip _ hσ hr
  have b : Avenue σ 0 r := ⟨Work.F07.realStrip _ hσ (by simp),a,by simpa⟩
  refine ⟨fun v => into L.tab v.smooth ?_,
    fun i p v => into (uncurry (L.spot i)) (p.smooth.prodMk v.smooth) ?_,
    fun i j p q v => into (road3 (L.arch i j)) (p.smooth.prodMk (q.smooth.prodMk v.smooth)) ?_⟩

  · rw [v.hits]; exact Eventually.mono ((Work.F07.stripOpen _).mem_nhds a) fun _ ha => h.tab.shape ha
  · simp only [v.hits,p.hits]
    exact (avenue (z:=(0,r)) (by exact b)
      continuous_fst continuous_snd).mono fun _ he => (h.spot i).shape he
  · simp only [v.hits,p.hits,q.hits]
    have e : Boulevard σ 0 0 r := ⟨b,b,by simpa⟩
    exact (boulevard (z:=(0,0,r)) (σ:=σ) (by exact e)
      continuous_fst (continuous_snd.fst) (continuous_snd.snd)).mono fun _ he => (h.arch i j).shape he
end Livens
end ExactRunning
