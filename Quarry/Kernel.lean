import Quarry.Lens
import YM.SU5.Exchange.Pace.Cult
import YM.SU5.Interaction.Source
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 720000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation

open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Rill Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Vale Dial Fock
open Vow Ione Sour Swell
open BPress (NPL)
open Buffered
open Afterglow Tapestry
open FullBill Window Marks
open Pitching Focus QuadClock

variable {P : Preparation} {f : (s:Side)→Scree.Loom s→Prop} (Y : Course P f)
local notation "n0" i:max s:max => P.Ctor (Y.ir i) s
local notation "coords" s:max => hat P.R.L P.x s
local notation "Π" => P.K.j

/-- Kernel purchase on the actual law, includes the mask launch on **mark128**. -/
structure Counterfoil (s i k m : ℕ) (a c F D : ℝ) (x : Site (cell (Y.ir i) P.block P.R.L s))
    (J T : Axis → SOp (cell (Y.ir i) P.block P.R.L s))
    (X Z : SOp (cell (Y.ir i) P.block P.R.L s))
    (V : Bag (cell (Y.ir i) P.block P.R.L s)) : Prop where
  study :
    let R := RootBook Y i k s
    let p := R.p
    let K := (Y.voyage i).CapeT s
    let M := funde P.K.j R.J.M (cell (Y.ir i) P.block P.R.L s)
    let S := Moire.bloom R.J.P
    let w := p.B / 10
    let y := hat P.R.L P.x s
    let B := Real.exp (-a*(w:ℝ))*c
    let u := hueW P.R.L y
    let Q := pinpr P.R.L y
    p.threshold=Pressure.temp y ∧ p.supportExponent=1 ∧ p.B=Pressure.radiusB y ∧
    p.order=6 ∧ p.power=2 ∧ w+P.J.n≤p.B ∧ 4*m≤p.B ∧ 6≤p.B ∧
    Roof (cell (Y.ir i) P.block P.R.L s) P.J.k P.d P.J.n K ∧ p.threshold ≤ P.J.k ∧
    0<a ∧ 0<c ∧ 0<Q ∧
    Staffer M S P.d ∧
    (∀ l, Trunk (node x) (J l) w a c P.d) ∧
    (∀ l, Soak (node x) (T l) a B P.d) ∧ Trunk (node x) X w a c P.d ∧ Soak (node x) Z a B P.d ∧
    (∀ l : Axis, ∀ z : Openc (More (cell (Y.ir i) P.block P.R.L s)) P.d,
      spur (millIntro M S) x l m z.val = J l z.val + T l z.val) ∧
    (∀ z : Openc (More (cell (Y.ir i) P.block P.R.L s)) P.d,
      (M z.val-tickA _)*windmill x m=X z.val+Z z.val) ∧
    Opening P.U R K P.J.n 24 (node x) P.h (rScale p) (port p x)
      ((stemS y:ℂ) • mark128 p K x Q m J X) ((u:ℂ) • puffLine K p x J X m)
      V F (D*Q)

theorem market129 (flag : ∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay) (W : Compass_sol Y)
    (hT : RateStamp Y) (m : ℕ) : ∃ (a c:ℝ) (F D:ℝ→ℝ), 0<a ∧ 0<c ∧ NPL F ∧ NPL D ∧
    ∀ᶠ s : ℕ in atTop, ∀ᶠ i : ℕ in atTop, ∀ k : ℕ, s < Y.uv k →
      ∀ x : Site (cell (Y.ir i) P.block P.R.L s), ∃ J T X Z V,
        Counterfoil Y s i k m a c (F (coords s)) (D (coords s)) x J T X Z V := by
  obtain ⟨a,c,F,D,ua,uc,H,v,T⟩ := factorium Y flag W hT m
  obtain ⟨a',c',b,u,w,A,U,hb,I,M,G⟩ := statements Y flag hT W m
  refine ⟨a,c,F,D,ua,uc,H,v,?_⟩
  filter_upwards [T,G,(turnover P).eventually (draft_π P.R.L),
    (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop (4*m+2*P.J.n+10)] with s t g H' hB
  filter_upwards [t, g] with i hu hg k hv x
  obtain ⟨J,Kt,X,Z,l,z,f,b,hh,hX,Fk,p⟩ := hu k hv x
  obtain ⟨hx,hT,π',hp,vq,κ,vg,a1,a2,a3,a4,a5,-⟩ := hg k hv
  let Q' := (RootBook Y i k s).p; let w := hat P.R.L P.x s
  have hu : Q'.B = Pressure.radiusB w := a1
  obtain ⟨η,χ,-⟩ := H'
  have Hz : 0 < pinpr P.R.L w := pow_pos χ _
  have hL : 4*m+2*P.J.n+10 ≤ Q'.B := hu.symm ▸ hB
  have Hk : Q'.B/10+P.J.n ≤ Q'.B := by omega
  refine ⟨J,Kt,X,Z,Fk,⟨a4,a5,a1,a2,a3,Hk,by change 4*m ≤ Q'.B; omega,
    by change 6≤ Q'.B; omega,π'.roof,π'.reach,ua,uc,Hz,hp,l,z,f,b,hh,hX,?_⟩⟩
  have PZ := openWard P.U (RootBook Y i k s) _ f l π'.roof π'.reach P.dpos Hk ua.le
    (show 4*m ≤ Q'.B by omega) (show 6 ≤ Q'.B by omega) _ p
  dsimp only [mark128]
  rw [smul_smul, show (stemS w:ℂ)* ((pinpr P.R.L w / Q'.threshold ^ 2 : ℝ):ℂ)=(hueW P.R.L w:ℂ) from ?_]; exact PZ
  have ht:Q'.threshold=Pressure.temp w:=a4
  rw [← Complex.ofReal_mul,ht,hueW,mul_comm]

/- Signed integrand lens. Requires the kick for the actual measure and keeps the
    pre-Mark support & multiscale bill. No size estimate on `/Z` from a positivity law. -/
section separate
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
open TreasuryFog Satin Advance Journey
variable (s i k : ℕ) (m : ℕ)
local notation "N" => cell (Y.ir i) Λ.block Λ.R.L s
local notation "R" => RootBook Y i k s
local notation "A" => Λ.U
local notation "K" => (Y.voyage i).CapeT s

/-- Opened integrand after carrying the spectator at the same bra, actual denominator **not** included here. -/
def aisle (V : Bag N) (F : Buffered.Mark N) (u : Orbit N) : ℂ :=
  Buffered.letterRead (F (drawn K u))
    (pilotH Λ.U R K u (projects_here Y i k s u).1 (acts (giveB V u) (engineKet R u)))

local notation "ζ" => hat Λ.R.L Λ.x s
local notation "latte" => stemS ζ
local notation "Q" => pinpr Λ.R.L ζ
variable {a c u v:ℝ} {x: Site (cell (Y.ir i) Λ.block Λ.R.L s)}
    {J T : Axis → SOp (cell (Y.ir i) Λ.block Λ.R.L s)}
    {X Z : SOp (cell (Y.ir i) Λ.block Λ.R.L s)}
    {V : Bag (cell (Y.ir i) Λ.block Λ.R.L s)}
    (ℬ : Counterfoil Y s i k m a c u v x J T X Z V)
    (e : (Y.voyage i).kick ≤ k) (h : s ≤ Y.uv k)
local notation "μ" => ((latte:ℂ) • mark128 (R).p K x Q m J X)
local notation "puffCar" => ((hueW Λ.R.L ζ:ℂ) • puffLine K (R).p x J X m)

/-- Authorized competitor keeping both full and birth charges at the occurrence. -/
lemma Counterfoil.billed (s' : Counterfoil Y s i k m a c u v x J T X Z V) :
    Opening A R K Λ.J.n 24 (node x) Λ.h (rScale (R).p) (port (R).p x) μ puffCar V u (v*Q) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩ := s'.study; exact h21
-- useful when evolving call from this scaled Key later

include ℬ
lemma Counterfoil.realMask : RealStencil (mark128 (R).p K x Q m J X) (port (R).p x) := by
  obtain ⟨h1,-,h3,-,-,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩:=ℬ.study
  exact stencil128 _ K _ h17 h9 h10 Λ.dpos h6 h11.le h15 h8 (show m ≤ (R).p.B by omega) Q

include e h
lemma Counterfoil.aisleSale {S : Support (More (cell (Y.ir i) Λ.block Λ.R.L s))}
    (F : Buffered.Mark (cell (Y.ir i) Λ.block Λ.R.L s)) (Hf : AtSupport false S F)
    (w : Disjoint (Swell.port (R).p x) S) :
    Integrable (aisle Y s i k V F) (city N) ∧ partitionZ R Λ.U K ≠ 0 ∧
      partitionZ R Λ.U K = markedRead (1 : Buffered.Mark N) K (denZ R A K) ∧
      Journey.compass Y i k s (F* μ)= (∫ u, aisle Y s i k V F u ∂city N) / partitionZ R Λ.U K := by
  have v':= Counterfoil.billed Y s i k m ℬ
  let f : Buffered.Mark N := F* μ
  let P := drawn K
  have hx(y : Orbit N) : inner ℂ (mateK N) (acts (f (P y)) (denZ R Λ.U K y))= aisle Y s i k V F y :=
    Nest.withinBra A R K y _ v'.cost μ _ (Opening.tail A R K y v' (F (P y)) w ((Hf.allV _).sector))
  obtain ⟨ξ,δ,Ω⟩ := Tapestry.funds Y s i k (env_mult Hf.env v'.realf.foot.env) e h
  change Integrable (fun y : Orbit N => inner ℂ (mateK N) (acts (f (P y)) (denZ R Λ.U K y))) (city N) at ξ
  refine ⟨(by simp_rw [hx] at ξ; exact ξ), δ, Eq.symm (markvac K _), Ω.trans ?_⟩
  change (∫ y, inner ℂ (mateK N) (acts (f (P y)) (denZ R Λ.U K y)) ∂city N)/partitionZ R A K=_
  simp_rw [hx]
lemma Counterfoil.aisleSolo : Integrable (aisle Y s i k V 1) (city N) ∧ partitionZ R Λ.U K≠0 ∧
      partitionZ R Λ.U K = markedRead (1 : Buffered.Mark N) K (denZ R A K) ∧
      Journey.compass Y i k s μ = (∫ u, aisle Y s i k V 1 u ∂city N)/ partitionZ R Λ.U K := by
  simpa only [one_mul] using Counterfoil.aisleSale Y s i k m ℬ e h 1 (AtSupport.oneM ∅) (by simp)
end separate
end YM.CF.Py.Rate.LocalLimit.Preparation
