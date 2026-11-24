import YM.SU5.CompassRose.Ranunculus

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open CF.Fir CF.Jill CF.Flare CF.Kea CF.Emu Lamour Lamour.Bridge
open WakeInvestment Gleam Gleam.Wake Regis.Head.Brecht
variable (P : Spine)(v : ℕ→ℕ)(β : ℕ→ℝ) (T : Pools P v β)
local notation "pᵥ" z:max => Rose.period P (v ((z:ℕ×ℕ).2))
local notation "cᵥ" z:max => Rose.cutoff P (v ((z:ℕ×ℕ).2))
local notation "O" z:max => orbitSize P v z
local notation "Y" => P.run
local notation "R" s:max A:max => sPow P.par s A
variable {I:Type*} (W:I→ℕ→Staff)

section hierarchy
-- includes exact Touch on spins for repeated-appointments and refuses any gauge contact
-- unless further calibration. Necessary when allowing layouts with coincident projection in spatial axis.
variable {A:ℝ}{E w:ℝ}(p:0<A)(a:Investment P.par E w) (U : Dispatchers P.par)(M : Meritorious P.par)
variable (X : I→Gaia)(F : I→ PlaqAxes)(L : I→DirSpin) (q r : I→ℕ→ℕ)
  (t:∀ i, LayoutBudget P A (X i) (W i) (q i) (r i) (F i) (L i)) (l:List I) (e:l.Pairwise fun i j=> X i ≠ X j) (c:∀ i j,X i=X j→ ∀ᶠ s : ℕ in atTop, (W i s).u=(W j s).u)
abbrev bill (X : I→Gaia) (F : I→PlaqAxes) (L:I→DirSpin) (l:List I) := roseMoment l (spinRow X L) (tideRow X F)
lemma blooms_accept {C : I→ Gaia} {X' : Type*} (f : Filter X') (B:X'→ CTag I→CTag I→ℂ)
    (S : CTag I → CTag I →ℂ) (V:X'→sIndex I→sIndex I→ℂ) (U:sIndex I→sIndex I→ℂ)
    (v:∀ i j,Tendsto (fun x=> V x i j) f (𝓝 (U i j))) (e:l.Pairwise fun i j=> C i≠ C j)
    (h: ∀ i j,C i.1 ≠ C j.1 → Tendsto (fun x=>B x i j) f (𝓝 (S i j))) :
    Tendsto (fun x=> roseMoment l (V x) (B x)) f (𝓝 (roseMoment l U S)) := by
  apply invest_limit l f (fun t x=> charge t * RoseGaussian.exchange (B x) t.length (t.map panelColor) * runes (V x) (stream t)) _
  intro q H 
  refine ((RoseGaussian.exchange_limit S f B _ _ ?_).const_mul _).mul (spin_leap f U V v (stream q))
  apply List.pairwise_map.mpr; refine (show q.Pairwise (fun a b=> C a.1≠C b.1) from (List.pairwise_map («R»:=fun a b:I=> C a ≠ C b) (f:=Prod.fst)).mp (H.symm ▸ e)).imp (fun g=> h _ _ g)
variable [Fintype I]
include t T p c e
lemma finite_pose : Tendsto (fun z:ℕ×ℕ => seatT Y z.1 (pᵥ z) (cᵥ z) (cargoShip P v W z) (checkBy P v W l A z) (κFix β z.1)) bobbin (𝓝 (bill X F L l)) := by
  let Vv(z:ℕ×ℕ):= meshRow P v W A z; let K(z:ℕ×ℕ):=originBond P v β W A z
  let B(z:ℕ×ℕ)(i j):=RoseGaussian.cost (K z i) (K z j)
  have he:Tendsto (fun z=> roseMoment l (Vv z) (B z)) bobbin (𝓝 (bill X F L l)):= blooms_accept l bobbin B (tideRow X F) Vv _ (pole_value P v T.up X L W (fun i=>(t i).spin_target) (fun i=>(t i).spin) c p) e (tide_limit P v β T p W t)
  apply he.congr'
  rw [Filter.EventuallyEq,bobbin_for]
  refine Eventually.of_forall fun s=> ?_
  have h : 1 ≤ P.par.K.j := by rw [P.par.kJ]; decide
  filter_upwards [(thicken P T.up s).eventually (ownsHalo h)] with n hv; exact (flower_price P v β W (A:=A) (s,n) l ((hv (Vale.val_e ..)).1)).symm
include a U M
lemma moving_prices : Tendsto
   (fun z:ℕ×ℕ=> Journey.sharp Y P.large z.1 (pᵥ z) (cᵥ z) (Papal.household P.calibration (clusterW P β W q l A z.1)))
   bobbin (𝓝 (bill X F L l)) := by
  let Q(z:ℕ×ℕ):= seatT Y z.1 (pᵥ z) (cᵥ z) (cargoShip P v W z) (checkBy P v W l A z) (κFix β z.1)
  let Z(z:ℕ×ℕ):= Journey.sharp Y P.large z.1 (pᵥ z) (cᵥ z) (Papal.household P.calibration (clusterW P β W q l A z.1))
  have h0:Tendsto (fun i=> Z i-Q i) bobbin (𝓝 0):= by
    rw [tendsto_zero_iff_norm_tendsto_zero]; let f(s:ℕ):= hat P.par.R.L P.par.x s
    refine squeeze_zero' (g:=fun z : ℕ×ℕ=> chip (f z.1) (-3)) (Eventually.of_forall fun _=> norm_nonneg _) (many_compass P v β W X q r T p l a U M t) ?_
    exact ((rchip (A:=A) P 0).comp Rose.runway).congr fun z:ℕ×ℕ=>by change _ ^ (0:ℕ)*_ = _; rw [pow_zero,one_mul]
  have hp:= h0.add (finite_pose P v β T W p X F L q r t l e c); rw [zero_add] at hp; exact hp.congr fun i => sub_add_cancel (Z i) (Q i)
local notation "P!" s:max => Papal.household P.calibration (clusterW P β W q l A s)
omit a U M p T c e in
lemma art_title (s:ℕ) : TestFamily P.calibration true (P! s) ∧ CovCover P.calibration (P! s) := by
  induction l with
  | nil=> exact ⟨TestFamily.oneT,fun _ _ _=>(map_one _).symm⟩
  | cons i l H =>
    let G:=offers P A s (W i s) (q i s) (κFix β s); have hv:= center_goods P (t i) s (κFix β s); let k:=Papal.household P.calibration (clusterW P β W q l A s)
    refine ⟨(aux_test hv.1).mul H.1,?_⟩; intro m g x; change (G*k) m _=twist _ ((G*k) m _); simp only [Pi.mul_apply,map_mul]; exact congrArg₂ (·*·) (hv.2 m g x) (H.2 m g x)

lemma wake_earning : Tendsto (fun s=> P.E s (P! s)) atTop (𝓝 (bill X F L l)) :=
  reels (f:=fun z:ℕ×ℕ=> Journey.sharp Y P.large z.1 (pᵥ z) (cᵥ z) (P! z.1))
   (Eventually.of_forall fun s=> (sharp_on_track Y P.law P.history s (art_title P β W X F L q r t l s).1).comp T.up.tendsto_atTop)
   (moving_prices P v β T W p a U M X F L q r t l e c)
end hierarchy
#print axioms wake_earning
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
