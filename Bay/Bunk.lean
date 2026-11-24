import Bay.Hailer
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


open Buffered
namespace Berth
variable (w:Berth) 
lemma threshold_ne: IsleB SU.group w.R.p.threshold:=by
 obtain ⟨p,_,_,t,_⟩:=(w.P.run.voyage w.i).paths (w.P.run.uv w.k)
 unfold R RootBook; rw [t]; exact p.can.isle w.s

lemma threshold_pass:∀ᵐ u:Orbit w.side ∂city w.side,FleetS w.R.p.threshold u.1:=
  (measurePreserving_fst (μ:=prior SU.group (More w.side)) (ν:=depot w.side)).quasiMeasurePreserving.ae (threshold_ne w _)

variable {I:Type}[LinearOrder I][Fintype I]

structure Quest
 (T:I→footprint w.side) (b:I→ℝ) 
 (o:I→Stencil w.side) (y:I→phy w.side)
 (v:I→Sour.Bag w.side) (G:Orbit w.side→Prop):Prop where
  pair: ∀ i, Accompanies (T i) (b i) (o i) (y i)
  pilots (u)(i): G u → ∀ p, w.sockets u p (y i) (v i)

def pages (o:I→Stencil w.side)(l:List I):Mark w.side:=
   toMark (l.map o).prod
def scroll (y:I→phy w.side)(l:List I):Orbit w.side →Phys w.side:=
   fun x=>acts ((l.map y).prod x) (w.volume x)

/-- locus of lifted reading equality -/
def admission(G:Orbit w.side→Prop)(u:Orbit w.side):Prop:= G u∧FleetS w.R.p.threshold u.1

structure Bunk (G:Orbit w.side→Prop)
 (V:Mark w.side)(Y:Orbit w.side→ℂ)(d:ℝ):Prop where
 priced:‖w.sharp V‖ ≤ d*w.sigma
 isLit (u):w.admission G u → letterRead (V (Advance.drawn w.K u)) (w.volume u)=Y u
 int:Integrable Y (city w.side)
 paid:w.sharp V=(∫ x,Y x ∂city w.side)/w.cap

abbrev verse (V:Mark w.side)(f:Orbit w.side→Phys w.side)(x:Orbit w.side):=
 letterRead (V (Advance.drawn w.K x)) (f x)

/-- tip ket assertions on the squarefree algebra, AND signed physical readings. Signed comparison uses additional disjointness for test and amongst labels, may depend on l in applications. -/
structure Reloaded
 (T:I→footprint w.side)(σ:I→Seat w.side)(b:I→ℝ) 
 (o:I→Stencil w.side) (y:I→phy w.side)
 (U:Mew.Key I→ RegBudget w.side)(W:Mew.Key I→ ForceBudget w.side)
 (G:Orbit w.side→Prop):Prop where
  thick:∀ᵐ u:Orbit w.side∂city w.side,w.admission G u
  charges:w.kick→ w.levy
  entry (l:List I)(u)(k:ψS σ l)
   (ind:independent l T)(t:w.admission G u):
    w.winE U W l u=w.scroll y l u
  confirms (l:List I)
    (k:ψS σ l)(ind:independent l T)
    (S:footprint w.side)(v:Bool)
    (V:Mark w.side)(z:AtSupport v S V)
    (q:Disjoint (stair l T) S)
    (e:w.kick)
    (j:ℝ)(u:∀ x,‖V x‖ ≤ j):

    w.Bunk G (w.pages o l * V)
      (w.verse V (w.winE U W l)) ((l.map b).prod*j)

variable {w}
 {T:I→footprint w.side}{σ:I→Seat w.side}{b:I→ℝ}
 {o:I→Stencil w.side}{y:I→phy w.side}
 {v:I→Sour.Bag w.side}
 {G:Orbit w.side→Prop}
 {a c:ℝ}{M L m s:ℕ} {F C D:ℝ→ℝ}

variable (w:Berth) in
lemma unhit (G:Orbit w.side→Prop)(h:∀ᵐ u ∂city w.side,G u):
   ∀ᵐ u∂city w.side,w.admission G u:= h.and (w.threshold_pass)

omit [LinearOrder I] [Fintype I] in
lemma lengthL (l:List I)(k:ψS σ l):l.length ≤ w.lampCap:=
 (List.length_map ..).symm.trans_le (k.length_le_card)

variable {r:blazeK w.side} {E B:I→ Aura w.side→ℝ}

lemma shrug (h:w.Rig a c m)
 (g:w.Thermal M L F C D r)(i:Multiplicity σ M)
 (d:w.Cached σ v L E B C D)
 (j:w.Quest T b o y v G)(k:∀ᵐ u∂city w.side,G u)
 (u:w.lampCap ≤ s)(v:Ids w.side):
 w.Reloaded T σ b o y (w.flareE d σ s v) (w.flareF d σ s) G:=by
 have limit:=w.unhit G k
 have d0:1 ≤ s:= (Fintype.card_pos (α:=Seat w.side)).trans_le u -- .le
 let U:=w.flareE d σ s v
 let W:=w.flareF d σ s

 have entry:∀(l:List I)(x),ψS σ l → independent l T → w.admission G x →
    w.winE U W l x=w.scroll y l x:=by
    intro l x t ind p
    rw[scroll,collapsed]
    exact primesw x y g i d (emblem_pure h x) (fun f=>j.pilots x f p.1 _) s d0 v l t
     ((lengthL l t).trans u) p.2 (reorg l j.pair ind x)
 refine ⟨limit,charges h,entry,?_⟩
 intro l p t S k V z e0 e dV gV
 let m0:=march l j.pair t
 let Z:=w.pages o l
 let st:=Z*V
 let Y:=w.verse V (w.winE U W l)
 let K:=fun x=>letterRead (st (Advance.drawn w.K x)) (w.volume x)
 have f(x)(r:w.admission G x):K x=Y x:=by
    unfold Y verse
    rw [entry l x p t r]
    exact m0.waltz z e0 ..
 have tell:K=ᵐ[city w.side]Y:=limit.mono f
 refine ⟨sharp_sup h e st (fun t=>(norm_mul_le ..).trans
    (mul_le_mul (m0.pay.purse t.1) (gV t) (norm_nonneg _)
      ((norm_nonneg _).trans (m0.pay.purse t.1)))),f,?_,?_⟩
 · exact (mark_integrable h.pulse.roof.bill (supportProd m0.pay z)
    (Marks.can_read w.sig w.U w.R w.K (charges h e))).congr tell
 rw [←integral_congr_ae tell];rfl
end Berth
