import WakeRoad.Close
import WakeRoad.Tallow
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open ArborJet Preparation Yoke.ArborJet
open Dial Pressure Stationary Regis.Circuit
open CF.Onyx
open CF.Gingham.Ruff Spine.Gingham.VoyageB
open UVNext.FreeStress
-- transport coefficients. Leaf oxygen (axes & color)
abbrev oxygen:= Lattice.PlaqAxes × SU.group.ColorIndex
def takeIn {m:ℕ}(i:Postcard m):oxygen:=(i.1.2,i.2)
def normalKernel (i j:oxygen):ℂ:= (sch (G:=SU.group) i.2 j.2:ℂ)*specter i.1 j.1 (basis 3)
lemma radiance (i j: oxygen): normalKernel i j= ((((4*Maxwell.normal:ℝ):ℂ)*(frigid j.1:ℝ))* if i=j then 1 else 0):= by
 unfold normalKernel sch specter
 rw [bare_diagonal i.1 j.1]; by_cases h:i=j
 · subst j; unfold UVNext.FreeStress.coat frigid; have t:= i.1.property; have u:i.1.val.1≠ (3:Axis):=(lt_of_lt_of_le t (Fin.le_last _)).ne
   simp only [u,false_or]; split_ifs <;> norm_num
 rw [if_neg h,mul_zero]; split_ifs with p q r <;> try simp
 · exact (h (Prod.ext q p)).elim
#print axioms radiance
-- collar uniformity
variable (P:Spine)(r:ℕ→ℕ)(h:StrictMono r)
local notation "iₛ" i:max=>P.period (P.projection.rows (r i))
local notation "kₛ" i:max=>P.cutoff (P.projection.columns (r i))
local notation "nDoc" s:max i:max=>side P.run (iₛ i) s
local notation "Mₛ" s:max i:max=>P.par.V.L.H ((P.run).uv (kₛ i)-s)
private theorem collection {X:ℕ→ Type} [∀ n,Finite (X n)] [∀ n,Nonempty (X n)]{T:∀ s:ℕ,X s→ℕ→Prop}(v:∀i:∀n,X n,∀ᶠ s:ℕ in atTop,∀ᶠ n:ℕ in atTop,T s (i s) n):∀ᶠ s:ℕ in atTop,∀ᶠ n:ℕ in atTop,∀ x:X s,T s x n:=by
 let p(s):=∀ x:X s,∀ᶠ n:ℕ in atTop,T s x n
 choose i h using fun s=> show ∃ i:X s,(∀ᶠ n in atTop,T s i n)→p s from by
    by_cases v:p s
    · exact ⟨Classical.arbitrary _,fun _=>v⟩
    unfold p at v; rw [Classical.not_forall] at v
    obtain ⟨a,t⟩:=v
    exact ⟨a,fun h=>False.elim (t h)⟩ -- `push Not` yields frequent
 exact (v i).mono fun _ t=> eventually_all.mpr (h _ t)

abbrev orzo(n:Side)(s:ℕ)(b:Bool): Vessel SU.group (More n) (CardsT P s):= elector (Pressure.radiusB (hat P.par.R.L P.par.x s)/10) (stanceR P s) b
abbrev delta_b (s j:ℕ)(x y: CardsT P s):ℂ:= (((2*(ArborJet.moment P s:ℝ):ℝ):ℂ)^4) * chipbook (M:=Mₛ s j) (orzo P (nDoc s j) s false) (orzo P (nDoc s j) s true) x y -- arg order M_
lemma p_score (q:ℝ)(h:0<q)(hr:StrictMono r):
 ∀ᶠ s in atTop,∀ᶠ j in atTop,∀ x y: CardsT P s, dist (delta_b P r s j x y) (normalKernel (takeIn x) (takeIn y)) < q:=by
 -- give default
 haveI: NeZero SU.group.lieDim:=by
    have h': Fintype.card SU.group.ColorIndex ≠ 0:=by exact_mod_cast (show (Fintype.card SU.group.ColorIndex:ℂ)≠0 from prism_nonzero)
    exact ⟨by simpa [Gauge.ColorIndex] using h'⟩
 letI :∀ s,Nonempty (CardsT P s):= fun s=> ⟨ ((⟨0,(by simp; omega)⟩,⟨(0,1),by decide⟩),0) ⟩
 have e(U D:PlaqAxes)(t k:SU.group.ColorIndex): ∀ᶠ s:ℕ in atTop,∀ᶠ j in atTop,∀ x:CardsT P s × CardsT P s,
    dist (((↑(2*(ArborJet.moment P s:ℝ):ℝ):ℂ)^4)*axialKernel (nDoc s j) (Mₛ s j) x.1.1.1.val (adress P s true x.2.1.1.val D) U D t k) (normalKernel (U,t) (D,k)) < q :=collection (fun y=> eventually_curry_iff.mp (Metric.tendsto_nhds.mp (purchase P r hr (fun i=> (y i).1) (fun i=> (y i).2) U D t k) q h))
 let v (i j:oxygen):= e i.1 j.1 i.2 j.2
 filter_upwards [eventually_all.mpr (fun i=> eventually_all.mpr (v i))] with s l
 filter_upwards [ eventually_all.mpr (fun i=> eventually_all.mpr (l i))] with j u x y
 let a:=takeIn x; let b:=takeIn y
 have ht := u a b (x,y)
 have h':=compass_pose P s (nDoc s j) true y
 change dist (_*coupon ((wrap (More (nDoc s j))) ↑x.1.1,x.1.2) ( (wrap (More (nDoc s j))) (adress P s true y.1.1.val y.1.2),y.1.2) x.2 y.2 (Mₛ s j)) _ < _ at ht
 rw [h'] at ht; exact ht
#print axioms p_score
