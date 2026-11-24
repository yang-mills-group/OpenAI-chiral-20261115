import Bay.D.Brig
import Bay.D.Rondo
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

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

variable (P:VacuumSelection.Spine)
local notation "K" => P.calibration
local notation "Y" => P.run
local notation "H" => P.large
local notation "X" => P.Test
def scale (P:VacuumSelection.Spine)(s:ℕ):ℝ:=hat P.par.R.L P.par.x s
abbrev Guest := Option (P.Spectrum0 (3:Axis))
variable (s:ℕ)

def reception: X →ₗ[ℂ] ℂ where
 toFun f:=P.E s f.val
 map_add' f g:=Tower.E_add Y H P.law s f.property g.property
 map_smul' a f:=Tower.E_scale Y H P.law s f.property a
def Price : Guest P → X →ₗ[ℂ] ℂ
| none=> reception P s
| some y=>P.singleState 3 s y
lemma price_star (g:Guest P)(f:X): star (Price P s g f)=Price P s g (P.reflectTest 3 f):=by
 cases g with
 | some y=> change star (P.chi _ y _)=P.chi 3 y _
            rw [←map_star,P.reading_star]
 | none=>
   change star (P.E s f.val)=P.E s (P.reflectTest 3 f).val
   rw [← P.occupied 3 s f,← P.occupied 3 s (P.reflectTest 3 f),← P.reflected]
   let e:=P.groundZero 3; let v := P.compressed 3 s f
   exact (inner_conj_symm (𝕜:=ℂ) (v e) e).trans
     (ContinuousLinearMap.adjoint_inner_right v e e).symm
lemma price_one (g:Guest P): Price P s g 1 =1:=by cases g with|none=>exact Tower.E_unit _ _ P.law _ | some y=> exact chargesUnit ..

lemma price_slide (g:Guest P)(n:ℤ)(f:X):
 Price P s g (P.shifts 3 n f)=Price P s g f :=by
 cases g with
 | some y => exact P.slide_single 3 y s n f
 | none =>
   rw [Price]
   change P.E s (P.shifts _ _ f).val=_ 
   suffices P.E s (P.shifts 3 n f).val=P.E s f.val from this
   rw[←P.occupied 3 s (P.shifts 3 n f),←P.occupied 3 s f]
   have h:P.compressed 3 s (P.shifts 3 n f)=P.compressed 3 s f:=congrArg Subtype.val (P.shifted_read ..)
   rw[h]

def Encore (i k:ℕ→ℕ):Prop:= Row P i k ∧ ∀ᶠ r in atTop, Canopy Y s (i r) (k r) H
variable {i k:ℕ→ℕ} {S:Finset Cover} {m:ℕ→ℝ}
local notation "N" r:max=> Papal.count Y s (i r)
local notation "Ω"=>scale P s
def pegN (a:ℕ) (x:Buffered.Family K): Mark (Papal.count Y s a) :=
 arrange _ _ (Journey.terrain Y H (P.run.ir a) s) (x (momentm Y a s))

structure Noria (S:Finset Cover):Prop where
 able: Able K Ω
 gauges :∃t B, Feeling K 3 t B S ∧ taps K*t≤B ∧ B ≤ atRate 12 Ω

/-- Per-tilt receipt with changing cost and queue limit. Need only appear eventually. -/
structure Gigue (i k:ℕ→ℕ)(z:ℂ)(m:ℕ→ℝ)(f:X)(F:ℕ→Buffered.Family K)(S:Finset Cover):Prop where
 rangeK: Noria P s S
 shape: BQueue S F f.val
 roster:∀ᶠ r:ℕ in atTop, ∃ (o d:Seat (Papal.count Y s (i r)))
    (x:Pane (Papal.count Y s (i r))→ℝ) (W:Chalk (More (Papal.count Y s (i r))) ℝ), Lease Y s (i r) (k r) o d x W ∧ beans Y s (i r) (k r) W=m r ∧
    Staff (Tunic o d x z) (pegN P s (i r) (F r)) S 1

theorem music {z:ℂ}(u:‖z‖≤thetaB Ω)
 {μ:ℝ} (b:Tendsto m atTop (𝓝 μ)) (e:Encore P s i k)
 {f:X} {F:ℕ→Buffered.Family K} (p:Gigue P s i k z m f F S) (D':P.Register) (g:Guest P):
 ‖Price P s g f‖ ≤Real.exp (z.re*μ + tilt Ω) ∧ |μ|≤Ni Ω :=by
 obtain ⟨t,B,h,q,v⟩:=p.rangeK.gauges
 let c:=Real.exp (z.re*μ+tilt Ω)
 have C n: ‖P.E s (singing K 3 t f.val n)‖≤c^(2^n:ℕ):=by
   have ey:=eclat Y H s t B S h q v p.rangeK.able n
   obtain ⟨T,w⟩:=songqueue 3 t p.shape n
   have hy:=quickens P s e.1 w
   have H' := (((b.const_mul z.re).add_const (tilt Ω)).const_mul ((2^n:ℕ):ℝ)).rexp
   unfold c;rw[←Real.exp_nat_mul]
   refine le_of_tendsto_of_tendsto hy.norm H' ?_
   filter_upwards [e.2,p.roster,e.1.growing.eventually ey] with r a d l
   obtain ⟨o,v,x,W,hv,hx,hW⟩:=d
   have ht:=l _ a _ _ _ _ _ hv u _ hW
   rw[hx] at ht
   exact ht
 refine ⟨?_,le_of_tendsto b.abs ?_⟩
 · cases g with
   | none=> have Q:=C 0; rw[singing,pow_zero,pow_one] at Q; exact Q
   | some y=> exact reap _ _ P D' _ f p.shape.landing h.1 (Real.exp_pos _) (fun n=>C (n+1)) y
 filter_upwards [p.roster] with j k
 obtain ⟨o,d,x,W,h,r,_⟩:=k
 show |m j| ≤ _
 rw [←r]
 exact h.flavor_fee
