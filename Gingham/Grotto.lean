import YM.SU5.Six.Photos
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)
local notation "A"=> P.Ensemble 3
local notation "W"=> P.Hil 3
local notation "R"=> P.vacuum 3
local notation "S"=> P.Spectrum0 3

/- Joint joint bare calibration used throughout. Bare prescriptions on any
    volume by cutoff (though physical limits ONLY taken on chosen jointly
    advancing volumes/cutoffs). -/
open Dial Reed Pastry
namespace Diary

abbrev irr(e:ℕ):ℕ:= P.period (P.projection.rows e)
abbrev uvv(e:ℕ):ℕ:= P.cutoff (P.projection.columns e)
abbrev mm(e:ℕ):= P.run.ir (irr P e)
abbrev nn(e:ℕ):= P.run.uv (uvv P e)
lemma rising_i: StrictMono (irr P):= P.law.pick.grow_i.comp P.history.growsA
lemma rising_k: StrictMono (uvv P):= P.law.pick.grow_k.comp P.history.growsB

lemma rising_depth:StrictMono (nn P):= P.run.uv_grows.comp (rising_k P)
lemma atHeight(s:ℕ): ∀ᶠ e in atTop, Ferry P.run s (irr P e) (uvv P e):=
 P.history.finance s
abbrev gram (e:ℕ):= ((P.run.voyage (irr P e)).X (nn P e)).gram
open Set
def bareβ (n:ℕ):ℝ:= if p:n∈range (nn P) then (gram P p.choose n).beta else 0
lemma pivots (e:ℕ): bareβ P (nn P e)= (gram P e (nn P e)).beta:=by
 let h:nn P e∈range (nn P):=mem_range_self e
 rw [bareβ,dif_pos h,(rising_depth P).injective h.choose_spec]

/-- Common density formula at cutoff depth n on any designated torus. -/
def uniformDen (n:ℕ)(m:Side): Pane (P.par.Ctor m n) → Phys (P.par.Ctor m n) :=
    fun V=> Vale.capP (K:=P.par.K) P.par.U (bareβ P n) (P.run.meter.a n) V
lemma uniformDen_on (e:ℕ)(z :Orbit (side P.run (irr P e) (nn P e))) :
   denZ (gram P e (nn P e)) P.par.U ((P.run.voyage (irr P e)).CapeT (nn P e)) z
      = uniformDen P (nn P e) (mm P e) z.1:=by
 unfold uniformDen
 rw [pivots]
 exact P.bare_density ..

local notation "K"=>P.calibration
abbrev rawE(s e:ℕ) (f:P.Test): ℂ:=
    Journey.sharp P.run P.large s (irr P e) (uvv P e) f.val


lemma rawE_joint(s:ℕ)(f:P.Test): Tendsto (fun e=>rawE P s e f)
   atTop (𝓝 (P.E s f.val)):=by
 obtain ⟨L,h⟩:= findsBay _ f
 have hL:InTest K true L false f.val:= h
 obtain ⟨c,hc⟩:=Journey.valuation P.run P.large hL
 obtain ⟨_,_,H⟩:= P.history.implements s L
 have hpc:pay f.val c:=hc
 have v:0<c+1:=by linarith [pay_nonneg hpc]
 refine Metric.tendsto_nhds.mpr fun ε hε=>?_
 filter_upwards [H (ε/(c+1)) (by positivity)] with e ht
 have he: ‖rawE P s e f - P.E s f.val‖ ≤ ε/(c+1)*c:=
    (ht f.val hL c hc).2.2.2.2.1
 rw [dist_eq_norm_sub]
 refine he.trans_lt ((mul_lt_mul_of_pos_left (show c<c+1 by linarith)
   (div_pos hε v)).trans_eq (div_mul_cancel₀ _ v.ne'))


lemma rising_size: StrictMono fun e=> (mm P e).val:=P.run.ir_grows.comp (rising_i P)

