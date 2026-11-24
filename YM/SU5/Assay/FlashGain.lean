import YM.SU5.Assay.NeumSeed
import YM.SU5.Cordial.Grotto
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
/-!
# Every clan has flashes admitting Neumann decay

The aperture for a single flash needn't have zero true projection as its
physical size shrinks. We find FIXED n (independent of the resolution s),
not performing our tag construction on a moving UV hypothesis. The bounds
are in the mean boxes and hold simultaneously with the measurements, without
demanding new flags on the elected character.
-/
variable {P:Spine}{R:P.Register}{u v:ℝ}{X:Supplier}{j:Axis}{n:ℕ}
local notation "K"=>P.calibration
variable (P)(Z:Lead.Clan)

lemma defaultBay (n:ℕ): P.defaultR Z n ∈bay K (P.flash n).patio true:=
    widerBay K _ _ (((obs_in ..).1 (P.naturalR Z n)).1)
lemma defaultColor (n:ℕ): P.defaultR Z n∈enclave K:=
   ((obs_in ..).1 (P.naturalR Z n)).2
lemma flashTaste (h:Tasting.Paid P.par)(n:ℕ):∃ y:ℂ,P.Taste (P.defaultR Z n) (P.flash n).patio y:=
 P.hasTaste h ⟨_,porchGone _⟩ (((obs_in ..).1 (P.naturalR Z n)).1) (P.defaultColor Z n)
private lemma strictAbove(p:ℕ→ℕ):∃ f:ℕ→ℕ,p≤f∧StrictMono f:=by
 let f : ℕ→ℕ:= Nat.rec (p 0) (fun i v=>max (p (i+1)) (v+1)); exact ⟨f,fun i=> by cases i; exact le_rfl; exact le_max_left .., strictMono_nat_of_lt_succ (fun i=> show f i < max _ (f i + 1) from (Nat.lt_succ_self _).trans_le (le_max_right ..)) ⟩
variable {P}
lemma vividAt (h:uniform P R X u v)(w:Tasting.Paid P.par)(N:ℕ):∃ n≥N, ∃ y:ℂ,y≠0 ∧
    P.Taste (P.defaultR Z n) (P.flash n).patio y:=by
 by_contra g
 have hx(n:ℕ)(e:N≤n):∀ᶠ s:ℕ in atTop, ∀ x:P.Spectrum0 3,‖P.singleState 3 s x (P.defaultR Z n)‖≤1/2:=by
   obtain ⟨y,f⟩:=P.flashTaste Z w n
   obtain rfl:y=0:=not_not.mp fun t=>g ⟨n,e,y,t,f⟩
   simpa only [sub_zero] using Taste.watch (P.defaultBay Z n) (P.defaultColor Z n) f 3 _ (show (0:ℝ)<1/2 by norm_num)
 obtain ⟨r,t,p,H⟩:= outing h keyV keyV_positive (fun _=>N)
 choose z hz using fun i=>eventually_atTop.mp (hx (r i) (t i))
 obtain ⟨c,a,b⟩:=strictAbove fun i=>max (z i) (p i)
 obtain ⟨q,_,w⟩:= H c b fun i=>(le_max_right ..).trans (a i)
 obtain ⟨x,v⟩:= w.exists
 have ht:=(aboutOne Z q v keyV_go).norm.eventually (lt_mem_nhds (show 1/2<‖(1:ℂ)‖ by norm_num))
 obtain ⟨i,f⟩:= ht.exists
 exact not_lt_of_ge (hz i _ ((le_max_left ..).trans (a i)) _) f

theorem residualFlash (h:uniform P R X u v)(w:Tasting.Paid P.par): ∃ n>P.calibration.ℓ,∀ j, ∃ d a c,
 P.ResidualTag j (P.defaultR Z n) (P.flash n).patio d a c:=by
 obtain ⟨n,e,_,p,g⟩:= vividAt Z h w (P.calibration.ℓ+1)
 exact ⟨n,e,fun j=>Taste.neum P g (P.defaultBay Z n) p j⟩

#print axioms residualFlash
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
