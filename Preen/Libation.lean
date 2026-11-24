import Preen.Ultima
import Preen.FoyerX
import Preen.Weights
import Risa.Engage
import Preen.Spurt
import Risa.SeedBox
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
local notation "I"=>Fin (cardD P A s)
local notation "Nc" i:max=> count P.run s i
local notation "Y"=>P.run
local notation "π₀" i:max => P.period (P.projection.rows i)
local notation "ζ₀" i:max => P.cutoff (P.projection.columns i)
variable (w:ℕ)(h:withinT o w)(R:Pilot P s A o b)(hS:0<P.payday s)
local notation "S₀"=>spots P s w o A
local notation "Z"=>trialY P s w o b R.price A
-- pair fit.need hot_dock.Ver
variable (pc:BoltCharge P.run)(pH:∀ᶠ s:ℕ in atTop,∀ i k,(P.run.voyage i).kick≤ k → s ≤ P.run.uv k → closeDen P.run s i k)
def Hugeβ (P:Spine)(s A:ℕ):Prop:=∀ C:ℝ,∀ᶠ i:ℕ×ℕ in atTop,∀ hw:(P.run.voyage i.2).kick ≤ i.1,Ferry P.run s i.2 i.1∧ ∀ {n₀:Bool}{u:Bool→Skye.Seat (count P.run s i.2)}{d:ℝ}{t:Bool→Signed},|berlin P.run A s i.2 i.1 n₀ u t-d| *scaleY (hat P.par.R.L P.par.x s)^A ≤1→ |d|≤C→ ∀ x y:boyQ P.run A s i.2 d n₀ u t, ∀ m:ℕ,m+addgap (P.calibration) ≤ (count P.run s i.2).val → (∀ a:Axis,cows a (x.S∪y.S) m) → Disjoint x.S y.S → ‖solder P.run i.2 i.1 hw s (Sway x*Sway y)‖ ≤ Real.exp ((8*parcelF (hat P.par.R.L P.par.x s))*(4*((m+addgap (P.calibration):ℕ):ℝ))^4+9)
include pc pH in
lemma fuelAgenda :∀ᶠ s:ℕ in atTop,Hugeβ P s A:=withinPair P.run A P.large pc pH -- parameter order check
abbrev school(P:Spine)(s w A:ℕ):= 8*parcelF (hat P.par.R.L P.par.x s)*(4*(((2*slip P s w A+addgap (P.calibration)):ℕ):ℝ))^4
include h R hS
/- on P.E purchases.Family Q call.POS.Existing tags.Solder.Bro. -/
lemma eclipse (B:Hugeβ P s A):
 ‖P.E s (P.reflectTest 3 (Z)*(Z)).val‖≤ Real.exp (school P s w A+9):=by
 let L:= spots P s w o A; let M:= trialY P s w o b R.price A; let D:= (P.reflectTest 3 M*M).val
 have hg:InTest K true L false M.val:= (Tapestry.locates ..).1 (zoned P ..)
 have he:InTest K true (Tower.reflectedBox 3 0 L∪L) false D:=InTest.mul ((Tower.axial K _ _ hg).mono Finset.subset_union_left) (hg.mono Finset.subset_union_right)
 obtain ⟨q,hQ⟩:=Journey.valuation P.run P.large he; let Q:= BQueue.stay he (add_pos_of_nonneg_of_pos (pay_nonneg (F:=D) hQ) zero_lt_one:0<q+1) (fun m i=>(hQ m i).trans (le_add_of_nonneg_right zero_le_one))
 have hv:= (hot_deck P.run P.large P.law s P.history _ _ Q).norm.comp R.trans.tendsto_atTop
 apply le_of_tendsto hv
 let ξ:=fun i:ℕ=> ((ζ₀ i),(π₀ i))
 have hm:Tendsto ξ atTop atTop := ((P.law.pick.grow_k.comp P.history.growsB).tendsto_atTop.prodMk ((P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop)).mono_right (by rw [prod_atTop_atTop_eq]) -- check
 have ht(v:ℕ): ∀ᶠ i:ℕ in atTop, v+addgap K ≤ (Nc (π₀ i)).val:= ((count_grows ..).comp ((P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop)).eventually_ge_atTop _
 have hf:= (P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop
 let ρ(i:ℕ):= ξ (R.station i)
 have hx:= hm.eventually (B |R.price|)
 have hy:∀ᶠ i:ℕ in atTop, |boarding P s A o b (R.station i)-R.price| *(θ)^A ≤ 1:=((R.market.sub_const R.price).abs.mul_const ((θ)^A)).eventually (ge_mem_nhds (show |R.price-R.price| *(θ)^A <1 from by simp))
 let e:= 2*slip P s w A
 filter_upwards [hy,R.trans.tendsto_atTop.eventually (((hx.and (P.history.finance s)).and (hf.eventually (coords_e P s w o A))).and ((hf.eventually (locale_dist P s w o A h)).and (ht e)))] with i hp hc
 let d:= R.station i; let m:=π₀ d; let k:=ζ₀ d
 change ‖hot P.run P.large s m k D‖≤ _
 obtain ⟨⟨⟨ho,hB⟩,t⟩,p,v⟩:=hc
 obtain ⟨F,H,H0⟩:=platterE P s w o b R.price A m hS t
 have hx := (ho hB.depth).2 hp (le_rfl) (flipS 3 0 F) F e v (by change ∀ j,cows j (hyphen 3 0 F.S∪ F.S) _; rw [H]; exact walls_cost P s w o A h m) (by change Disjoint (hyphen 3 0 F.S) F.S; rw [H]; exact p)
 rw [hot_pay P s m k hB.depth]
 let f:=distribute P.run P.large s m
 have ht:f D=Sway (flipS 3 0 F)*Sway F:=by
    change distribute P.run P.large s m (mirror K 3 0 (Z).val * (Z).val)=_; rw [(distribute_arith P.run P.large s m (mirror K 3 0 (Z).val) (Z).val 0).2.1,(distribute_arith P.run P.large s m (Z).val 1 0).2.2.2.2,H0, show reflMark 3 0 (Sway F)= Sway (flipS 3 0 F) from mirrorS (q:=0) F]
 change ‖solder P.run m k _ s (f D)‖≤ _; rw [ht]; exact hx
#print axioms eclipse
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
