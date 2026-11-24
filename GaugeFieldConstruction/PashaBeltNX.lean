import GaugeFieldConstruction.MornBeltNX
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
-- actual Coalition: one spine/view/archive, one registration, one path, and APPROVED solicitation of orientation frame and dynamics. Predicate open Badge to allow further needs while preserving same purchases.
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration -- tune
namespace Glaze
variable {P:Spine}{i:Axis}{s t w:ℕ}
local notation "Ζp" => ruler P.par.block
local notation "χ"=>P.stampPin t
local notation "Nt"=> timeMesh P.par
-- not split before reaching Belt!
variable {A D:P.Glaze}(p:A.w≤w)(q:D.w≤w)
local notation "o₀"=> pinOut w
local notation "m₀"=> pinPay w
local notation "N"=> (χ (m₀:ℤ):ℝ)
local notation "M"=> (χ (w:ℤ):ℝ)
local notation "Mτ"=> (χ ((w:ℤ)+1):ℝ)
local notation "X" => belt p q
local notation "uP"=>pinDiagonal w
local notation "θP"=>P.vtile t uP
local notation "ψ"=> P.grantGapNX i t
-- profile pinPay selecting later P ledger from public
variable {Z:Lead.Clan} (ε: P.Medal Z)
variable (t i)
lemma tickRaiseNX(A:P.Glaze)(g:s≤t):P.tock t (A.glazeRiseNX g).w=P.tock s A.w:= congrArg Subtype.val (A.stampPreserveNX g)
variable {t}
lemma riseGrantNX(A:P.Glaze)(g:s≤t){a b:P.meshPin}(x:P.tock s A.w ≤ (a:ℝ))(y:P.tock s A.w ≤ (b:ℝ)):ψ (A.glazeRiseNX g).w (A.glazeRiseNX g).F (a:ℝ) (b:ℝ)=P.grantGapNX i s A.w A.F (a:ℝ) (b:ℝ):=by
   let B:=A.glazeRiseNX g; exact (hearthPayNX i t B.w (B.centers i) ((tickRaiseNX t A g).trans_le x) ((tickRaiseNX t A g).trans_le y)).same ((Habitable.forward g).1 (hearthPayNX i s A.w (A.centers i) x y))
abbrev PriceLGNX (J:P.Glaze)(h:J.w ≤ w)(l: ε.bright.w ≤ w) := belt h l
/-- tape across SAME spine and directions. bound on all larger real/non-stamp samples in transition.
 m=N rectangular width any. choose s sufficiently high. Curvature Actor Ω normalize. -/
def ChartBoatNX (A:P.Glaze)(s t:ℕ)(Rup:ℝ) (B:P.Glaze):Prop:= ∃ (h:s ≤ t)(u: ε.bright.w ≤ (A.ocSpanNX s t)), B=belt (A:=A.glazeRiseNX h) (w:=A.ocSpanNX s t) le_rfl u ∧
   ∀i:Axis,∀ a b:P.meshPin,P.tock t B.w≤ (a:ℝ)→P.tock t B.w≤ (b:ℝ)→ ‖P.grantGapNX i t B.w B.F (a:ℝ) (b:ℝ)-P.grantGapNX i s A.w A.F (a:ℝ) (b:ℝ)‖ ≤ Rup
variable(A)
lemma MayAwakeNX {e:ℝ}(H:0<e):∀ᶠ t:ℕ in atTop,∃ B:P.Glaze,ChartBoatNX ε A s t e B:=by
    let Y:= P.tock s A.w; have y:0<Y:= (A.apron s).real_width_pos P 0
    let w(i:Axis):ℝ:= ‖P.grantGapNX i s A.w A.F Y Y‖; let m:= 1+∑ x:Axis,w x
    have p(i:Axis):w i ≤ m:= (Finset.single_le_sum (f:=w) (fun _ _=>norm_nonneg _) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one) -- remove i section lean
    have hb:0< m:= add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg (fun _ _=>norm_nonneg _))
    filter_upwards[eventually_all.mpr fun i:Axis=> oreCrossNX ε y (div_pos H hb) i,eventually_ge_atTop s] with t v h
    let U:= A.glazeRiseNX h; let V:= ε.bright
    have e': P.tock t U.w=Y:=tickRaiseNX t A h
    have hu:V.w ≤ U.w:=by
      exact_mod_cast (P.tock_le ..).mp ((v (0:Axis)).1.trans_eq e'.symm)
    let X₀:= belt (A:=U) le_rfl hu
    refine ⟨X₀,h,hu,rfl,?_⟩; intro i a b k y'
    have he: Y ≤ P.tock t X₀.w:= e'.symm ▸ (P.tock_le t _ _).mpr (by dsimp only [X₀,belt]; unfold pinPay; omega)
    have hc:P.stampPin t U.w=P.stampPin s A.w:=A.stampPreserveNX h
    rw [← riseGrantNX i A h (he.trans k) (he.trans y')]; refine (BudgetBeltNX (A:=U) le_rfl hu (a:ℝ) (b:ℝ) k y').trans ?_
    have hz: P.tock s A.w ≤ (P.stampPin t U.w:ℝ):=e'.ge -- tune
    rw [show U.w=(A.glazeRiseNX h).w from rfl, riseGrantNX i A h hz hz,show ((P.stampPin t _):ℝ)=Y from e']; exact (mul_le_mul (p i) ((v i).2 Y le_rfl Y le_rfl) (norm_nonneg _) hb.le).trans_eq (by field_simp)
-- Apt tapes move & promote further
lemma lacBeamNX(A B:P.Glaze)(t:ℕ){e:ℝ}(v:ChartBoatNX ε A s t e B):(B.apron t).Beams Z.2:=by
   obtain ⟨h,u,rfl,_⟩:= v; let X₀:=A.glazeRiseNX h
   let E:=ε.bright; let f:= Vacancy.ordinate; let Y:=pinDiagonal (A.ocSpanNX s t);
   change X₀.F*P.chartAll Y E.F ∈ P.Beam t (X₀.S∪P.placeSet E.S f Y) Z.2; rw[mul_comm,Finset.union_comm]; exact Beam.join (Beam.sail (ε.first t).1 f Y) X₀.inlet (belt_pin (A:=X₀) le_rfl u _).symm
#print axioms MayAwakeNX
#print axioms lacBeamNX
end Glaze
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
