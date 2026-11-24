import SatinThinRoman
import Velour.Board.Birth
/-!
Price the EXTENSIVE sharp demand on the gap-array licenses.
Here comparison heights f,r may be lower than v-1 and we don't
have a bound on v-r.
-/
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars true
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis.Head.Etch
variable (i k:ℕ){f r v d:ℕ}{a c:ℝ}
local notation "L"=> P.R.L
local notation "Δ"=> P.block
local notation "Ω" j:max=> side Y i j
local notation "Gξ" j:max=> Vale.apt (Y.ir i) P.block P.R.L j
open Again Buffered.Afterglow.Tower.SlabMark

open VelourBoard
variable (H:Real.exp 1≤ P.x) {A b z u:ℝ} (base:f≤r)(fine:r≤v)
local notation "ε"=> meterC (hat L P.x f)
local notation "e"=> (RootBook Y i k f).p.B
local notation "K"=> tent Y H
local notation "R"=> P.R.L.val ^ (v-f)
local notation "μ" => momentm Y i v

variable (B:ℕ)(o: VelourBoard.Cell)
variable (τ: Site (side Y i f)) (F:Buffered.Family (tent Y H))
local notation "pB"=> gapMark Y i k b z base fine
local notation "πB"=> (2 * pitch (K) B)
variable (hV:ShelterCost c Y f i k)
 (h:ReadDensity Y i k A base fine b z u)
 (g:Ferry Y v i k)


include hV h g
theorem gap_board
 (t:Shield (K) B o (rural e+1) 0 (node τ))
 (fee:14*ε*((↑(2*pitch (K) B :ℕ):ℝ)^4)≤1)
 (x:exhibit Y H v i F = pB τ) 
 (l:List (VelourBoard.Tile (K))) (X Z:VelourBoard.Cell)
 (hD: Deck μ (R*B) (fun i=> (↑(R:ℕ):ℤ)*o i) F l X Z):
  ‖Journey.sharp Y H v i k (VelourBoard.Representation l)‖ ≤
     (owedF P f A 1)^l.length:=by
 let J := pB
 let D := rural e+1
 let Q := fun i' => (↑(R:ℕ):ℤ)*o i'
 have hk : f+(v-f)=v:=Nat.add_sub_of_le (base.trans fine)
 have hz: ((K).c μ).val = (R:ℕ)*(Ω f).val:=by
    rw [terrain Y H (Y.ir i) v,← refine_side,hk]
 have vp:0 < (R:ℕ):=pow_pos (P.R.L.property) _
 have hfit:= at_coarser vp hz hD.fits
 have hp:= coarser_fill vp hz hD.fill
 let G:=fun a (y:Site (side Y i f))=> Shield (K) B o D a (node y)


 have turns:∀a y,G a y→ ∀ j d,∃ y',G (tipped j d a) y' ∧
   reflMark j (PaneCut (K) ((R:ℕ)*B) Q j d) (J y)= J y':=by
    intro a y v' j d
    let s:= PaneCut (K) B o j d
    refine ⟨(plane j s).mills _ y,?_,?_⟩
    · unfold G; rw [Shape.nodex]; exact turned j d _ v'
    unfold Q; rw [scaled_plane, show (↑(R:ℕ):ℤ)* PaneCut (K) B o j d=highTurn P f v s from by unfold highTurn s; rw [Nat.cast_pow]]
    exact (gap_swing Y i k j s y g.depth g.enters base fine).symm
 let sep : Site (side Y i f)→ Site (side Y i f) → Prop:=
       fun x y=> rural e < separation (node x) (node y)
 obtain ⟨L',length,val,_,a⟩:=inscribe Y H v i G J ⟨τ,t,x⟩ turns hD.paved
   (fun _=>True) (fun _ _ _ => trivial) sep 
   (fun _ _ p q n _ _ h k=> lt_of_lt_of_le (by unfold D; omega:rural e<2*D)
      (separates hfit p q n h k))
 have r:=gap_ticket Y i k base fine L' hV h a
 rw [actualRead,val]
 refine r.trans ?_
 rw [length]

 obtain ⟨_,_,p',m',_⟩:= hV.load.health
 have hi : sites (Ω f) ≤ (πB:ℕ)^4 * (l.length:ℝ):=by
   unfold sites; have hm:=hp.1
   exact_mod_cast (
     show (More (Ω f)).val^4 ≤ (πB:ℕ)^4 * l.length from by
       change ((Ω f).val*2)^4 ≤ _
       linarith only [Nat.mul_le_mul_left 16 hm])
 have hs: 14*ε*sites (Ω f) ≤ l.length:=by
    have ht:0≤ ε := p'.le.trans m'
    nlinarith only [mul_le_mul_of_nonneg_left hi (show 0≤14*ε by linarith),
      mul_le_mul_of_nonneg_right fee (Nat.cast_nonneg (α:=ℝ) l.length)]
 unfold steamRent owedF
 rw [pow_one,mul_pow,←Real.exp_nat_mul]
 apply mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le _) (pow_nonneg p'.le _)
 push_cast; linarith
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.gap_board

