import Gingham.Ruff.Talisman
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

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false


open Lander
variable {a c μ d}
variable {F:ℕ→Fleece P.calibration}{ν:ℕ→ℕ}
variable (β:Lander P a c μ d ν F)
   {δ t:ℝ}{X:Rialto 6 P.par.d δ t}
   (w:Anthem P a c μ d δ t X)(hp:1≤ρ)




variable {C:ℝ}

/-- Universal purchase. Call on any composition of Regalia charges; even
   **product or collision** stamps at one stage. Even time-difference stamp
   with translations in ticks and its actual width (including each tick
   shifting, and only sum prices before differentiation rescaling). -/
structure Meteor (P:Spine)(ρ:ℝ)(s:ℕ): Prop where
 late: ∀ᶠ n in atTop, Patina P ρ s (irr P n) (uvv P n)
 wings: ∀ ν:ℕ→ℕ,Tendsto ν atTop atTop → ∀{U:Finset Cover}{A:Cluster P.calibration}{d0:ℝ}
   (r:Regalia P ρ s ν U A d0){w:ℕ}{o:Cell}
   (_:Parcel P.calibration w o 0 U)
   (j:Axis)(_:o j=0)(p:0<w),
    ∃e:P.InCase j s w r.ticket,
      ‖P.Box j s w p e.card‖≤ CoinPrice P s w d0 ∧
      ∀x:P.Spectrum0 j, ‖e.charges x p‖≤CoinPrice P s w d0
 narrow: ∀ n:ℕ,(n:ℝ)≤notch P s→Fee P s n≤1
 mouth: (↑(salt P s+salt P s):ℝ)≤notch P s
 pinch:0<salt P s+salt P s

def mist(q:ℝ):ℝ:=4*Real.exp 1*q
lemma starburst(h:Meteor P ρ s){d':ℝ}
   (x:0≤d'){w:ℕ}(t:(w:ℝ)≤notch P s):
    CoinPrice P s w d' ≤ mist d':=by
 unfold CoinPrice RegisterPrice mist; rw [mul_assoc 4 _ d']
 have e:= Real.exp_monotone (h.narrow w t)
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e x) (by norm_num)

namespace Meteor
variable {A:Cluster P.calibration}{f:Family P.calibration}{S:Finset Cover}{o:Cell}
local notation "Λ" => Regalia P ρ s ν

/-- beacon for any width in fee budget, and SMALL slopes after
    eventually. uniform over **all** elections and all actors. -/
lemma parcel_small (h:Meteor P ρ s)
    (g:Tendsto ν atTop atTop)
    {w:ℕ}(p:0<w)
    (t:(w:ℝ)≤notch P s)
    (r:Λ S A C)
    (fit:Parcel K w o 0 S)(j:Axis)(u:o j=0):
  ∃e:P.InCase j s w r.ticket, ‖P.Box j s w p e.card‖≤ mist C ∧
       ∀x:P.Spectrum0 j, ‖e.charges x p‖≤ mist C:=by
  obtain ⟨e,z,b⟩:=h.wings ν g r fit j u p
  exact ⟨e,z.trans (starburst h r.pos t),fun x=>(b x).trans (starburst h r.pos t)⟩

#check stage
#check VoyageB_Board.harbor
#check scudding

lemma pass (P:Spine)(s:ℕ)(D:ℕ)(v:salt P s≤ D)(j:Axis) :
 Parcel P.calibration (D+D) (VoyageB_Board.horizon j D) 0
    (CF.Gingham.Ruff.stage (VoyageB_Board.transport P j D)
     (frond P.calibration (P.run.meter.a s))):=
   scudding v (VoyageB_Board.harbor P j D) 0 -- z cost


abbrev being(P:Spine)(s:ℕ):=salt P s
lemma ray (h:Meteor P ρ s) (r: Regalia P ρ s ν (frond K (~p~ s)) A C)
       (g:Tendsto ν atTop atTop) (j:Axis):
 let u:=being P s
 let t:=(r.leaves (VoyageB_Board.transport P j u)).ticket
 t.val= relocate K j u (A none) ∧
 ∃e:P.InCase j s (u+u) t,
  ‖P.Box j s _ h.pinch e.card‖≤ mist C ∧
       ∀x:P.Spectrum0 j, ‖e.charges x h.pinch‖≤ mist C:=by
   dsimp only
   exact ⟨rfl,h.parcel_small g h.pinch h.mouth _ (pass _ _ _ le_rfl j) j (if_pos rfl)⟩

#print axioms ray
end Meteor



include β in
lemma milky(h:Radiant P C ρ) (u:IcePath P.run (irr P) (uvv P)):
 ∀ᶠ s in atTop,Meteor P ρ s:=by
 let I:ℕ:=100+16*P.par.block.val+P.calibration.ℓ
 filter_upwards [cauldron β,h.hum,tallLaces P (I*10) 1,smallSeams P 1 zero_lt_one]
    with s a j b t
 refine ⟨j, fun ν g {U A d0} r {w o} fit j' t p=> r.sash g u j fit t p,t,?_,by unfold salt; omega⟩
 rw [←a.B,pow_one] at b
 unfold salt; apply le_trans _ b
 let z:ℕ:= (~p~ s).B
 change (↑((3*z+8+16*P.par.block.val+P.calibration.ℓ)+(3*z+8+16*P.par.block.val+P.calibration.ℓ)):ℝ)≤ I*10*(1+z)
 unfold I
 push_cast
 have t:0≤ (↑(P.par.R.L.val):ℝ)^P.par.b:=by positivity
 have j:=Nat.cast_nonneg (α:=ℝ) (P.calibration.ℓ)
 have b:=Nat.cast_nonneg (α:=ℝ) z
 nlinarith only [t,j,b]
#print axioms milky


include β in lemma valleys
 (h:Radiant P C ρ)(u:IcePath P.run (irr P) (uvv P)):
 ∃δ'>0, ∃t', ∃X':Rialto 6 P.par.d δ' t', Anthem P a c μ d δ' t' X' ∧
  ∀ᶠ s:ℕ in atTop, Meteor P ρ s ∧ Amethyst P F ρ ν s (honey P ρ δ' a c):=by
 obtain ⟨δ,t,X',v,w⟩:= Cosmos.anthem _ _ _ _ _ β.toCosmos
 exact ⟨δ,v,t,X',w,(milky β h u).and (stanza β w h.pos)⟩

