import Velour.Gathers.Rhythm
import Velour.Gathers.Totty
import Velour.Wadding.Lining
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x


local notation "⊥₀"=> P.tableau j x 0 -- change notation
local notation "ρ"=> P.wealth j x
local notation "ι'"=> P.enter j x



def macroDial (k:ℕ):ℝ≥0:=⟨P.macroStep k,(P.macroStep_pos k).le⟩
lemma dial_card(k:ℕ):0<P.macroDial k ∧ ((P.macroStep k).toNNReal =P.macroDial k) :=
 ⟨NNReal.coe_lt_coe.mp (P.macroStep_pos k), Real.toNNReal_coe⟩
def Apron.compact (D:P.Apron):(𝓗).Op:=⊥₀ (D.engine P j x)
namespace Veloured
variable {P j x}{T:ℕ→P.Apron}(h:P.Veloured j x T)
local notation "Q!"=> fun d:ℝ≥0=>h.printOp d
lemma print_tail:(Σ₀).Covetails (fun d:ℝ≥0=>h.printOp d):=by
 intro d p t; dsimp only
 rw [h.print_wrap (show (0:ℝ)<d from p)
       (show (d:ℝ)≤ ↑(d+t) from NNReal.coe_le_coe.mpr le_self_add)]
 rw [NNReal.coe_add,add_sub_cancel_left,pad_val,Real.toNNReal_coe]


local notation "t"=>P.macroDial
local notation "τ"=>P.macroStep
local notation:max "Y!" i:max=> (T i).engine P j x
local notation:max "Z!" i:max=> (T i).compact P j x
include h

lemma print_beats(k:ℕ): Gleams ℋ
    (fun i=>(Σ₀).tucked (Y! i) (t k)) (h.printOp (t k))∧
    Gleams 𝓗
    (fun i=>(Σ₁).tucked (Z! i) (t k)) (h.adorning (t k)):=by
 have u: Gleams ℋ (fun i=>(Σ₀).tucked (Y! i) (t k)) (h.printOp (t k)):=by
    let l(i:ℕ):= (T i).realWidth P j + τ k
    have g:Tendsto l atTop (𝓝 (τ k)):=by simpa using h.thin.add_const (τ k)
    refine (h.wvary (P.macroStep_pos k) g g).agree (Eventually.of_forall ?_)
    intro i; dsimp only; rw [show (T i).dye P j x (l i) (l i)=
                           P.priceCap j x (T i) k from rfl,P.priceEq,pad_val,(P.dial_card k).2]
    rfl
 exact ⟨u, (P.lyre_glow j x u).agree (Eventually.of_forall fun i=>P.lyre_heat j x (t k) (t k) (Y! i))⟩


lemma print_joint {A B:ℝ}(a:1≤A)(b:1≤B)
     (y:∀ k i:ℕ, ‖P.priceCap j x (T i) k‖ ≤ A*B^k)
     (m:ℕ)(c:B<2^m):
     (∃ X, (Σ₀).Ribs (fun i=>Y! i) (fun d=>h.printOp d) m
              (full_bill t A B m) X) ∧
     (∃ X, (Σ₁).Ribs (fun i=>Z! i) h.adorning m (full_bill t A B m) X):=by
 have v(i:ℕ):Installments ((Σ₀).tucked (Y! i)) t A B:=by
    refine ⟨a,b,fun k=>(P.dial_card k).1,P.halvesClock,fun k=>?_⟩
    have g:=y k i
    rw [priceEq,pad_val,(P.dial_card k).2] at g
    exact g
 have v'(i:ℕ):Installments ((Σ₁).tucked (Z! i)) t A B:=by
    refine ⟨a,b,fun k=>(P.dial_card k).1,P.halvesClock,fun k=>?_⟩
    refine le_trans ?_ ((v i).pay k)
    rw [tucked,tucked,Apron.compact,←P.lyre_heat]
    exact P.tableau_pay ..
 exact ⟨(Σ₀).wind_all h.print_tail v (fun k=>(h.print_beats k).1) m c,
       (Σ₁).wind_all h.adorning_covetails v' (fun k=>(h.print_beats k).2) m c⟩


lemma earned_joint (u:P.Totty j x T):
     ∃ m A X X', (Σ₀).Ribs (fun i=>Y! i) (fun d=>h.printOp d) m A X ∧
         (Σ₁).Ribs (fun i=>Z! i) h.adorning m A X':=by
  obtain ⟨C,D,b,d,y⟩:=u
  obtain ⟨m,r⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num:1<(2:ℝ))).eventually
    (eventually_gt_atTop D)).exists
  obtain ⟨⟨X,p⟩,Z,g⟩:=h.print_joint b d y m r
  exact ⟨_,_,_,_,p,g⟩
end Veloured
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
