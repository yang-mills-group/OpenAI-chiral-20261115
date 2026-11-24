import SatinThinCoalition
import Velour.Crepe.Sheen

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
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
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid
variable (P:Spine) (j:Axis)(x:P.Spectrum0 j)
local notation "σ"=> P.physicalEnergy j x
local notation "Υ" => timeMesh P.par
variable {ι : Type} (A:ι→ P.Apron) (I:Finset ι)(h:Axis→ℕ)(s:ℕ)
variable (u:∀ j,0< h j) (t:∀ i∈I,(A i).s ≤ s) (f:∀ i∈ I,∀ j,(A i).zoom P s j ≤ h j)


include t in
lemma canvas_velour (B:P.Apron)(z:ι→ℂ)(p:B.F= ∑ i∈ I,z i • (A i).full P s)
    (v:B.s=s)(f:∀ i∈ I,(A i).realWidth P j ≤ B.realWidth P j)(r:ℝ)(h:B.realWidth P j ≤ r):
    B.velour P j x r=∑ i∈ I,z i • (A i).velour P j x r:=by
    subst s
    let D:=B.realWidth P j
    let n:=B.u j
    have e:=B.pos j
    have T:bell Υ B.s (n+n:ℕ) - D = D:=by rw [Nat.cast_add,bell_add]; exact add_sub_cancel_left _ _
    let J(i:ι):= z i • (A i).velour P j x D
    let q:=B.dyedHere P j x n D D rfl T (le_refl _) (le_refl _)


    have u': B.velour P j x D = ∑i∈I,J i:=by
       refine q.unique ?_; rw [p,map_sum]
       refine ThreadOp.sum (add_pos e e) _ fun i y=> ?_
       rw [map_smul]
       exact ((A i).dyedAbove P j x (t i y) n _ _ rfl T (f i y) (f i y)).smul _
    rw [B.velour_twice P j x (le_refl D) h,u',map_sum]
    unfold J
    simp_rw [map_smul]
    refine sum_congr rfl fun i y=>congrArg (z i • ·)
        ((A i).velour_twice P j x (f i y) h).symm

lemma pivot_velour (R:ι→ℝ)(l:List Axis)(r:ℝ)(d:bell Υ s (h j) ≤ r):
    (((P.canvas A I h s u t f (fun i=>(R i:ℂ))).pivot P l)).velour P j x r=∑ i∈ I,(R i:ℂ) • (((A i).pivot P l)).velour P j x r:=by
 let B:=P.canvas A I h s u t f (fun i=>(R i:ℂ)); let i'(i:ι):=(A i).pivot P l; have he: (B.pivot P l).realWidth P j=bell Υ s (h j):= B.pivot_w j P l -- order
 refine P.canvas_velour j x i' I s (fun i v=> by rw [show (i' i).s=(A i).s from (A i).pivot_s P l]; exact t i v) _ _ (P.reflectorSum A I h s u t f ..) (B.pivot_s P l) (fun i v=>?_) _ (le_trans (le_of_eq he) d)
 unfold i'; change _≤(B.pivot P l).realWidth P j; rw [Apron.pivot_w, he]; exact (P.zoom_check j s (h j) (A i) (t i v)).mp (f i v j)



end Spine
namespace Spine
open Lamour.Bridge.Celeste.Morn Aria Casting
open MacroGrid SatinNucleus
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
variable (f r n:ℕ) (A:Coalition) (v:ℕ→ℕ)(u:StrictMono v)(a:ℕ→ℝ)
local notation "V" k:max=>v (n+k)
local notation "F" i:max=> P.basePlay x f i

local notation "s₀"=> parliament n A v
local notation "U"=> (F (v n)).zoom P s₀
local notation "Fh"=> fun k:ℕ=> P.basePlay x f (V k)

local notation "A'"=> fun (k:ℕ) => A.w k * (P.rewardK f r * a (n+k))
local notation "B" A:max=> P.pleading x f r n A v a u -- check order
lemma pleading_velour(p:ℝ)(l:List Axis)(h:P.roomy * P.macroStep (v n) ≤ p): ((B A).pivot P l).velour P j (ξ) p= ∑ i∈ A.voters, (((A.w i * (P.rewardK f r * a (n+i)) : ℝ) : ℂ)) • ((F (V i)).pivot P l).velour P j (ξ) p:= P.pivot_velour j (ξ) Fh A.voters (U) (s₀) _ _ _ (A') l p ((P.base_wg x j f n A v).le.trans h) -- check args!
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
