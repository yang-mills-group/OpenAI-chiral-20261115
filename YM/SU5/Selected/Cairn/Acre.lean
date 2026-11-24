import YM.SU5.Selected.Cairn.Giant
import YM.SU5.FiniteGaugeData.Tower.RoomShape
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
/-! # Broad area. Itself rep exponent cost; pointwise radius uniform bound polynomial.
-/
open Afterglow Tower Tower.SlabMark Lifted
namespace Giant
variable (A:Giant)
local notation "W" => A.bW
local notation "w" => A.coreB
local notation "k" => A.seedB
local notation "Φ" => A.hub
lemma radial : 1≤k:=by unfold seedB; omega
lemma widthH:k≤w:=Nat.le_add_right ..
lemma widthC : w ≤ W:=Nat.le_add_right ..
lemma height : 1≤ W:= A.radial.trans (A.widthH.trans A.widthC)
-- Explicit broad cost: relative time ~11W ≥ buffer; hub spatial1. ν-law h₃ safe. support around operator writ.
lemma broadBeat(x:Cover)(p:x∈ A.Broad): 9* (W:ℤ)≤ x 3 ∧ x 3≤ (12:ℤ)* W ∧ ∀ j:Fin 3, |x j.castSucc|≤(2:ℤ)* W:= by
 obtain ⟨i,v⟩:= box_test.mp (plant_test.mp p); simp_rw [Pi.sub_apply] at i v
 have hp:=A.height; have ht:= i (3:Axis); have hx:= v (3:Axis); rw [A.azimuth] at ht hx; refine ⟨by omega,by omega,fun j=>?_⟩; specialize i j.castSucc; specialize v j.castSucc; rw [A.helm_v] at i v; exact abs_le.mpr ⟨by omega,by omega⟩
variable {N:Side}
lemma Glow:(park N A.Broad).Nonempty:= Nonempty.image (f:=wrap (More N)) (show A.Broad.Nonempty from ⟨_,plant_id ..⟩) -- Finset name
lemma risk: Lattice.halo ((tideU A.rank+1)*A.debt.val*A.debt.val) (park N A.Rad) ⊆ park N A.Core:=by rw [Rad,Core,park_plant,park_plant]; exact park_halo _ _ le_rfl _
lemma riskC:Lattice.halo A.debt.val (park N A.Core)⊆park N A.Broad:=by rw [Core,Broad,park_plant,park_plant]; exact park_halo _ _ le_rfl _
lemma nearBudget: Distant A.debt.val ((park N A.Broad)ᶜ) (park N A.Core):=by rw [Core,Broad,park_plant,park_plant]; exact Lantern.Bulb.farther _ _ le_rfl _
def tokenS := 16*A.bW
-- require > 200*W. addGap H foot.
lemma broad_space {K:Calibration}(t:addgap K≤ A.timeGap.val)(s:A.tokenS < N.val): park N A.Broad⊆ band N 3 0 K.ℓ:=
 Tower.SlabMark.enters_arc K 3 (x:=0) (fun x h=> by
    obtain ⟨v,z,e⟩:= broadBeat A x h; have ht:=A.geo_t; unfold addgap stepgap at t; unfold tokenS at s; constructor <;> omega) rfl
lemma broad_region (K:Calibration)(t:addgap K ≤ A.timeGap.val): Tower.region 3 0 K.ℓ A.Broad:= by intro x u; have h:=(A.broadBeat x u).1; have hx:=A.geo_t; unfold addgap stepgap at t; omega
-- all axis uses these integers. width cost in MoreN
abbrev maxAge:= (100:ℕ)*A.bW
private lemma broads (x:Cover)(p:x∈ A.Broad)(i:Axis): -(12* (W:ℤ))≤ x i ∧ x i≤ 12*(W:ℤ):=by
 obtain ⟨t,wG,vG⟩:= A.broadBeat x p -- notation w conflict!
 cases i using Fin.lastCases
 next => rw [show Fin.last 3=(3:Axis) from rfl]; omega
 next i=>specialize vG i; obtain ⟨v₀,v₁⟩:=abs_le.mp vG; omega
lemma broad_cows (i:Axis): cows i (hyphen 3 0 (park N A.Broad)∪ park N A.Broad) A.maxAge:=by
 refine ⟨-(12*(W:ℤ)),fun x t=>?_⟩; unfold maxAge
 rcases mem_union.mp t with h|h
 · obtain ⟨y,tg,rfl⟩:= mem_image.mp h; obtain ⟨x,p,rfl⟩:=mem_image.mp tg; rw [Shape.anno]; refine ⟨(plane 3 0).motion x i, ?_,?_,rfl⟩; all_goals rw [fling_move]; have hx:= broads A x p i; split_ifs <;> omega
 obtain ⟨x,p,rfl⟩:=mem_image.mp h; exact ⟨x i,(broads A x p i).1,by have ht:=(A.broads x p i).2; omega,rfl⟩
-- Budget upper argument $explicit in d$ after P body. maxW+addgapK≤ slope*..
def wrens(P:Tour)(b d:ℕ):ℕ:= 4*(P.elevation+P.seats+b+1)
def americans (P:Tour)(b y:ℕ):ℕ:= 101*(wrens P b y+tideU y+2)
lemma ground_time(K:Calibration)(hm:addgap K≤ A.timeGap.val): (( (A.maxAge+addgap K:ℕ):ℝ)) ≤( (americans A.TourA A.beams A.rank):ℝ)* (A.debt.val:ℝ)^2:=by
 let d:=A.debt; have hp:addgap K ≤ W:=hm.trans A.geo_t; let f:= Nat.le_add_left 0 1; have ht:(W)= k+(tideU A.rank+1)*d.val*d.val+d.val:= by unfold bW coreB; rfl
 change (((_:ℕ)):ℝ) ≤ _; unfold americans; have hx :wrens (A.TourA) A.beams A.rank = k:=rfl; rw [hx]; exact_mod_cast (show A.maxAge+addgap K ≤ (101 * (A.seedB+tideU A.rank+2))*A.debt.val^2 from (le_trans (b:=101*W) (by unfold maxAge; omega) (by rw [ht]; have h:=d.property; change _ ≤ _*(d.val)^2; refine le_trans (Nat.mul_le_mul_left 101 (add_le_add (Nat.add_le_add_right (Nat.le_mul_of_pos_right A.seedB (pow_pos h 2)) _) (Nat.le_mul_of_pos_left d.val h))) (le_of_eq (by norm_cast; change 101*(A.seedB*d.val^2+(tideU A.rank+1)*d.val*d.val+d.val*d.val) = 101*(A.seedB + tideU A.rank + 2)*d.val^2; ring)))))
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms broad_cows
#print axioms broad_region
#print axioms broad_space
#print axioms riskC
#print axioms ground_time
