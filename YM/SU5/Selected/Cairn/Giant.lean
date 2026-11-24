import YM.SU5.Selected.Cairn.Seeds
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
/-! # deterministic geometry, physical rulers stable. χ projection reached after pose. --/
open Afterglow Tower Tower.SlabMark
open Lifted (nodeC node_of) -- syntax split
structure Giant extends Tour where
 beams : ℕ -- choose cutoff power cost horizon
 debt : Side -- $d$ stage
 rank : ℕ -- opaque letter count (>=20)
variable (A:Giant)
namespace Giant
abbrev TourA:= A.toTour
abbrev Whistle:= A.TourA.Wp
abbrev t : ℕ:= A.TourA.elevation
abbrev n : ℕ:= A.TourA.seats
def seedB: ℕ:= 4*(A.t+A.n+A.beams+1)
def coreB:ℕ:= seedB A +(Attic.tideU A.rank+1)*A.debt.val*A.debt.val
def bW:ℕ:= coreB A+A.debt.val
-- Thermal footprint for Price+book
local notation "F" => A.bW
local notation "M₀" => A.TourA
def pin: Cover:= Ε 0 (5*(F:ℤ))
def hub := Lifted.nodeC A.pin
def Rad := plant A.seedB A.hub
def Core:=plant A.coreB A.hub
def Broad:=plant A.bW A.hub
local notation "Φ"=> A.hub
local notation "κ"=> A.pin
variable (b:Bool)
def westY (x:ℕ):Cover:= A.pin-Rail.pick x
def eastX (x:ℕ):Cover:= A.pin + Ε A.Whistle (↑(A.t+x:ℕ))
def markN (x:ℕ):= nodeC (A.eastX x)
def markY (x:ℕ):= nodeC (A.westY x)
def ascX:= Icc (A.markN 0) (A.markN A.n)
def ascY:= Icc (A.markY A.beams) (A.markY 0)
lemma nodal2(x:Cover)(i:Axis): nodeC x i=2*x i+1:=by simp [nodeC,two_mul,two_smul] -- tune open
lemma azimuth : A.hub 3=10*(F:ℤ)+1:=by rw [hub,nodal2,pin,node₃]; ring
lemma helm_v(j:Fin 3): A.hub j.castSucc=1:=by simp [hub,nodal2,pin]
local notation "Ω"=> A.TourA.speed
local notation "J" i:max=> A.markN i
local notation "Γ" i:max=> A.markY i
lemma pin_track(j:ℕ) : (J j) 3 = A.hub 3+ 2*(A.t+j:ℕ):=by rw [markN,eastX,hub,nodal2,nodal2,Pi.add_apply,node₃]; ring
lemma dot_track(j:ℕ) : (Γ j) 3= A.hub 3-2*(j:ℤ):=by rw [markY,westY,Rail.pick,hub,nodal2,nodal2,Pi.sub_apply,node₃]; ring
lemma east_v(j:ℕ)(i:Fin 3) : (J j) i.castSucc=A.hub i.castSucc+2*(A.t:ℤ):=by rw [markN,eastX,hub,nodal2,nodal2,Pi.add_apply,nodeV]; unfold Whistle Tour.Wp; ring -- maybe A.t reduc
lemma west_v(j:ℕ)(i:Fin 3): (Γ j) i.castSucc=A.hub i.castSucc:=by rw [markY,westY,hub,nodal2,nodal2,Rail.pick,Pi.sub_apply,nodeV]; simp -- sub 0 rfl?
private lemma mono_x (i j:ℕ)(p:i≤j): A.markN i ≤ A.markN j:= by intro k; cases k using Fin.lastCases with
 | last=> rw [show Fin.last 3=3 from rfl,pin_track,pin_track]; gcongr
 | cast k=>rw [east_v,east_v]
private lemma mono_y (i j:ℕ)(p:i≤j): A.markY j≤ A.markY i:= by intro k; cases k using Fin.lastCases with
 | last=>rw [show Fin.last 3=3 from rfl,dot_track,dot_track]; gcongr
 | cast k=>rw [west_v,west_v]
lemma ascN (i:ℕ)(p:i≤ A.n): A.markN i∈ A.ascX:= mem_Icc.mpr ⟨mono_x A 0 i (Nat.zero_le _),mono_x A i _ p⟩
lemma ascW (i:ℕ)(p:i≤ A.beams): A.markY i∈ A.ascY:= mem_Icc.mpr ⟨mono_y A i _ p,mono_y A 0 i (Nat.zero_le _)⟩
lemma gai (i:ℕ) (p:i≤ A.n): J i∈ A.Rad:= by
 apply plant_test.mpr; apply box_test.mpr; constructor <;> intro j <;> rw [Pi.sub_apply] <;> unfold seedB <;> (cases j using Fin.lastCases <;> first| (rw [show Fin.last 3=3 from rfl,pin_track]; omega)| (rw [east_v]; omega))
lemma gal (i:ℕ)(p:i≤ A.beams): Γ i∈ A.Rad:= by
 apply plant_test.mpr; apply box_test.mpr; constructor <;> intro j <;> rw [Pi.sub_apply] <;> unfold seedB <;> (cases j using Fin.lastCases <;> first| (rw [show Fin.last 3=3 from rfl,dot_track]; omega)| (rw [west_v]; omega))
lemma nudge : A.ascX⊆A.Rad:= Finset.Icc_subset_Icc (mem_Icc.mp (A.gai 0 (Nat.zero_le _))).1 (mem_Icc.mp (A.gai A.n le_rfl)).2
lemma nut : A.ascY⊆A.Rad:= Finset.Icc_subset_Icc (mem_Icc.mp (A.gal A.beams le_rfl)).1 (mem_Icc.mp (A.gal 0 (Nat.zero_le _))).2
def anchorX (b: Bool):= markN A (A.TourA.shiftH b) -- shift of origin.X
lemma speed_low: A.TourA.speed ≤ A.n:=by unfold n Tour.seats; omega
lemma anchor_here : A.anchorX b ∈ A.ascX:= ascN A _ ((M₀).sh_b b|>.trans A.speed_low)
def anchorY:= markY A 0
lemma anchor_dawn: A.anchorY∈ A.ascY:= ascW A _ (Nat.zero_le _)
def pulseX:ℤ:= A.hub 3+2*((A.t+A.TourA.ridgeB:ℕ):ℤ)
def Zumba:= A.ascX.filter (fun v:Cover=> pulseX A≤ v 3)
def Knot(b:Bool):= if b then A.ascX ∩ A.Zumba else A.ascX\A.Zumba
lemma knot_x : A.Knot b⊆ A.ascX:=by cases b; exact sdiff_subset; exact inter_subset_left
lemma knot_root {x:Cover}(h:x∈ A.Knot b) : x∈ A.Zumba ↔ b=true:=by
 cases b; · exact iff_of_false (mem_sdiff.mp h).2 (by decide)
 have e:x∈ A.Zumba:=(mem_inter.mp h).2
 simp [e] -- [(mem_inter.mp h).2]
lemma knot_on (v:A.TourA.UnitX)(p:v.1=true) (i:Bool): markN A (A.TourA.hilt i v).val∈ A.Knot true:=by
 let k:=A.TourA.hilt i v; have he := A.ascN _ k.isLt.le; refine mem_inter.mpr ⟨he,mem_filter.mpr ⟨he,?_⟩⟩; unfold pulseX; change _ ≤ (A.markN k.val) 3; rw [pin_track]; have v':k.val≥ A.TourA.ridgeB:= (A.TourA.vast ..).mpr p; omega
lemma knot_off (v:A.TourA.UnitX)(p:v.1=false) (i:Bool): markN A (A.TourA.hilt i v).val∈ A.Knot false:=by
 let k:=A.TourA.hilt i v; have he := A.ascN _ k.isLt.le; refine mem_sdiff.mpr ⟨he,?_⟩; intro v'; have hp:= (mem_filter.mp v').2; change pulseX A ≤ (A.markN k.val) 3 at hp; rw [pin_track] at hp; unfold pulseX at hp; have hk: v.1=true:= (A.TourA.vast ..).mp (show k.val≥ _ from by omega); exact Bool.noConfusion (p.symm.trans hk)
lemma portS : A.Rad⊆ A.Core:= from_plant _ (Nat.le_add_right ..)
lemma portT : A.Core⊆A.Broad:=from_plant _ (Nat.le_add_right ..)
lemma geo_t : A.timeGap.val ≤ A.bW:=by have hp:A.bW ≥ A.seedB:= (Nat.le_add_right A.seedB _).trans (show _≤_ from Nat.le_add_right A.coreB _); unfold seedB at hp; change _ ≥ 4*(100*A.timeGap.val+A.n+A.beams+1) at hp; omega
lemma sorted (x y:Cover)(p:x∈A.ascY)(q:y∈ A.ascX)(i:Axis): x i+2*(A.t:ℤ) ≤ y i:=by
 have hx : x i ≤ (A.markY 0) i:= (Finset.mem_Icc.mp p).2 i; have he: (A.markN 0) i ≤ y i:= (Finset.mem_Icc.mp q).1 i; cases i using Fin.lastCases <;> first| (rw [show Fin.last 3=(3:Axis) from rfl] at *; rw [dot_track] at hx; rw [pin_track] at he; omega)| (rw [west_v] at hx; rw [east_v] at he; omega) -- dependent change last defeq rw?
lemma are_d : Disjoint A.ascY A.ascX:= disjoint_left.mpr (fun x p q=>by have he:= sorted A x x p q 0; have hp:0<A.t:= (M₀).elev_pos; omega)
-- translated cap costs
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms nut
#print axioms knot_on
#print axioms knot_root
#print axioms sorted
#print axioms are_d
