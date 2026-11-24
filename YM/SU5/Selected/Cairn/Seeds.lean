import YM.SU5.Selected.Attic.Mira
import YM.SU5.Selected.Cor.RideMark
import YM.SU5.Selected.Twirl.Car
/-! # New competitor. ALL stencils come from same period lease & guard. Also spatial
 offset at every site of the *operators* not hidden sources. Sorted chronology. -/
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
-- Gauge magnitude typed. Booster integer
structure Tour where
 timeGap : Side -- separation control guaranteed ≥addgap; choose ≥.
 block : Side -- movement magnitude chosen 8 B

variable (P:Tour)
namespace Tour
abbrev Lolli (_P:Tour):= Fin 10
abbrev UnitX := Bool × P.Lolli × Fin 2
abbrev speed:= 8*P.block.val
def seats:= 80*(P.speed+1)
def elevation:= 100*P.timeGap.val
lemma elev_pos:0<P.elevation:=by unfold elevation; positivity
lemma speed_pos:0<P.speed:=by unfold speed; positivity
lemma seat_pos:0<P.seats:=by unfold seats; positivity
def Wp: FaceL:=fun _=> (P.elevation:ℤ)
def rentB (b:Bool): ℕ:= if b then 40 else 0
def ph (b:Bool):ℂ:= if b then I else 1
lemma ph_norm(b:Bool): ‖ph b‖=1:=by cases b <;> simp [ph]
lemma ph_inv(b:Bool):star (ph b)*ph b=1:=by cases b <;> simp [ph]
private def slotAge(i:P.UnitX):ℕ:=rentB i.1+2*i.2.1.val+i.2.2.val
def shiftH (b:Bool):ℕ:= if b then P.speed else 0
lemma sh_b (b:Bool): P.shiftH b≤P.speed:=by unfold shiftH; split_ifs; rfl; omega
lemma age(v:P.UnitX):rentB v.1 ≤ P.slotAge v∧ P.slotAge v ≤ rentB v.1+19:= by have ht:(v.2.1.val)<10:= v.2.1.isLt; have hz:=v.2.2.isLt; unfold slotAge; omega
def hilt(b:Bool)(i:P.UnitX): Fin P.seats:=⟨(P.speed+1)*P.slotAge i+ P.shiftH b, by have h:=P.age i; have hp:=P.sh_b b; have ht:rentB i.1 ≤ 40:= (by unfold rentB; split_ifs <;> omega); let r:=P.speed+1; have h':r*P.slotAge i ≤ r*59:=Nat.mul_le_mul_left _ (by omega); unfold r at h'; unfold seats; omega⟩
lemma fed (b:Bool)(i:P.UnitX): (P.hilt b i).val= (P.speed+1)*P.slotAge i+ P.shiftH b:=rfl
lemma tracks : Injective (Function.uncurry P.hilt) := by
 rintro ⟨b,i⟩ ⟨b',j⟩ e; replace e:= congrArg Fin.val e; simp only [Function.uncurry_apply_pair,fed] at e -- tune
 have h':0<P.speed+1:=by omega
 have hp:=P.sh_b b; have hf:=P.sh_b b'; let r:=P.speed+1; have he:P.slotAge i=P.slotAge j:=by
    by_contra t; obtain q|q:=Nat.lt_or_gt_of_ne t; · have ht:r*(P.slotAge i+1)≤ r*P.slotAge j:= Nat.mul_le_mul_left _ q; unfold r at ht; rw [Nat.mul_add,Nat.mul_one] at ht; omega
    have ht:r*(P.slotAge j+1) ≤ r*P.slotAge i:= Nat.mul_le_mul_left _ q; unfold r at ht; rw [Nat.mul_add,Nat.mul_one] at ht; omega
 have hz:b=b':=by rw [he] at e; have hh:= Nat.add_left_cancel e; unfold shiftH at hh; have h:= P.speed_pos; cases b<;> cases b'<;>simp at hh<;> first|rfl|omega
 apply Prod.ext hz; have hj:i.1=j.1:=by have v:=age P i; have w:=age P j; unfold rentB at v w; cases q:i.1 <;> cases t:j.1 <;> first|rfl|simp [q,t] at v w; omega
 unfold slotAge at he; rw [hj] at he; change i=j; exact Prod.ext hj (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))) -- oz vals bind
-- ask Stake A via mask for orth
open Nacre
local notation "w" => P.Wp
noncomputable def consent (b:Bool): WRect (Fin P.seats) P.UnitX:= ph b • mask (P.hilt b)
noncomputable def blueprint:= consent P true+consent P false
set_option synthInstance.maxSize 20000
lemma driver (b:Bool) : Injective (P.hilt b):= fun i j h=> (Prod.mk.inj (P.tracks (a₁:=(b,i)) h)).2 -- h usage
lemma off (b c:Bool)(h:b≠ c) : (P.consent b)ᴴ* consent P c=0:=by
 unfold consent; rw [Matrix.conjTranspose_smul, Matrix.smul_mul,Matrix.mul_smul]; rw [show (mask (P.hilt b))ᴴ*mask (P.hilt c)=(0:Op (UnitX P)) from ?_,smul_zero,smul_zero]; ext i j; rw [mask_star_mem,mask,Matrix.of_apply,if_neg]; rfl; exact fun v=> h ((Prod.mk.inj (P.tracks (a₁:=(b,i)) (a₂:=(c,j)) v)).1)
lemma target (b:Bool) : (P.consent b)ᴴ* blueprint P=1:=by
 have ht: (P.consent b)ᴴ*P.consent b=1:=by unfold consent; rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,mask_self _ (P.driver b),smul_smul,ph_inv,one_smul]
 unfold blueprint; rw [Matrix.mul_add]; cases b<;> rw [ht]; rw [P.off _ _ (by decide),zero_add]; rw [P.off _ _ (by decide),add_zero]
lemma consent_cost(b:Bool): ‖P.consent b‖≤1:=by unfold consent; rw [norm_smul,ph_norm,one_mul]; exact mask_toll _ (P.driver b)
-- charge time TRUE deadline. support stencils remain in cover time rank slots and lower stream. rooted D open band.
def ridgeB := (P.speed+1)*40
lemma vast (b:Bool)(s:P.Lolli)(i: Fin 2)(a:Bool): (P.hilt b (a,s,i)).val≥ P.ridgeB ↔ a=true:=by
 let p:P.UnitX:= (a,s,i); rw [fed]; have he:= P.age p; have hv:= P.sh_b b
 unfold p at *; cases a
 · have h: (P.speed+1)*P.slotAge (false,s,i) ≤ (P.speed+1)*19:= Nat.mul_le_mul_left _ (show _ from he.2); unfold ridgeB; constructor; intro y; omega; intro y; cases y
 constructor; · intro; rfl
 intro; apply le_trans (b:=(P.speed+1)*P.slotAge (true,s,i)) _ (Nat.le_add_right ..); unfold ridgeB; gcongr; exact he.1
end Tour
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Tour
#print axioms vast
#print axioms consent_cost
#print axioms target
