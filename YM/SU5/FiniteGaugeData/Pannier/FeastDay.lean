import YM.SU5.FiniteGaugeData.Pannier.PaleFace
/-!
# Native insertion set from cover stencil, revenue width/copy inequality. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG
open Py.Rate.Pannier
open Work.E08
open Lifted (nodeC node_of)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
-- count `q` centers per axis. radius formula curvature condition. U0 on cover arbitrary.
variable {n:Side}{r q B d w:ℕ}{o:Cover}
def Sen (o:Cover)(r:ℕ): Finset Cover:= (box r).image (·+nodeC o)
def Islet (n:Side)(o:Cover)(r:ℕ):= BlockP r (wrap (More n) (nodeC o))
lemma sen_islet (o:Cover)(r:ℕ) : Islet n o r=(Sen o r).image (wrap (More n)) := by
 ext x; rw [Islet, blocks_test,Sen,image_image,mem_image]; let p:=wrap (More n) (nodeC o);
 constructor; · intro h; refine ⟨Lattice.lift (x-p),lift_mem_box h,?_⟩; rw [comp_apply,map_add,wrap_lift]; change x-p+p=x; abel
 rintro ⟨i,p,rfl⟩; rw [comp_apply,map_add]; exact separation_box_add _ p
private abbrev Disc(q:ℕ) := Axis→ Fin q
private def dexterity (q:ℕ):Fin (q^4) ≃ Disc q := Fintype.equivOfCardEq (by simp [Disc,Axis])
-- Higher boost by one means even if gap much closer.
def booty (o:Cover)(d q:ℕ)(i:Fin (q^4)): Cover:= fun a=> ((d+1:ℕ):ℤ)*((dexterity q i a).val:ℤ)+o a
def payout (d q w:ℕ):ℕ:=2*(d+1)*q+(w+d+1)
local notation "|E|"=> payout d q w -- quotient?
private lemma offload (a:Axis)(i:Fin (q^4)) : (nodeC (booty o d q i)-nodeC o) a=2*(((d+1:ℕ):ℤ)*(dexterity q i a).val):=by change (nodeC _ a)-(nodeC _ a)=_; unfold nodeC booty; simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply]; simp only [nsmul_eq_mul,Nat.cast_ofNat]; ring
private lemma length_d (a:Axis)(i:Fin (q^4)):
    0≤(nodeC (booty o d q i)-nodeC o) a ∧ (nodeC (booty o d q i)-nodeC o) a≤ (2*((d+1:ℕ):ℤ)*q):=by
 rw [offload,←mul_assoc]; constructor; · positivity
 exact mul_le_mul_of_nonneg_left (by exact_mod_cast (dexterity q i a).isLt.le) (by positivity)
private lemma patch_lon (j:Fin (q^4)): nodeC (booty o d q j)-nodeC o ∈ box (2*(d+1)*q):=by
 apply box_test.mpr; constructor; · intro i; have h:0≤(nodeC _ -nodeC o) i:=(length_d (d:=d) i j).1; omega
 intro i; simpa only [Nat.cast_mul,Nat.cast_ofNat] using (length_d (o:=o) (d:=d) i j).2
private lemma solid_width (a b: Fin (q^4))(p:4*(2*(d+1)*q) < (More n).val) :
 let x:= nodeC (booty o d q a); let y:=nodeC (booty o d q b)
 Lattice.lift (wrap (More n) x-wrap (More n) y)=x-y:=by
 intro x y; apply lift_eq_iff.mpr; refine ⟨(map_sub ..).symm,fun i=>?_⟩; have hx:=box_test.mp (patch_lon (o:=o) (d:=d) a); have he:=box_test.mp (patch_lon (o:=o) (d:=d) b); let T:=2*(d+1)*q
 have hv:-(T:ℤ)≤ x i-nodeC o i:=hx.1 i
 have hg:x i-nodeC o i≤T:=hx.2 i
 have hq:-(T:ℤ)≤ y i-nodeC o i:=he.1 i
 have hr:y i-nodeC o i≤ T:=he.2 i
 change 4*T < _ at p; change _ < 2*(x i-y i) ∧ 2*(x i-y i) ≤ _; omega

def midWay (n:Side)(o:Cover)(d q:ℕ): Fin (q^4)→ Seat n:= fun a=> wrap (More n) (nodeC (booty o d q a))
private lemma striper {i j:Fin (q^4)} (v:i ≠ j)(t:4*(2*(d+1)*q)<(More n).val):
    d+1 ≤ separation (midWay n o d q i) (midWay n o d q j):=by
 obtain ⟨a,g⟩:∃ a,dexterity q i a ≠dexterity q j a:= not_forall.mp (fun h=>v ((dexterity q).injective (funext h)))
 let x:=nodeC (booty o d q i); let y:=nodeC (booty o d q j)
 have hf: (x a-y a).natAbs≤ separation (midWay n o d q i) (midWay n o d q j):=by
    have hl:= solid_width (o:=o) i j t; have he:= component_le (midWay n o d q i-midWay n o d q j) a; unfold midWay at he; rw [hl] at he; exact he
 have heo:x a-y a=(2*((d+1:ℕ):ℤ))*((dexterity q i a).val-(↑(dexterity q j a).val:ℤ)):=by
    have hp:x a-nodeC o a=2*(((d+1:ℕ):ℤ)*(dexterity q i a).val):=offload a i
    have hg:y a-nodeC o a=2*(((d+1:ℕ):ℤ)*(dexterity q j a).val):=offload a j
    rw [mul_sub]; linarith
 rw [heo,Int.natAbs_mul,Int.natAbs_mul,Int.natAbs_natCast] at hf; apply hf.trans'; apply (Nat.le_mul_of_pos_right (Int.natAbs 2*(d+1)) ?_).trans' (Nat.le_mul_of_pos_left (d+1) (by decide))
 apply Int.natAbs_pos.mpr; rw [sub_ne_zero]; intro l; exact g (Fin.ext (Int.ofNat_inj.mp l)) -- tune Prop type G
private lemma mid_cheap (o:Cover)(d w:ℕ)(q:ℕ)(i:Fin (q^4)): separation (wrap (More n) (nodeC o)) (midWay n o d q i) ≤ 2*(d+1)*q:=by
 unfold midWay; have t:=separation_box_add (wrap (More n) (nodeC o)) (patch_lon (o:=o) (d:=d) i); rw [map_sub,sub_add_cancel] at t; exact t
abbrev birthSeat (n:Side)(o:Cover)(d q:ℕ)(i:Fin (q^4)):=node (wrap n (booty o d q i))
@[simp] lemma seatQ (n:Side)(o:Cover)(d q:ℕ): birthSeat n o d q=midWay n o d q:=funext fun i=> node_of ..
lemma feast (t:4*(2*(d+1)*q)<(More n).val)(o:Cover)(w:ℕ) :
 let f:= birthSeat n o d q; let S:= Finset.univ.image f; Injective f∧Sparse d S∧ Lattice.halo (w+d+1) S ⊆ Islet n o (payout d q w):=by
 rw [seatQ]; intro f S;
 constructor; · intro i j g; by_contra h; have ht:d+1 ≤ separation (f i) (f j):= striper h t; rw [g,separation_self] at ht; omega
 constructor
 · intro i hi k hk p; obtain ⟨i,u,rfl⟩:= mem_image.mp hi; obtain ⟨k,h,rfl⟩:=mem_image.mp hk; have he:i≠k:= fun v=>p (v ▸ rfl); exact (striper (o:=o) he t).trans' (Nat.le_succ _)
 intro i p; apply blocks_test.mpr; obtain ⟨k,h,u⟩:= halo_spec.mp p; obtain ⟨k,v,rfl⟩:= mem_image.mp h; exact (separation_triangle ..).trans (add_le_add (mid_cheap o d w q k) u)
-- *budget planning*: threshold on q independent of horizon n. density authority from purchased constants in perspective.
def innerRatio (d:ℕ):ℝ:= (((4*(6*(d+1)+1):ℕ):ℝ)^4)⁻¹
theorem innerRatio_pos (d:ℕ):0 < innerRatio d:=by unfold innerRatio; positivity
theorem width_cost {d w b:ℕ} (g:w+d+1 ≤ q)(h:b ≤ q) :
    ((4*((2*payout d q w)+b):ℕ)^4:ℝ)*innerRatio d ≤ ((q^4:ℕ):ℝ):=by -- parsing casts! `((a:ℕ)^4:ℝ)` may infer
 let F:=payout d q w; let D:=6*(d+1)+1; let E:=4*D; have hp:2*F+b ≤ D*q:=by unfold D F payout; nlinarith only [g,h,show 0 ≤ d*q by omega]
 have he:(4*(2*payout d q w+b):ℕ)^4 ≤ q^4*(E^4):=by rw [←mul_pow]; apply Nat.pow_le_pow_left; apply (Nat.mul_le_mul_left _ hp).trans; exact le_of_eq (by unfold E; ring)
 unfold innerRatio; rw [← div_eq_mul_inv]; exact (div_le_iff₀ (by positivity)).2 (by exact_mod_cast he)
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.feast
#print axioms YM.CF.Pannier.Chancel.width_cost
