import YM.CF.Fir.Kappa
import YM.CF.Rush.Loop
import YM.CF.Jill.Tory
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N F:Side}(G: Ratio N F)
local notation "L" => G.count
-- actual AP mode equality (no alias choices used for real-axis same orbit)
def grain (k:Site N)(l:Site G.count)(a:Axis) :ℤ:= chert (k a) + N.val * lift l a
def aimK (k:Site N)(l:Site G.count) : Site F:= fun a=> (grain G k l a:Per F)
omit G
private lemma ch_extent {n:Side}(x:Per n): -(n.val:ℤ)< 2*chert x+1∧ 2*chert x+1≤ n.val:=by
 obtain ⟨e,h⟩:=inZone x; rw [ch_price,payH (N:=n),←neg_mul] at e; rw [ch_price,payH (N:=n)] at h; have hk:=pinch_pos n; have hx:=lt_of_mul_lt_mul_right e hk.le; have hp:=le_of_mul_le_mul_right h hk; constructor; exact_mod_cast hx; exact_mod_cast hp
private lemma ch_interval {n:Side}(x:ℤ)(h:-(n.val:ℤ)< 2*x+1)(e:2*x+1≤n.val): chert (x:Per n) = x:=by
 set y:= (x:Per n); have hx : (n.val:ℤ)∣ chert y-x:=(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (by rw [Int.cast_sub,chert_cast]; exact sub_self _)
 obtain ⟨i,v⟩:=hx; obtain ⟨t,k⟩:=ch_extent y
 rcases Int.lt_trichotomy i 0 with a|a|a; swap
 · subst i; omega
 have hg:i ≤ -1:=by omega
 have hu: (n.val:ℤ) >0:=by exact_mod_cast n.property
 nlinarith
 have hu: (n.val:ℤ) >0:=by exact_mod_cast n.property
 have hw : 1 ≤ i := by omega
 nlinarith

include G
lemma ch_aim (p:Odd G.count.val)(k:Site N)(l:Site L)(a:Axis): chert (aimK G k l a) = grain G k l a := by
 have he:=centers_odd l p a; have t:= ch_extent (k a)
 have hn: (0:ℤ)< N.val:=by exact_mod_cast N.property
 apply ch_interval <;> (unfold grain; rw [G.exact_size,Nat.cast_mul]; nlinarith [he.1,he.2,t.1,t.2])
lemma aim_eq (p:Odd G.count.val)(k:Site N)(l:Site L): mel (aimK G k l) = aliasAt (mel k) l := by
 funext a; rw [alias_value]
 change (↑(Lat.principal _):ℂ) = ((↑(Lat.principal (k a)):ℂ)+_)/_
 rw [ch_price,ch_price,ch_aim G p,grain]
 unfold pinch
 rw [G.exact_size]; push_cast
 have he : (N.val:ℂ) ≠ 0:= by exact_mod_cast N.property.ne'
 have hh : (G.count.val:ℂ)≠0:= by exact_mod_cast G.count.property.ne'
 field_simp; ring
lemma aim_injective (p:Odd G.count.val) : Injective (fun x:Site N × Site L=> aimK G x.1 x.2):=by
 rintro ⟨x,y⟩ ⟨u,v⟩ h
 have hh a: chert (x a)+ N.val * lift y a= chert (u a)+ N.val *lift v a:= (ch_aim G p x y a).symm.trans ((congrArg chert (congrFun h a)).trans (ch_aim G p u v a))
 have hx: x=u :=by
    funext a; have he:=congrArg (fun j:ℤ=>(j: Per N)) (hh a); push_cast [chert_cast] at he; simpa using he
 subst u
 have he: lift y=lift v:=funext fun i=> (mul_right_injective₀ (show (N.val:ℤ)≠0 by exact_mod_cast N.property.ne')) (add_left_cancel (hh i)) -- tune
 rw [lift_inj he]
def float (p:Odd G.count.val) : (Site N × Site G.count) ≃ Site F := Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨aim_injective G p,Fintype.card_congr (G.splitSites.symm)⟩)
@[simp] lemma float_eq (p) (k l) : float G p (k,l)= aimK G k l:= rfl
lemma summing (p:Odd G.count.val){I:Type*}[AddCommMonoid I](f:Momentum→I): ∑ i:Site F,f (mel i)=∑ i:Site N, ∑ l:Site L,f (aliasAt (mel i) l):=by rw [←Equiv.sum_comp (float G p) (fun i:Site F=> f (mel i)),Fintype.sum_prod_type]; simp_rw [float_eq, aim_eq G p]
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.summing
