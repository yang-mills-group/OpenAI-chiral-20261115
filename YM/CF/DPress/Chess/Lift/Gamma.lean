import YM.CF.DPress.Chess.Stencil.Price
import YM.CF.Fixed.OneParticle
import YM.CF.Vault.Horse
/-! Bounded-range actual CAR operator lift from a single step. No offset included inside lift
 (bookmark is scalar, separate). In particular need both kinds of insertions and `SpaceM`.

 Lift uses the same `cloth` stencil on the two chiralities before the `cartsL`
 reindexing, even though the ket uses `ticketT` (with an inverse block). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat Peaks Cube Tulip Dial SU Branch Drapes Wilson Fock Fixed NormedSpace Spire 
open scoped Topology BigOperators NNReal ENNReal Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m L:Side}(G:Ratio n m){N M:Type*}[Fintype N][Fintype M][LinearOrder N][LinearOrder M]{j J:ℕ} {o:Odd L.val}
lemma quant_up (A:Op N)(x y:Ket N)(h:x=acts A y)(P:Wave N): acts (create x) (acts (quant A) P)=acts (quant A) (acts (create y) P):=by rw [←act_mul,←act_mul,h,quant_create]
lemma quant_down (A:Op N)(x y:Ket N)(h:y=acts (star A) x)(P:Wave N): acts (remove x) (acts (quant A) P)=acts (quant A) (acts (remove y) P):=by rw [←act_mul,←act_mul,quant_ann,←h]
abbrev Upper (Y:Op N)(x: Ket N):Prop:= acts Y x=x
abbrev Lower (Y:Op N)(x: Ket N):Prop:= acts Y x=0
lemma Upper.acted {A B:Op N}{x:Ket N}(h:Upper A x)(t:Commute A B):Upper A (acts B x):=by unfold Upper at *; rw [←act_mul,t.eq,act_mul,h]
lemma Lower.acted {A B:Op N}{x:Ket N}(h:Lower A x)(t:Commute A B):Lower A (acts B x):=by unfold Lower at *; rw [←act_mul,t.eq,act_mul,h,map_zero]
lemma lobe_coat (x:Ket (Single n)) : acts (lobe G true) (coat (patchQ G) x)=coat (patchQ G) (acts (tickA n) x):=by rw [whale_plus]; exact origin _ _ (reefS_deck ..) x _
-- `lobe true` nonzero anywhere (not taking n restrictions). DP.
lemma lobe_sure : lobe G true ≠ 0:= by
 let a:Single n:= ((0,0),Classical.arbitrary _); let X:=(patchQ G); have ht: acts (tickA n) (basisKet a)=basisKet a:=by
    rw [Fixed.tickA_upper,cut_basis, if_pos (show a∈Fixed.upperIndices n by simp [Fixed.upperIndices,a,plusHalf])]; -- he
 intro e; have hp:= lobe_coat G (basisKet a); rw [e,act_zero,ht,basis_shell] at hp; have hz:= congrArg (fun u:Ket (Iota G)=> u.ofLp (X a)) hp; simp [X] at hz -- name
variable (j':ℕ)(Y:Nom n m)(i: Male) (p: Odd G.count.val)
noncomputable def pulse (j:ℕ)(i:Male)(Y:Nom n m) := Peaks.cloth j i G (unionP Y)
private abbrev P := pulse G j' i Y
lemma pulse_comm (j:ℕ)(i:Male)(Y:Nom n m)(p:Odd G.count.val): Commute (lobe G true) (pulse G j i Y):= (canUse j G.count p).orients i G _
variable {j' Y i}
local notation "Φ"=> pulse G j' i Y
local notation "W"=> ticketT (Vault.Thread j') true i G (unionP Y)
local notation "K"=> lobe G true
local notation "L'"=> G.count
lemma pulse_unit {o:Odd L.val}(h: Along j' L o (Vault.Thread j') true i G (unionP Y)): IsUnit Φ:=by
 by_contra! p; have ht: (1-K)*K=0:= (by rw [sub_mul,one_mul,(lobe_sq ..).1.eq,sub_self]); have he:= Matrix.nonsing_inv_apply_not_isUnit _ (mt ((Matrix.isUnit_iff_isUnit_det Φ).2) p); have hx: W*K=0:=by change (Φ⁻¹*_+_*(1-K))*K=0; rw [he,zero_mul,zero_add,mul_assoc,ht,mul_zero]
 let S:= ticketT (Vault.Thread j') false i G (unionP Y); have hv:star S * W=1:=h.bridge; apply lobe_sure G; rw [←one_mul (lobe G true),←hv,mul_assoc,hx,mul_zero] -- he `.1.eq`
include p
lemma unticket {o:Odd L.val}(h: Along j' L o (Vault.Thread j') true i G (unionP Y))(x:Ket (Iota G))(t: Upper K x) : acts W (acts Φ x)=x:=by
 have hp:=Upper.acted t (pulse_comm G j' i Y p); change acts (Φ⁻¹*K+_*(1-K)) _=x; unfold Upper at *; rw [act_add,act_mul,act_mul,act_sub,act_one,hp,sub_self,map_zero,add_zero,←act_mul,(Fock.live (pulse_unit G h)).2,act_one]
lemma launch_t (x:Ket (Iota G))(t:Lower K x) :acts (star W) x=acts Φ x:=by
 -- x minus. star*commutes with K since both inv & star.
 have hx:= pulse_comm G j' i Y p; -- need Commute A star inv.NON Unit? use relation lower starinv. need h too to prove?
 change acts (star (Φ⁻¹*K+ star _*(1-K))) _=_; rw [show Vault.Thread j' i G (icec (unionP Y))=Φ from ?_,star_add,star_mul,star_mul,star_star,star_sub,star_one,(lobe_sq ..).2, act_add]; swap; · rw [revI]; rfl
 have he:Lower K (acts Φ x):= t.acted hx; have hw: Commute K (star Φ⁻¹):=by
    have hp:Commute K Φ⁻¹:=by
       by_cases h:IsUnit Φ; swap; · rw [Matrix.nonsing_inv_apply_not_isUnit _ (mt ((Matrix.isUnit_iff_isUnit_det _).2) h)]; exact Commute.zero_right _
       refine IsUnit.mul_right_inj h |>.1 ?_ -- K*Φ^- on left.
       rw [←mul_assoc,hx.eq.symm,mul_assoc,(Fock.live h).1,mul_one,←mul_assoc,(Fock.live h).1,one_mul]

    apply (lobe_sq ..).2 ▸ hp.star_star  -- tune

 rw [act_mul,act_mul,(Lower.acted t hw),act_sub,act_one,he,sub_zero,zero_add] -- Lower lemma applied notation; maybe rewrite
end YM.CF.DPress.Chess.Lift
