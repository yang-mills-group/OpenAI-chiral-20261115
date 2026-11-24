import YM.CF.BProof.Bias.Payday
import YM.CF.BProof.Align.Ins
/-! Slabs with single layers. Π as in B-Ppass calculated from Board. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I]{A P Q X:Op I}{N:Side}{c:ℝ}
lemma commLand(h:Fit P Q)(t:Commute X P)(u:Commute X Q)(e:Commute X (star Q)): Commute X (land P Q):= by
 have ht: Commute X (entered P Q):=(e.mul_right u).add_right ((Commute.one_right _).sub_right t); exact u.mul_right (((show Commute (entered P Q)⁻¹ X from shiftOn h.active h.active ht.symm).symm).mul_right e)
lemma commEntry(b:Board A P Q c)(h:Commute X A)(u:Commute X P)(t:Commute X Q): Commute X (entryP A P Q):=by
 let L:=space P Q; let E:=house A P Q 0; have he:Commute X (wedgeP A P):=by apply commLand b.child u (h.mul_right u) ?_; rw [star_mul,b.a.isSelfAdjoint,b.p.isSelfAdjoint]; exact u.mul_right h
 have hh:Commute X (wedgeQ A P):=h.sub_right he; have ht:Commute X L:= (Commute.one_right _).sub_right (u.add_right t)
 refine (commLand b.fit0 h ?_ ?_).sub_right u; rw [b.slot0]; exact (u.mul_right he).add_right (ht.mul_right hh); rw [b.slot0,star_add,star_mul,star_mul,b.wall.isSelfAdjoint,b.p.isSelfAdjoint,b.leaves.isSelfAdjoint,b.drawn.isSelfAdjoint]; exact (he.mul_right u).add_right (hh.mul_right ht)
lemma entryLift(b:Board A P Q c): entryP A P Q= space P Q * wedgeQ A P * send A (house A P Q 0) :=by
 conv_lhs=>rw [← b.holdsPiH]; rw [entryP,mul_sub,swapOrth b.p b.wall b.pw,sub_zero,floorH,land, ←mul_assoc, b.slotL]
-- coordinates restricted to B-Ppass. R are Mark times.
def rowsX (R:Finset (Per N)):= univ.filter fun x:Site N=> x 0∈R
variable (R:Finset (Per N))
lemma row_at {x:Site N}{R:Finset (Per N)}: x∈rowsX R ↔ x 0 ∈ R:=by simp [rowsX]
abbrev PP:= bandCut (rowsX Rᶜ) true
abbrev QQ:= bandCut (rowsX Rᶜ) false
abbrev Seat(R:Finset (Per N)):= timeR ht R
lemma timeN : Seat Rᶜ=1-Seat R:=by unfold Seat timeR; rw [←dim_cut, show univ.filter (fun i:Single N=> ht i∈ Rᶜ)= (univ.filter (fun i:Single N=> ht i∈R))ᶜ from by ext i; simp]
lemma rangeA (u:Bool): bandCut (rowsX R) u=timeR ht R*bandCut (univ:Support N) u := by
 apply op_columns; intro i; rw [bandCut,bandCut,timeR,act_mul,cut_basis,cut_basis]; by_cases e:i.1.2∈ spHalf u
 · rw [if_pos ((mem_band ..).mpr ⟨mem_univ _,e⟩),cut_basis]; simp [row_at,e,ht,fsite]
 rw [if_neg (fun t=>e ((mem_band ..).mp t).2),if_neg (fun t=> e ((mem_band ..).mp t).2),map_zero]
lemma PP_eq: PP R= (1-timeR ht R)*tickA N:=by rw [PP,rangeA,ticka,show timeR ht Rᶜ= _ from timeN R] -- tune
lemma QQ_eq: QQ R=(1-timeR ht R)*(1-tickA N):=by rw [QQ,rangeA,dusk,show timeR ht Rᶜ=_ from timeN R]
lemma seat_eq: Seat R=space (PP R) (QQ R):=by rw [space,PP_eq,QQ_eq,←mul_add]; unfold Seat; noncomm_ring -- tune unify mult
lemma commuteT : Commute (Seat R) (tickA N):=by rw [←ticka]; exact time_cut ..
def Polar(j:ℕ)(M:Male)(R: Finset (Per N)):= entryP (redP j M N) (PP R) (QQ R)
variable {j:ℕ}(M:Male)(h:1≤j)(w:Per N)
def Free (b:ℝ)(j:ℕ)(M:Male)(R:Finset (Per N)):= Board (redP j M N) (PP R) (QQ R) b
variable (b:Free c j M R)
include b h
lemma haloEntry : Commute (haloW w) (Polar j M R):=by
 let W:=haloW w; let χ:=(wing_t (i:=1) w (by decide)).comm R; have ht: Commute W (tickA N):=by rw [sky_t]; exact mode_comm _ (fun _:Site N=> sky)
 -- χ orientation?
 apply commEntry (Q:=QQ R) b; rw [redP_eq M h]; exact mode_comm _ _; rw [PP_eq]; exact ((Commute.one_right _).sub_right χ.symm).mul_right ht; rw [QQ_eq]; exact ((Commute.one_right _).sub_right χ.symm).mul_right ((Commute.one_right _).sub_right ht)
lemma lift_gr : (1-tickA N)*Polar j M R=Seat R*Zenith j M N * tickA N * Polar j M R:=by
 let A:=redP j M N; let L:= Seat R; let T:=tickA N; let Z:= Zenith j M N; let U:= PP R; let V:= QQ R; let P:=Polar j M R; let W:=wedgeQ A U
 have hz: Z*W=(1-T)*W:=by unfold W; nth_rw 1 [← (show Board A U V c from b).spanQ]; rw [←mul_assoc,zen_frame M h,mul_assoc,(show Board A U V c from b).spanQ]
 have hg:L*T=T-U:=by unfold U; rw [PP_eq,sub_mul,one_mul,sub_sub_cancel]
 have hu:Commute L T:= commuteT R; have hz':Commute L (1-T):= (Commute.one_right _).sub_right hu; have ht:T*(L*W)=T*W:=by rw [←mul_assoc,hu.symm.eq,hg,sub_mul, show U*W=0 from (show Board A U V c from b).rimLeft,sub_zero]
 have hP:(1-T)*(L*W)=L*Z*T*(L*W):=by rw [mul_assoc (L*Z),ht,←mul_assoc (L*Z),mul_assoc L Z T, zen_y,mul_assoc L,hz, ←mul_assoc, ← mul_assoc, hz'.eq]
 let Y:=send A (house A U V 0); rw [show Polar j M R=L*W*Y from (by unfold L; rw [seat_eq]; exact entryLift (show Board A U V c from b))]; change _=L*Z*T*_; rw [←mul_assoc _ (L*W) Y, ←mul_assoc _ (L*W) Y, show 1-tickA N=1-T from rfl, hP] -- tune
lemma grantLift {X:Op (Single N)}(u:tickA N * X=X)(v:Seat R*X=X): Polar j M R*(X+Seat R*Zenith j M N*X)=X+Seat R*Zenith j M N*X:=by
 let L:=Seat R; let Z:=Zenith j M N; let T:=tickA N; let Y:=(T+Z)*X; let A:=redP j M N; let U:=PP R; let V:=QQ R; let B:Board A U V c:=b; let W:=wedgeQ A U
 have he:X+L*Z*X=L*Y:=by unfold Y; rw [add_mul,u,mul_add,v,mul_assoc L Z]
 have hg:A*Y=Y:=by unfold Y; rw [←mul_assoc,zen_find M h]
 have ht:U*Y=0:=by unfold Y U; rw [PP_eq,add_mul,u,mul_add,mul_assoc (1-timeR ht R), show (1-timeR Bias.ht R)* (T*X)= (1-L)*X from congrArg _ u]; rw [sub_mul (1:Op (Single N)),one_mul,v,sub_self, mul_assoc (1-timeR Bias.ht R),←mul_assoc T Z,zen_n,zero_mul,mul_zero,zero_add]
 have hh:W*Y=Y:=by unfold W; rw [wedgeQ,sub_mul,hg, B.wedgePformed, mul_assoc (_*U*_) (U*A), mul_assoc U A, hg,ht]; simp -- tune
 change _*(X+L*Z*X)=X+L*Z*X; rw [he]; unfold L; rw [seat_eq]; nth_rw 1 [←hh]; rw [←mul_assoc, ←mul_assoc, mul_assoc (Polar j M R) _ W, show Polar j M R * (_* W) = _ from B.fillPiH,mul_assoc,hh]
end YM.CF.BProof.Bias
