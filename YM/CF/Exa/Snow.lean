import YM.CF.Exa.Pace
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro -- tune
variable {κ:Type*}[TopologicalSpace κ](e:ℝ)(N:Side)
-- param actual continuous ζ. construct cernhat, D identity and T-D.La EO. True on gauge profile V. C(X) old core can be relieved arbitrarily.
abbrev Core (N:Side):= Tap.CrownX (N:=N)
variable (P C:Chin N→ Core N)
def bellP(A:Core N)(x:Chin N):Core N:= P x * ((A-1)*(1+C x))*P x
def harpT(A:Core N)(x:Chin N):Core N:=(1+bellP N P C A x)⁻¹-1
def finT(A B:Core N)(x:Chin N):Core N := let T:=A-1; let R:=T-B; let s:=1-P x; let H:= harpT N P C A x * P x; s*R*P x + s*T*C x * P x+s*T*(1+C x)*H + C x*H
def partV(A B:Core N)(x:Chin N):Core N:= (1-P x)*B*P x + finT N P C A B x
def oath(A B:Core N)(x:Chin N):Core N:= C x+partV N P C A B x
def boldT(A Z B:Core N)(v:Bool)(x:Chin N): Core N:= if v then pale (partV N P C A B) x*Z*(1-pale C x)+(1+pale C x)*(Z-1)*(1-pale C x) else (1-C x)*(A-1)*(1+C x)-partV N P C A B x*A*(1+C x)
def tilt(A:Core N)(x:Chin N):Core N:=A*(1+C x)
def tiltS(A:Core N)(x:Chin N):Core N:= A*(1-pale C x)
def flume (A:Core N)(x:Chin N):Core N:= Branch.pencil (bellP N P C A x) - charmE (tickA N) A
variable (A Z B: Core N)
variable {J: Bool}
lemma demand (U: Skye.Pane N)(v:IsStarProjection (P (profile U)))(p:TagG (P (profile U)) (C (profile U)))(r:‖bellP N P C A (profile U)‖<1)(y:star Z * A=1):let x:= Tulip.profile U; let T:= tilt N C A x; let H:= tiltS N C Z x
 star H * T=1∧bellP N P C A x=cern (P x) T∧ oath N P C A B x = Bop (P x) T ∧∀ i:Bool, boldT N P C A Z B i x= Proa.liftJet i (oath N P C A B x) T H-1:=by
 intro x T H; let D:=P x; let C':= C x; let Y:=harpT N P C A x; let V:= bellP N P C A x
 have hV:V=cern D T:=by
    change D*((A-1)*(1+C'))*D=D*(A*(1+C')-1)*D; have hp:D*C'=0:=p.1; simp only [sub_mul,one_mul,mul_sub,mul_one,mul_add,add_mul,hp,zero_mul]; abel
 have h: pale C x= star C':=by unfold pale x; rw [ice_pr]
 have hv: star H*T=1:=by unfold H T tilt tiltS; rw [h,star_mul,star_sub,star_one,star_star,mul_assoc,←mul_assoc (star Z),y,one_mul]; exact p.mud
 have hk: ‖cern D T‖<1:=by rw [←hV]; exact r
 let X:= clan (P:=D) (W:=T) v hk hv
 have hz : (1-D)*C'=C':=p.pen
 have hm : nous D T= Y*D+D:=by unfold nous Y harpT; rw [←hV]; change _=( _-1)*D+D; rw [sub_mul,one_mul,sub_add_cancel]
 have hw : D*(Y*D)=Y*D:=by have h:=X.tray; rw [hm,mul_add, v.isIdempotentElem.eq] at h; exact add_right_cancel h
 refine ⟨hv,hV,?_,fun i=>?_⟩
 · unfold oath partV finT Bop laneP; rw [hm]; let s:=1-D; let R:=Y*D
   have ht:s*R=0:=by unfold s; rw [sub_mul,one_mul,hw,sub_self]
   have hg:s*D=0:=by unfold s; rw [sub_mul,one_mul,v.isIdempotentElem.eq,sub_self]
   have hz:s*C'=C':=p.pen
   have hp:C'*D=C':=p.2
   change C'+(s*B*D+(s*(A-1-B)*D+s*(A-1)*C'*D+s*(A-1)*(1+C')*R+C'*R))= s*(A*(1+C'))*(R+D); rw [←mul_assoc s]; simp only [mul_sub,sub_mul,mul_one,one_mul,hg,ht,hz,mul_add,mul_one,add_mul,sub_mul, hp,ht]; abel
 let S:=partV N P C A B x; have he:pale (partV N P C A B) x=star S:=by unfold pale; rw [show ice x=x from ice_pr U]
 have hu: (1-C')*(1+C')=1:=p.mud
 unfold boldT; cases i; swap
 · change (star _ * Z*(1-pale C x)+ _)=_; rw [←show pale (partV N P C A B) x= star ((partV N P C A B) (ice x)) from rfl,he,h,show H=Z*(1-star (C x)) from (by unfold H tiltS; rw [h])]; change star S*Z*(1-star C')+(1+star C')*(Z-1)*(1-star C')=star (1+(C'+S))*(Z*(1-star C'))-1
   have hk:(1+star C')*(1-star C')=1:=by rw [←show star (1+C')=1+star C' from (by rw [star_add,star_one]),← show star (1-C')=1-star C' from (by rw [star_sub,star_one]),←star_mul,hu,star_one]
   rw [star_add,star_add,star_one,← add_assoc,add_mul (1+star C') (star S),←mul_assoc _ Z _,←mul_assoc (star S),mul_sub (1+star C') Z 1,mul_one,sub_mul (_*Z) (1+star C'),hk]; abel
 change (1-C')*(A-1)*(1+C')-S*A*(1+C')=(1-(C'+S))*(A*(1+C'))-1; rw [sub_add_eq_sub_sub, sub_mul (1-C') S, ←mul_assoc,←mul_assoc S,mul_sub,mul_one,sub_mul (_*A),hu]; abel
end YM.CF.Exa
