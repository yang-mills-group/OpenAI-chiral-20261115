import YM.CF.Exa.Wick
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro -- tune
open Thera Proa Tap Haro Skye
variable (N:Side) (Z F:Chin N→ Core N)(A V B:Core N)(x:Pane N)(u t:Bool)(p:IsStarProjection (Z (profile x)))(g:TagG (Z (profile x)) (F (profile x)))(h:star V * A=1)(v:‖bellP N Z F A (profile x)‖ < 1)
-- kernel.pose.Payment upper.KR. Inputs label Cod t; heck pure arcs.Mark.C.T tags.
abbrev don : Chin N→ Core N:=fun x=> sprig u (Z x) * boldT N Z F A V B t x* sprig t (Z x)
abbrev mire(t u:Bool)(x:Chin N): Core N:= pale (don N Z F A V B (!t) t) x * (sprig u (Z x) +don N Z F A V B u u x)
local notation "X"=> (Tulip.profile x)
local notation "Y"=> (tilt N F A X)
local notation "H"=> (tiltS N F V X)
local notation "Z₀"=> (Z X)
include p g h v
lemma sailV : let P:=Z₀; let S:= Bop P Y; (don N Z F A V B u u) X= elbow P S Y H u∧ (don N Z F A V B (!u) u) X=localTax P S Y H u:=by
 intro P S; let Q:= sprig u Z₀; let T:=sprig (!u) Z₀; unfold elbow localTax
 obtain ⟨_,_,c,r⟩:=demand N Z F A V B x p g v h
 let D:= liftJet u S Y H; have he:boldT N Z F A V B u X=D-1:=by
    change boldT N Z F A V B u _= _-1; unfold D; rw [←show oath N Z F A B X=S from c]; exact r u
 change Q * _ * Q= Q*D*Q-Q∧ T*_*Q=T*D*Q; rw [he]; have hp:Q*Q=Q:=by unfold Q; cases u; exact p.one_sub.isIdempotentElem.eq; exact p.isIdempotentElem.eq
 have hk:T*Q=0:=by rw [show T=1-Q from ?_,sub_mul,hp,one_mul,sub_self]; unfold T Q; cases u <;>simp [Proa.sprig]
 constructor; · rw [mul_sub,sub_mul,mul_one,hp]
 rw [mul_sub,sub_mul,mul_one,hk,sub_zero]
abbrev Cx:= Cod (Single N)
abbrev poseD (R:Chin N)(i j:Cx N):ℂ:= if i.1=j.1 then 0 else if i.1 then mire N Z F A V B i.1 j.1 R i.2 j.2 else star (mire N Z F A V B i.1 j.1 R i.2 j.2)
abbrev obit (R:Chin N)(i:Cx N)(j:Single N):ℂ:= cSignX i.1 (don N Z F A V B i.1 i.1 R j i.2)
lemma vaneX : torque Z₀ Y H= poseD N Z F A V B X ∧ pelic Z₀ Y H= obit N Z F A V B X:=by
 let P:=Z₀; let S:=Bop P Y; constructor
 · funext i j; let T:=fabric P
   have hu:star (dust T P S Y H i)* main T P S Y H j = mire N Z F A V B i.1 j.1 X:=by
      obtain ⟨C,K⟩:=rCalc P S Y H i; obtain ⟨D,L⟩:=rCalc P S Y H j; unfold mire Tulip.pale; rw [ice_pr x,K,D,(sailV N Z F A V B x i.1 p g h v).2,(sailV N Z F A V B x j.1 p g h v).1]
   change fuelC T P S Y H _ _= _; unfold fuelC poseD; dsimp only [T,fabric]; split; rfl; split; exact congrArg (fun t:Core N=> t i.2 j.2) hu; change (star (main T P S Y H j)* dust T P S Y H i) j.2 i.2= (star (mire N Z F A V B i.1 j.1 X)) j.2 i.2; rw [← hu,star_mul,star_star]
 funext i j; unfold obit pelic; rw [(sailV N Z F A V B x i.1 p g h v).1]
def mount (Z: Cx N→ Single N→ ℂ)(i:Cx N)(j:Single N):ℂ:= if i.2=j then 1+Z i j else Z i j
omit p g h v
lemma mountK (W:Cx N→ Single N→ℂ)(P:Core N)(i:Cx N): neck W P i=∑ j:Single N,mount N W i j • cry P (i.1,j):=by
 simp_rw [mount,show ∀ j:Single N,(if i.2=j then 1+W i j else W i j)=(if i.2=j then 1 else 0)+W i j from fun j=>by split <;>simp, add_smul, sum_add_distrib,ite_smul,one_smul,zero_smul,sum_ite_eq,mem_univ,ite_true]
 unfold Tap.neck; simp
include p g h v
lemma vent (c:Wave (Single N))(w:Sea Z₀ c)(T:Wave (Single N))(K:Sea (tickA N) T)(r: IsStarProjection (tickA N))(d: ‖cern (tickA N) A‖<1)(L:List (Cx N)) : let z:=skyGlow T A T; let M:= partV N Z F A B X; let y:= acts (exp (dg (F X))) c; let U:= Stilo.fixT Z₀ Prod.fst (mount N (obit N Z F A V B X)) (poseD N Z F A V B X) L
 TagG Z₀ M ∧ z⁻¹ • acts (quant A) (acts (rollC (cry Z₀) L) y)= Complex.exp (Matrix.trace (flume N Z F A X)) • acts (exp (dg M)) (acts ((Pastry.nursery Z₀ p).eval U) y):=by
 intro z M y U
 have ht:Commute (exp (dg (F X))) (rollC (cry Z₀) L):=by induction L with|nil=>exact Commute.one_right _|cons i L ih=>exact (moves _ _ p g i).mul_right ih -- check motives U depends L
 let P:=Z₀; let S:=Bop P Y; obtain ⟨hp,hv,hq,hr⟩:=demand N Z F A V B x p g v h
 have hR: ‖cern P Y‖<1:=by change ‖cern Z₀ Y‖< _; rw [←hv]; exact v
 let J:= Tap.clan p hR hp; have hS:S= F X+M:=hq.symm; have he:TagG P S:=⟨J.bare,J.chest⟩; let D:=F X; have hk:D= S-M:=by rw [hS]; abel -- tune D
 have hu:TagG P M:=by rw [show M=S-D from (by rw [hS]; unfold D; abel)]; exact (rentF P S D p he g).1
 have hm: exp (dg S)=exp (dg M)*exp (dg D):= (rentF P S M p he hu).2.trans (by rw [←hk]);
 refine ⟨hu,?_⟩; have hx:z=Complex.exp (Matrix.trace (charmE (tickA N) A)):= glorieux r d _ K; obtain ⟨hg,h'⟩:=vaneX N Z F A V B x p g h v
 rw [show Matrix.trace (flume N Z F A X)= Matrix.trace (charmE P Y)-Matrix.trace (charmE (tickA N) A) by rw [flume,hv,Matrix.trace_sub]; rfl]; unfold y; rw [←act_mul (rollC _ _), ←ht.eq, act_mul, tallied (F X) g.nil,←act_mul (quant A),←quant_mul]
 rw [show A*(1+_)= Y from rfl, jazz p hp hR _ w L, smul_smul,Complex.exp_sub,hx,div_eq_mul_inv,mul_comm (_⁻¹:ℂ),show exp (dg _)=_ from hm, act_mul]; refine congrArg _ (congrArg _ ?_)
 let V':=mount N (pelic P Y H); let W:=fun i:Cx N=>∑ j:Single N,V' i j • cry P (i.1,j)
 rw [funext (mountK N (pelic Z₀ Y H) Z₀), hg,h',← Stilo.meantZ Z₀ _ (mount N (obit N Z F A V B X)) _ L p c]; change acts (exp (dg D)) (acts ((Pastry.nursery P p).eval U) c)= acts _ (acts (quant (1+D)) c)
 have he': Commute (exp (dg D)) ((Pastry.nursery P p).eval U):=by
    let A':=mount N (obit N Z F A V B X); let Y'(x:Fock.Cl (Cod (Single N))):= offer (poseD N Z F A V B X) x • rollC (fun i=> ∑ j,A' i j • cry P (i.1,j)) x.term; rw [show (Pastry.nursery P p).eval U=((claps L).map Y').sum from Stilo.cedar ..]
    generalize claps L=W; induction W with|nil=> exact Commute.zero_right _|cons i W ih=> exact (((rams p (C:=D) g Prod.fst A' i.term).smul_right _).add_right ih)
 rw [←act_mul,he'.eq,act_mul,tallied D g.nil]
end YM.CF.Exa
