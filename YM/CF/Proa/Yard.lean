import YM.CF.Thera.Ticket
/-! Wick transfer in the sector with F-tilt kept exponential. Not restricted to projected creators.
Hence accommodates local Clifford operations even where gauge completion was needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter NormedSpace Finset Fock Scroll Matrix Spire Branch Thera
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {n m ι:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- (s i) used projector draw not sea
structure Letter(ι n:Type*) where
 seek:ι→Bool
 sites:ι→n
 matrix:ι→ Op n

def sprig(b:Bool)(Q:Op n):=if b then Q else 1-Q
def liftJet(v:Bool)(S W V:Op n):= if v then star (1+S)*V else (1-S)*W
def dialL(T:Letter ι n)(i:ι):FC n := creed (T.seek i) (acts (T.matrix i) (basisKet (T.sites i)))
def aqua(T:Letter ι n)(S W V:Op n)(i:ι):= liftJet (T.seek i) S W V * T.matrix i
def main(T:Letter ι n)(B S W V:Op n)(i:ι):=sprig (T.seek i) B * aqua T S W V i
def dust(T:Letter ι n)(B S W V:Op n)(i:ι):=sprig (!(T.seek i)) B * aqua T S W V i
lemma stack(T:Letter ι n)(B S W V:Op n)(i:ι):main T B S W V i+dust T B S W V i= aqua T S W V i:=by
 unfold main dust; generalize aqua T S W V i=U; rw [← add_mul]; cases g:T.seek i<;> simp [sprig]
def ivy(T:Letter ι n)(S W V:Op n)(i:ι):FC n:=creed (T.seek i) (acts (aqua T S W V i) (basisKet (T.sites i)))
lemma super (T:Letter ι n)(S W V:Op n)(h:S*S=0)(v:star W*V=1)(i:ι): quant ((1-S)*W)*dialL T i= ivy T S W V i*quant ((1-S)*W):=by
 unfold dialL ivy; generalize hk:T.seek i=c; unfold creed; cases c
 · rw [if_neg (show false≠true by decide),if_neg (show false≠true by decide),quant_create,←act_mul, aqua,hk]; rfl
 rw [if_pos rfl,if_pos rfl,quant_ann,←act_mul,aqua,hk]; congr 4
 change T.matrix i= star ((1-S)*W)*(star (1+S)*V*T.matrix i); rw [star_mul,←mul_assoc, ←mul_assoc (star W*_),mul_assoc (star W) (star _) (star _),←star_mul,show (1+S)*(1-S)=1 by rw [mul_sub,add_mul,add_mul,h]; simp,star_one,mul_one,v,one_mul]

def cane(T:Letter ι n)(B S W V:Op n)(i:ι):FC n:=creed (T.seek i) (acts (main T B S W V i) (basisKet (T.sites i)))
def brim(T:Letter ι n)(B S W V:Op n)(i:ι):FC n:=creed (T.seek i) (acts (dust T B S W V i) (basisKet (T.sites i)))
def fuelC(T:Letter ι n)(B S W V:Op n)(i j:ι):ℂ:= if T.seek i=T.seek j then 0 else if T.seek i then costC (dust T B S W V i) (main T B S W V j) (T.sites i) (T.sites j) else costC (main T B S W V j) (dust T B S W V i) (T.sites j) (T.sites i)
lemma ivy_v(T:Letter ι n)(B S W V:Op n)(i:ι): ivy T S W V i=cane T B S W V i + brim T B S W V i:=by unfold ivy cane brim; rw [← creed_a,←act_add,stack]
lemma ash_T(T:Letter ι n)(B S W V:Op n)(p:Wave n)(t:IsStarProjection B)(h:Sea B p)(i:ι): acts (brim T B S W V i) p=0:=by
 unfold brim; cases g:T.seek i
 · refine tarp t h.1 ?_; rw [←act_mul, dust, g,Bool.not_false]; change acts (B*(B*_)) _= _; rw [←mul_assoc,t.isIdempotentElem.eq]; rfl
 apply tars t h.1; rw [←act_mul, dust,g]; change acts (B*((1-B)*_)) _ =_; rw [← mul_assoc,Porth t,zero_mul,act_zero]
lemma ash_F(T:Letter ι n)(B S W V:Op n)(i j:ι):antiB (brim T B S W V i) (cane T B S W V j)=fuelC T B S W V i j • 1:=by
 unfold brim cane fuelC creed; cases u:T.seek i<;>cases v:T.seek j<;> simp only [ite_true,Bool.true_eq_false,Bool.false_eq_true,ite_false,zero_smul]
 · exact car_create ..
 · rw [antiB_comm]; unfold antiB; rw [car,tout]
 · unfold antiB; rw [car,tout]
 exact car_rem ..

def loT(T:Letter ι n)(B S W V:Op n)(i:ι)(f:m↪n):FC m:=creed (T.seek i) (trailK f (acts (main T B S W V i) (basisKet (T.sites i))))
def enC(T:Letter ι n)(B S W V:Op n)(i:ι)(x:n):ℂ:= if T.seek i then (star (main T B S W V i)) (T.sites i) x else main T B S W V i x (T.sites i)
variable {R:Op m}{P B W V K C:Op n}(F:m↪n)(D:Finset n)(H:Deck F D)(p:IsStarProjection R)(g:B=addS F D R)
include p H g
lemma pole(T:Letter ι n)(i:ι)(S W V:Op n)(x:Wave n): pailL F D (acts (cane T B S W V i) x)=acts (loT T B S W V i F) (pailL F D x):=by
 unfold cane loT; let A:=aqua T S W V i; subst B; let B:=addS F D R; have hb:=projectorD F D p H
 cases u:T.seek i
 · apply planter _ _ H R; rw [←act_mul]; unfold main; rw [u]; change acts (B*((1-B)*_)) _=_; rw [←mul_assoc,Porth hb,zero_mul,act_zero]
 apply rattan _ _ H R; rw [←act_mul]; unfold main; rw [u]; change acts (B*(B*A)) _ = acts (B*A) _; rw [←mul_assoc,hb.isIdempotentElem.eq]
lemma fag(T:Letter ι n)(i:ι)(S W V:Op n): loT T B S W V i F= ∑ j:m, enC T B S W V i (F j) • cry R (T.seek i,j):=by
 subst B; let B:=addS F D R; let A:=aqua T S W V i; let v:=acts (main T B S W V i) (basisKet (T.sites i)); let x:=trailK F v; have hb:IsStarProjection B:=projectorD F D p H
 change creed _ x= _; cases g:T.seek i
 · have hp: acts B v=0:=by unfold v main; rw [←act_mul, g]; change acts (B*((1-B)*A)) _=_; rw [←mul_assoc,Porth hb,zero_mul,act_zero]
   have hx: acts (1-R) x=x:=by rw [act_sub,act_one]; unfold x; rw [←pane F D H,hp,map_zero,sub_zero]
   change create x=_; nth_rw 1 [←hx,←basis_expand x]; rw [map_sum,map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,map_smul, show enC T B S W V i (F j)= x.ofLp j by unfold x; rw [seamK]; unfold v enC; rw [basis_act,g]; rfl]; change _= _ • seekF _ _; rw [seekF,prong_p]
 have hp: acts B v=v:=by unfold v main; rw [←act_mul,g]; change acts (B*(B*A)) _= acts (B*A) _; rw [←mul_assoc,hb.isIdempotentElem.eq]
 have he:acts R x=x:=by unfold x; rw [←pane F D H,hp]
 change remove x=_; nth_rw 1 [←he,←basis_expand x]; unfold remove; rw [map_sum,map_sum, star_sum]; apply sum_congr rfl; intro j _; rw [map_smul,map_smul,star_smul, show enC T B S W V i (F j)=star (x.ofLp j) by unfold x; rw [seamK]; unfold enC v; generalize hk:main T B _ _ _ i=A; rw [g,basis_act]; rfl]; change _=_ • hideF _ _; rw [hideF,prong_t]

lemma forward(T:Letter ι n)(v:Clad P B W V K)(o:TagG P C)(u:‖bentT K B W C‖<1)(X: Wave n)(e:Sea P X)(q:Wave m)(l:Sea R q)(J:List ι): let E:=traitP B K W C; let L:=fun i:ι=> ∑ j:m,enC T B E W V i (F j) • cry R (T.seek i,j)
 pailL F D (acts (quant W) (acts (rollC (dialL T) J) (acts (exp (dg C)) X)))=(Complex.exp (invoice (bentT K B W C))*skyGlow (hoist F D q) W X) • acts (exp (dg (summit F E))) (((claps J).map (invest L q (fuelC T B E W V))).sum):=by
 intro E L
 let R':=quant ((1-E)*W); let Y:=quant W; let Λ:=exp (dg E)
 let m:=hoist F D q; let s:Sea B m:=g.symm ▸ stageUp F D H p l
 have ht:= rideK v o (close_c u); let c:= (Complex.exp (invoice (bentT K B W C))*skyGlow m W X)
 have hx: Λ * R'=Y:=by unfold Λ R'; rw [show dg E=dg E from rfl,tallied _ ht.reef,← quant_mul,←mul_assoc,ht.flick,one_mul] -- tune
 have hy: acts R' (acts (exp (dg C)) X)= c • m:=by
   unfold R'; rw [quant_mul,tallied _ o.nil,act_mul,←act_mul (quant W),←quant_mul,broomstick ht X m e s,map_smul,show skyGlow m (W*(1+C)) X= _ from whittle v o X m e s u]; rw [show exp (dg _)=quant (1+E) from tallied E ht.reef,←act_mul,←quant_mul,mul_eq_one_comm.mp ht.flick,quant_one, act_one]
 have hr (l:List ι): R' * rollC (dialL T) l= rollC (ivy T E W V) l*R':=by
   induction l with
   | nil=>simp [rollC]
   | cons i j ih=> change R'*(_*rollC _ j)=_*rollC _ j*R'; rw [←mul_assoc,super T E W V ht.reef v.rain,mul_assoc, ih,←mul_assoc] -- star
 change pailL _ _ (acts Y _)= c • _; rw [←hx,act_mul,←act_mul R',hr,act_mul,hy,map_smul,map_smul,map_smul]
 congr 1; let d:= fuelC T B E W V; let Y:=invest (cane T B E W V) m d
 change pailL _ _ (acts Λ (chime (ivy T E W V) m J))= _
 rw [shadeW (ivy T E W V) _ (brim T B E W V) m d (ash_T T B E W V m v.helm s) (ash_F T B E W V) (ivy_v T B E W V), show pailL F D (acts Λ _)= _ from tides F D H p (g ▸ ht.bare) (g ▸ ht.chest) _]; -- tune
 congr 1; rw [map_list_sum,List.map_map]; congr 2; ext1 j
 let Y':= cane T B E W V; have hg (u:List ι): pailL F D (chime Y' m u)=chime L q u:=by
   induction u with
   | nil=> rw [emptyChime,emptyChime]; exact pourL _ _ H q
   | cons i u ih=> rw [charm,charm, show pailL F D (acts (Y' i) _)=_ from pole F D H p g T i _ _ _ (chime Y' m u), show L i=_ from (fag F D H p g T i E W V).symm,ih]
 change pailL F D (offer _ _ • chime Y' m j.term)= offer _ _ • _
 rw [map_smul,hg]
end YM.CF.Proa
