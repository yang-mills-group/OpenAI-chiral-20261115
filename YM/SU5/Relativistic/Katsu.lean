import YM.SU5.Relativistic.Terre
import YM.SU5.Relativistic.Abloom
import YM.CF.Emu.Fez
import YM.CF.Buffered.Probes
/-! # All molded Wick-bills via runes but interpolation at any linear filter k. `Bite` prescription.
No areas P^c' artifacts on this finite price. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip BPress.Spin.Blank Flare
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Stationary (Gaia cartWeight boundsEarth exileE)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
section
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I]
def lips (u:Bool)(P:Op I):=if u then 1-P else P
def tooth(P:Op I)(u w:Reader0 I):ℂ:= if u.1=w.1 then 0 else if u.1 then inner ℂ u.2 (acts (1-P) w.2) else inner ℂ w.2 (acts P u.2)
variable {P:Op I}{v:Wave I} (p:IsStarProjection P) {α:Type*}
include p
lemma choral (A:α→Reader0 I) (L:List α)(x:Sea P v): inner ℂ v (acts (rollC (ton ∘ A) L) v)=runes (fun i j=> tooth P (A i) (A j)) L:=by
 let F:= ton∘A; let H(i:Reader0 I):= acts (lips i.1 P) i.2; let X(i):=creed (A i).1 (H (A i)); let Y(i):= creed (A i).1 ((A i).2-H (A i)); let C (i j):= tooth P (A i) (A j)
 have hv(i): F i=Y i+X i:=by unfold F X Y ton; unfold Function.comp; rw [←creed_a, sub_add_cancel]
 have he(i): acts (X i) v=0:=by
    unfold X; rcases h:A i with ⟨b,z⟩; cases b
    · refine tarp p x.1 ?_; unfold H; change acts P (acts P z)=_; rw [←act_mul,p.isIdempotentElem.eq]; rfl
    change acts (Fock.remove (acts (1-P) z)) v=0; apply tars p x.1; rw [←act_mul, Porth p,act_zero]
 have ht(i):acts (star (Y i)) v=0:=by
    unfold Y; rcases h:A i with ⟨b,z⟩; cases b
    · change acts (remove (z-acts P z)) v=0; apply tars p x.1; rw [map_sub,←act_mul,p.isIdempotentElem.eq,sub_self]
    change acts (star (star (create (z-acts (1-P) z)))) v=0; rw [star_star]; apply tarp p x.1; rw [act_sub,act_one,sub_sub_cancel,←act_mul,p.isIdempotentElem.eq]
 have hp(i j): antiB (X i) (Y j)= C i j • 1:=by
    unfold X Y C; rcases h:A i with ⟨b,x⟩; rcases s:A j with ⟨u,y⟩; cases b <;> cases u
    · rw [show tooth P _ _=0 from (show tooth P (false,x) (false,y)=0 from rfl),zero_smul]; exact car_create ..
    · change antiB (create (acts P x)) (remove (y-acts (1-P) y))= (inner ℂ y (acts P x)) • _; rw [act_sub,act_one,sub_sub_cancel,antiB_comm]; unfold antiB; rw [car]; congr 1; nth_rw 1 [←p.isSelfAdjoint.star_eq]; rw [act_inner,←act_mul,p.isIdempotentElem.eq]
    · change antiB (remove (acts (1-P) x)) (create (y-acts P y))= (inner ℂ x (acts (1-P) y)) • _; rw [←show acts (1-P) y=y-acts P y from (by rw [act_sub,act_one]), antiB,car]; congr 1; nth_rw 1 [←p.one_sub.isSelfAdjoint.star_eq]; rw [act_inner,←act_mul,p.one_sub.isIdempotentElem.eq]
    rw [show tooth P _ _=0 from (show tooth P (true,x) (true,y)=0 from rfl),zero_smul]; exact car_rem .. -- tune shadow
 have hj(i:Cl α): inner ℂ v (invest Y v C i)=spinC C i:=by
    unfold invest spinC; cases hm:i.term
    · rw [emptyChime,inner_smul_right,inner_self_eq_norm_sq_to_K,x.2]; simp
    rw [charm,inner_smul_right,←act_inner, ht,inner_zero_left]; simp
 -- relate rollC chime
 rw [show acts (rollC (ton ∘ A) L) v=chime F v L from (?_),shadeW F Y X v C he hp hv L]; unfold runes; change inner ℂ v ((claps L).map _).sum=((claps L).map (spinC C)).sum; generalize claps L=W; induction W with|nil=>simp|cons a l ih=>simp only [List.map_cons,List.sum_cons,inner_add_right,hj]; rw [ih]
 rfl
end
-- lexicon of single mark probes site units FINITE
structure Bite where
 root:Cover
 spin:SpinIdx
 cost:Slot
 -- false=creator, true=remover
 hand:Bool
-- external transforms restrict B spin grade via Bright below
namespace Bite
variable (N:Side) (i j:Bite)
def loc : Ket (Single N):=Lifted.basisC N i.root i.spin i.cost
lemma normP:‖i.loc N‖=1:=by rw [loc,Lifted.basisC,norm_smul,show ‖Lifted.winding N i.root‖=1 from ?_]; simp [basisKet]; unfold Lifted.winding Rush.fee; simp -- tune
lemma pace {S:Finset Cover}(e:Lifted.nodeC i.root∈ S) : acts (cutM (modesIn N (S.image (wrap (More N))))) (i.loc N)=i.loc N:=by unfold loc Lifted.basisC; rw [map_smul,cut_basis, if_pos (show Lifted.index N i.root i.spin i.cost∈ modesIn N (S.image (wrap (More N))) from (modes_at ..).2 (by change node (wrap _ _) ∈ _; rw [Lifted.node_of]; exact Finset.mem_image_of_mem _ e))]
end Bite
section
variable (k:ℕ)
def colors (k:ℕ)(b:Bool) : Staff := let F:=Staff.ice k; if b then .add .one (.neg F) else .add .one F.flip
variable {N:Side}{P Q B:Op (Single N)} (p:IsStarProjection P)
local notation "W" => Saber (B:=tickA N) p k
def stilt(P:Op (Single N))(i:Bite):Reader0 (Single N):=⟨i.hand,acts ((colors k i.hand).stem (tickA N) P) (i.loc N)⟩
def vix (N:Side)(i:Bite):=creed i.hand (i.loc N)
private lemma keynote : IsStarProjection (tickA N):=by rw [←t_comp]; exact cutM_idp _
lemma artF (i:Bite): (W).glow (vix N i)=ton (stilt k P i):=by
 unfold vix stilt ton; dsimp only; unfold colors; cases h:i.hand
 · change _= create (acts (1+ (Staff.ice k).flip.stem (tickA N) P) _); rw [Staff.flip_p (tickA N) P _ p keynote,Staff.ice_at]; exact (W).glow_up _
 change _= remove (acts (1 + -((Staff.ice k).stem (tickA N) P)) _); rw [Staff.ice_at]; rw [show creed true (i.loc N)=remove (i.loc N) from rfl, Shaft.glow_down]; unfold Saber; simp [sub_eq_add_neg]
def chartP (N:Side)(x:List Bite): FC (Single N) := (x.map (vix N)).prod
lemma stamps (X:List Bite) : (W).glow (chartP N X)=rollC (ton∘ stilt k P) X:=by induction X with| nil=> simp [rollC,chartP,Shaft.glow_nil]|cons i l ih=> unfold chartP; rw [List.map_cons,List.prod_cons, Shaft.glow_mult,artF]; unfold chartP rollC at *; rw [ih,List.map_cons,List.prod_cons]; rfl
end
end YM.CF.Papyrus.Franc.Loaves
