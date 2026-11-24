import YM.CF.DPress.Chess.Lift.Weight
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat Peaks Cube Tulip Dial SU Branch Drapes Wilson Fock Fixed NormedSpace Spire Scree Skye Tap
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N M L:Side}(G:Ratio N M)(p:Odd G.count.val)(j:ℕ)(i:Male)(Y:Nom N M)(Q:Op Slot){o:Odd L.val}
-- work generically to avoid import-dup landscape.
local notation "kT"=> basisKet
local notation "X"=>patchQ G
section
variable {a b:Type*}[LinearOrder a][LinearOrder b][Fintype a][Fintype b]
lemma coat_swap (e:a≃b)(x:Ket a): coat e.symm.toEmbedding (coat e.toEmbedding x)=x:=by nth_rw 1 2 [←basis_expand x]; simp only [map_sum,map_smul,basis_shell,Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
lemma pail_up(F:a↪b)(S:Finset b)(p:Deck F S)(x:Ket a)(v:Wave b) : acts (create x) (pailL F S v)=pailL F S (acts (create (coat F x)) v):=by
 apply ext_inner_left ℂ; intro y; rw [pails _ S p,←act_inner,←act_inner, pails _ S p,show star (create x)=remove x from rfl,hoist_r F S p]
lemma pail_down(F:a↪b)(S:Finset b)(p:Deck F S)(x:Ket a)(v:Wave b) : acts (remove x) (pailL F S v)=pailL F S (acts (remove (coat F x)) v):=by
 apply ext_inner_left ℂ; intro y; rw [pails _ S p,←act_inner,←act_inner,pails _ S p,show ∀ (x:Ket a),star (remove x)=create x from fun x=>star_star _,hoist_c F S p]; simp [remove] 
end
lemma relocate (A: Op (Single M))(x: Ket (Single M)): coat (switchG G).symm.toEmbedding (acts A x)=acts (foot G A) (coat (switchG G).symm.toEmbedding x):=by
 let g:=(switchG G).symm.toEmbedding; have he:foot G A= addS g ∅ A:= (flexL (switchG G).symm A).symm -- tune
 rw [he,origin _ _ (shelfG ..)]
lemma relationU (A:Op (Single M))(x: Ket (Iota G)): acts A (coat (switchG G).toEmbedding x)=coat (switchG G).toEmbedding (acts (foot G A) x):=by
 let y:=coat (switchG G).toEmbedding x; have hp: x=coat (switchG G).symm.toEmbedding y:=(coat_swap ..).symm; nth_rw 2 [hp]; rw [←relocate]; exact Eq.symm (coat_swap (switchG G).symm (acts A y))
def shine (x:Ket (Single N)):Ket (Single M):= coat (switchG G).toEmbedding (acts (pulse G j i Y) (coat (patchQ G) x))
noncomputable def byrise (x:Ket (Single N)):Ket (Single M):= shine G j i Y (acts (peak N Q) x)
noncomputable def bydrop(x:Ket (Single N)):Ket (Single M):= shine G j i Y (acts (pit N Q) x)
local notation "Yq"=>pulse G j i Y
local notation "tie"=> ticketT (Vault.Thread j) true i G (unionP Y)
local notation "Rt"=>reefS G true
local notation "w"=> lobe G true
abbrev pathH (x:Phys M):=scaleZ Q (Dial.fire (Vault.Thread j) G i (unionP Y) (cartsL (switchG G).symm x))
include p
lemma rise_g {x:Ket (Single N)}(t:Upper (tickA N) x) : Upper (tickA M) (byrise G j i Y Q x):=by
 let y:= acts (peak N Q) x; let Z:= coat (patchQ G) y; have hp: Upper (lobe G true) Z:=by unfold Upper Z; rw [lobe_coat, show acts (tickA N) y=y from t.acted (peekU ..)]
 unfold Upper byrise shine; rw [relationU,← Dial.lobe_t, show (acts (lobe G true)) (acts (pulse G j i Y) Z)=acts (pulse G j i Y) Z from hp.acted (pulse_comm G _ _ _ p)] -- tune Z def rw
lemma drop_g {x:Ket (Single N)}(t:Lower (tickA N) x) : Lower (tickA M) (bydrop G j i Y Q x):=by
 let y:= acts (pit N Q) x; let Z:= coat (patchQ G) y; have hp: Lower (lobe G true) Z:=by unfold Lower Z; rw [lobe_coat, show acts (tickA N) y=0 from t.acted (peekL ..),map_zero]
 unfold Lower bydrop shine; rw [relationU,← Dial.lobe_t]; change coat (switchG G).toEmbedding (acts _ (acts Yq Z))=0; rw [show acts w (acts Yq Z)=0 from hp.acted (pulse_comm G _ _ _ p),map_zero]
lemma bring_up(h:Along j L o (Vault.Thread j) true i G (unionP Y))(x:Ket (Single N))(u:Upper (tickA N) x)(P:Phys M): acts (create x) (pathH G j i Y Q P)=pathH G j i Y Q (acts (create (byrise G j i Y Q x)) P):=by
 let y:= acts (peak N Q) x; let F:= coat (patchQ G) y; have hp:Upper w F:=by unfold Upper F; rw [lobe_coat,show acts (tickA N) y=y from u.acted (peekU ..)]
 unfold pathH Dial.fire; rw [peak_W]; simp only [map_smul]; apply congrArg; apply congrArg _; change acts (create y) ((pailL ..) (effectK _ _))=(pailL ..) _; rw [pail_up (patchQ G) Rt (reefS_deck ..), effectK,quant_up tie F _ (Eq.symm (unticket G p h F hp)), show cartsL _ (acts (create _) P) = acts (create (acts Yq F)) (cartsL (switchG G).symm P) from ?_ ] -- tune
 · rfl
 unfold cartsL; rw [hoist_c _ _ (shelfG ..)]; unfold byrise shine; rw [coat_swap]; rfl
lemma bring_down(h:star Q= Q) (x:Ket (Single N))(u:Lower (tickA N) x)(P:Phys M): acts (remove x) (pathH G j i Y Q P)=pathH G j i Y Q (acts (remove (bydrop G j i Y Q x)) P):=by
 let y:= acts (pit N Q) x; let F:= coat (patchQ G) y; have hp:Lower w F:=by unfold Lower F; rw [lobe_coat,show acts (tickA N) y=0 from u.acted (peekL ..),map_zero]
 unfold pathH Dial.fire; rw [pit_W Q h]; simp only [map_smul]; apply congrArg; apply congrArg _; change acts (remove y) ((pailL ..) (effectK _ _))=(pailL ..) _; rw [pail_down (patchQ G) Rt (reefS_deck ..), effectK,quant_down tie F _ (Eq.symm (launch_t G p F hp)), show cartsL _ (acts (remove _) P) = acts (remove (acts Yq F)) (cartsL (switchG G).symm P) from ?_ ]
 · rfl
 unfold cartsL; rw [hoist_r _ _ (shelfG ..)]; unfold bydrop shine; rw [coat_swap]; rfl
end YM.CF.DPress.Chess.Lift
