import YM.CF.DPress.Chess.Lift.Wave
import YM.CF.Scroll.Pith
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat Peaks Cube Tulip Dial SU Branch Drapes Wilson Fock Fixed NormedSpace Spire Scree Skye Tap
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N M L:Side}(G:Ratio N M)(p:Odd G.count.val)(j:ℕ)(i:Male)(Y:Nom N M)(Q:Op Slot) {o:Odd L.val}
local notation "X"=> patchQ G
variable (b:Shape)(v:UNI SpinIdx)(t:JetS b.s false true v)
local notation "FY"=>pflux b G v inert
local notation "F0"=> prepU b v inert N
local notation "F1"=> prepU (b.broad G) v inert M
include t
lemma moving_set : twist FY (cutM (lows X))=cutM (lows X):=by rw [←lighthouse]; exact hoodL (G:=G) _ _ _ -- tune θ binder
lemma coatR (x:Ket (Single N)):coat X (acts (prepU b v inert N).val x) = acts (pflux b G v inert).val (coat X x):=by
 nth_rw 1 2 [←basis_expand x]; simp only [map_sum,map_smul]; refine sum_congr rfl fun i _=>?_; apply congrArg ((x.ofLp i) • ·); apply PiLp.ext; intro j; by_cases h:j∈ lows X; swap
 · have he : acts (cutM (lows X)) (acts (pflux b G v inert).val (coat X (basisKet i))) = acts (pflux b G v inert).val (coat X (basisKet i)):=by
       rw [←moving_set G b v t,←Fock.swivel,coat_ret] -- maybe inject factors
   rw [basin X _ j h,←he,cut_apply,if_neg h]
 obtain ⟨j,-,rfl⟩:= mem_map.mp h; rw [basis_shell, ←seamK, trails,basis_act,basis_act]; rcases i with ⟨⟨a,p⟩,r⟩; rcases j with ⟨⟨e,u⟩,s⟩; change (mealU b v inert N).val (e,u,s) (a,p,r)=(fros b G v inert).val ((e,0),u,s) ((a,0),p,r); unfold fros mealU portX; dsimp only; rw [jump_apply,jump_apply]; dsimp only; by_cases u:b.mills N e=a; rw [if_pos (show Tofu b N e=a from u),if_pos (show (paceU b G (e,0))=(a,0) from Prod.ext u b.s.act_zero)]
 rw [if_neg (show Tofu b N e≠a from u),if_neg (show paceU b G (e,0)≠(a,0) from fun v=> u (congrArg Prod.fst v))]
-- exact polar reflection carries the same stencil (true transit). use $stanza.Sθ$ here not tag support assertion.
include p
lemma shineR (x:Ket (Single N)): shine G j i (stanza G b inert Y) (acts (prepU b v inert N).val x)= acts (prepU (b.broad G) v inert M).val (shine G j i Y x):=by
 unfold shine; rw [coatR G b v t,relationU,← puff G p]; refine congrArg (fun k=>coat (switchG G).toEmbedding k) ?_; exact Eq.symm (Lift.act_cost FY (pulse G j i Y) (pulse G j i (stanza G b inert Y)) (clothing G p b inert v t j i Y) _) -- tune
lemma flyH (x:Ket (Single N)): acts (prepU (b.broad G) v inert M).val (byrise G j i Y Q x) = bydrop G j i (stanza G b inert Y) Q (acts (prepU b v inert N).val x):=by unfold byrise bydrop; rw [←shineR G p j i Y b v t, peak_flip Q b v t x]
lemma flyB(x:Ket (Single N)): acts (prepU (b.broad G) v inert M).val (bydrop G j i Y Q x) = byrise G j i (stanza G b inert Y) Q (acts (prepU b v inert N).val x):=by unfold byrise bydrop; rw [←shineR G p j i Y b v t, pit_flip Q b v t x]
end YM.CF.DPress.Chess.Lift
