import YM.CF.BProof.Shore.Shroud
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Function Metric Finset Lattice Wilson Nest Stave Gallery
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l q:ℕ}{u ε d a b δ θ:ℝ}
local notation "Sκ"=>Site n
local notation "Z"=> Nerve.Halo
namespace Score
open Wool
variable {T:Tray (Floor q) ε}{F:Drum (rollup q T) (Floor q)}
variable {A:Score n q}(U:Config SU.group n)(W:Writ q T s l u a b δ d θ F)(B:Seal A s l b a)
local notation "hΨ"=>team s l u T A U
local notation "Ω"=>A.cur.native A.orderC U
local notation "Τ"=> tagger s l u T A U
local notation "ζF"=>caught s l u A U
local notation "dmat"=>dummy F
-- explicit parameters
variable (s l u T F A)
def opened(x:Sκ): plate (Pad (Floor q)):= if caught s l u A U x then lower (Ω x) else dummy F (Τ x) -- notation inside explicit braces weird
variable {s l u T F A}
local notation "Ρ"=> opened s l u T F A U
include W B
lemma worthy(x:Sκ): Dummy d (Ρ x):=by
 unfold opened; have p:=W.cost_a.trans_le W.cost_b; split; · exact ⟨_,king_lower (Wool.frame A.orderC U B.ch x),p.le.trans' (dist_self _).le⟩
 rename_i h; exact is_dummy p.le (W.book.kit _ (challenge U W B (x:=x) (y:=x) (by simp)) (contest U B (by simp) (fun t=>h t.1))) (Τ x) (pool_tap U B x x).1
lemma worth_h(x:Sκ)(i:Axis)(g:ζF x)(p: ζF (x+step i)): dist (roll (Ρ x) (U (x,i))) (Ρ (x+step i)) ≤ d:= by rw [opened,opened,if_pos p,if_pos g,roll_lower, lower_dist]; exact (Wool.phase B.ch A.orderC U W.hC B.small W.hδ.le W.err _ _ (commissioned U B g)).trans W.cost_c -- order
lemma worth0{x y:Sκ}(p:separation x y≤1)(h:¬ζF y): Like (3*d) (Ρ x) (Ρ y):=by
 have e:= stand U W B p (fun t=> h t.2); unfold opened; rw [if_neg h]; split
 · refine ((ray0 U W B p (by assumption) (contest U B p (fun t=> h t.2))).trans e).weaken ?_; linarith only [W.cost_b]
 exact e.weaken (by linarith only [W.cost_a,W.cost_b])
lemma worth (x:Sκ)(i:Axis): Like (3*d) (Ρ x) (Ρ (x+step i)):=by
 by_cases p:ζF x; · by_cases h:ζF (x+step i); exact ⟨U (x,i), (worth_h U W B x i p h).trans (by linarith only [W.cost_a,W.cost_b])⟩; exact worth0 U W B (nearV x (posDir i)) h
 exact (worth0 U W B ((separation_comm ..).trans_le (nearV x (posDir i))) p).symm
end Score
end YM.CF.BProof.Mesh.Shore
