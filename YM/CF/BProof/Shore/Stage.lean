import YM.CF.BProof.Shore.Warm
/-! Support of map. Pointwise hull radius Uniform. -/
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
variable {T:Tray (Floor q) ε}{F:Drum (rollup q T) (Floor q)} {A A':Score n q}{U V:Config SU.group n}
variable (B:Seal A s l b a){X:Support n}
structure Reads(X :Support n)(A B:Score n q)(U V:Config SU.group n):Prop where
 orderC : Set.EqOn A.orderC B.orderC X
 cur:Set.EqOn A.cur.mark B.cur.mark X
 fine:Set.EqOn A.fine.mark B.fine.mark X
 fire:Set.EqOn A.fire B.fire X
 ties:Agrees X U V
lemma Reads.reduce(h: Reads X A A' U V){Y:Support n}(p:Y⊆X): Reads Y A A' U V:=⟨h.orderC.mono p,h.cur.mono p,h.fine.mono p,h.fire.mono p,agrees_mono h.ties p⟩
abbrev wager(s l:ℕ):=Z*l+Wool.keep0 s+Radius s l+10
variable {x:Site n}(p: Reads (region n x (wager s l)) A A' U V)
include p B
lemma shards{i:Sκ}(g:i∈A.fine.group x) : sound s l u U i=sound s l u V i ∧ Key T A U i= Key T A' V i := by
 let j:=keep0 s; let t:= wager s l; have hm:=B.mi.mom x i g; have hk:i∈region n x t:= (reg_in ..).2 (hm.trans (by unfold t wager; omega)); have hx:region n i j ⊆ region n x t:= reg_pay hm (by unfold j t wager; omega)
 refine ⟨clear_cost u (Radius s l) i U V (agrees_mono p.ties (reg_pay hm (show Z*l+(Radius s l+10) ≤ t from (by unfold t wager; omega)))), ?_⟩; rw [Key,Key,show A.fine.hue i=A'.fine.hue i from congrArg Prod.fst (p.fine hk), p.fire hk,sees B.ch _ _ i (p.orderC.mono hx) (p.cur.mono hx) (agrees_mono p.ties hx)]
-- catch doesn't require Seal A'.
lemma burnD {i:Sκ}(g:i∈A.fine.group x): sound s l u U i = sound s l u V i:= clear_cost u _ i U V (agrees_mono p.ties (reg_pay (B.mi.mom x i g) (show Z*l+(Radius s l+10)≤_ from by unfold wager; omega)))
theorem caught_cost : caught s l u A U x=caught s l u A' V x:=by
 have he : A.fine.group x = A'.fine.group x:= ranges p.fine (by simp); unfold caught; rw [←he]; apply propext; constructor <;> intro h i g; exact burnD B p g ▸ h i g; exact (burnD B p g).symm ▸ h i g -- tune
lemma tagger_cost : tagger s l u T A U x=tagger s l u T A' V x:=by
 ext i; unfold tagger bale; rw [← mask_vals p.fine (show x∈ _ from ((reg_in ..).2 (by simp) : x∈region n x (wager s l)))]; apply sum_congr rfl; intro j _; by_cases e:j∈ A.fine.group x; · obtain ⟨p1,p2⟩:= shards (T:=T) (u:=u) B p e; rw [p1,p2]
 simp only [vani e,ite_self]
lemma open_cost : opened s l u T F A U x = opened s l u T F A' V x:=by
 let S:=region n x (keep0 s); have ht:S ⊆ region n x (wager s l):= reg_arc (by unfold wager; omega)
 rw [opened,opened,← caught_cost B p]; by_cases h : caught s l u A U x; · rw [if_pos h,if_pos h,sees B.ch _ _ x (p.orderC.mono ht) (p.cur.mono ht) (agrees_mono p.ties ht)]
 rw [if_neg h,if_neg h];  exact congrArg (dummy F) (tagger_cost B p)
end Score
end YM.CF.BProof.Mesh.Shore
