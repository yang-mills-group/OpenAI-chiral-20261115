import YM.CF.Vp929.Roof.Loom
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Filter Mesh Lattice Rooms Atlas Guide MeasureTheory Palace Mos Mesa Cube Lat Skye Read Cane Spire Scroll Laurent Paper SU ProbabilityTheory Borel
open scoped Topology Classical NNReal ENNReal Matrix.Norms.Frobenius
namespace Dream

private def e(l:ℕ):ℝ:=1/(l+1 :ℕ)
private lemma ep(l:ℕ):0<e l:=by unfold e; positivity
structure StoryL where
 C:Side
 K:ℕ→ℝ
 flags : ℝ
 chord : ℝ
structure Legal (s:StoryL)(d:ℝ):Prop where
 p :0<s.flags
 e : s.flags≤ d
 well : Sweater s.C (Delta.roofLength granite) s.K s.flags s.chord
 ears : ∀ (n:Side)(A:Pane n),RG.flags s.chord A=∅ → Guard A d
private lemma sentinelL(d:ℝ)(p:0<d):∃ s:StoryL, Legal s d:=by
 obtain ⟨c,C,G⟩:= taxon p; obtain ⟨x,L,r,t,H,W⟩:= boltH (Delta.roofLength granite) c C d p; exact ⟨⟨x,L,r,c⟩,⟨t,H,W,G⟩⟩
/-- Uniform tape, one set of deterministic finite-range rules on the (lifted) data. -/
def plot(l:ℕ):StoryL:=(sentinelL _ (ep l)).choose
protected def Nimbus(l:ℕ)(n:Side)(P: Orbit n→ Pane n):Prop:= Haven (plot l).C (plot l).K n P

lemma arch {b d:ℝ}(p:0<b)(q:0<d):∃ N:ℕ,∃ (l r:ℕ) (u:ℝ), 0<u∧u≤b∧∀ n:Side, N≤ n.val→∃ P:Orbit n→Pane n, Roof n u d r P∧Dream.Nimbus l n P:=by
 obtain ⟨l,h⟩:= exists_nat_gt (1/min b d); let T:= plot l; let C:=T.C; let K:=T.K; let u:=T.flags; have f:Legal T (e l):=(sentinelL _ (ep l)).choose_spec; have e₀:e l ≤ min b d:=by unfold e; push_cast; refine (div_le_iff₀ (by positivity)).mpr ?_; have R:= (div_lt_iff₀ (lt_min p q)).mp h; linarith [lt_min p q]
 let r:= 2*(Fringe C)+reachT C+1; have z:Borel.Gather.Budget r (Fringe C) (reachT C):= le_rfl; let N:= 2*(spanR*Bolt C); refine ⟨N+1,l,r,u,f.p,f.e.trans (e₀.trans (min_le_left ..)),fun n v=>?_⟩
 have E:N<(More n).val:= Nat.lt_of_lt_of_le v (Nat.le_mul_of_pos_right _ two_pos); refine ⟨_,Dream.covering C K n E r f.well z d (fun A h=> (f.ears n A h).shrink (e₀.trans (min_le_right ..))),Dream.heaven C K n E r f.well z⟩
end Dream
end YM.CF.VolumeCape
#print axioms YM.CF.VolumeCape.Dream.arch
