import YM.CF.DPress.Chess.Stencil.Vein
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Symbol
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat Peaks Cube Tulip Dial SU Branch Drapes Wilson
open scoped Topology BigOperators NNReal ENNReal Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m N:Side}(G:Ratio n m){A B:Nom n m→Op (Iota G)}{r j:ℕ}
namespace Stroke
variable {G}
lemma douse_k (ho:Odd G.count.val)(A:Track G.count)(S:Finset Cover)(R:ℕ)(t:∀ i,i∉S→A i=0) (hp:∀ i∈S,16*G.count.val+8*G.count.val*Laurent.size i ≤ R)(o:Lattice.Order): Stroke G (fun X=> douse G true false A o (unionP X)) R:=by
 unfold douse; refine sum univ _ fun r _=> sum univ _ (fun s _=> ?_); let T:= S.image names.symm; let F(i:ℕ):= drag G true false r s (names i) (A (names i) r s) o ∘ unionP
 have he(i:ℕ):i∈ T↔ names i∈ S:=by simp [T,Equiv.symm_apply_eq];
 have hx(X: Nom n m)(i:ℕ)(h:i∉ T):F i X=0:=by unfold F drag; rw [comp_apply,t (names i) (mt (he i).mpr h)]; simp only [Matrix.zero_apply,mul_zero,zero_smul]; exact sum_eq_zero fun _ _=>Matrix.ext fun i j=>by simp [panel]
 have ht(X): (∑' i,F i X)=∑ i∈ T,F i X:=tsum_eq_sum (s:=T) (hx X)
 change Stroke G (fun X=> (∑' i,F i X)) R; simp_rw [ht]; exact sum T F (fun i x=> stork ho r s _ _ _ _ ((run_len ..).trans (hp _ ((he _).1 x))))
lemma clothB (j:ℕ)(L:Side)(ho:Odd L.val): ∃ r:ℕ,∀{N P:Side}(G:Ratio N P),G.count=L→ ∀ M: Male, Stroke G (fun X=> cloth j M G (unionP X)) r:=by
 obtain ⟨S,p⟩:= brix_h j L ho; refine ⟨S.sup (fun i=>16*L.val+8*L.val*Laurent.size i),?_⟩; intro N P G h M; subst L; let A(X):= mosaic G true false (tub (brix j G.count)) (unionP X); have ht:S.Nonempty∨¬ S.Nonempty:= em _; have he: Stroke G A (S.sup (fun i=>16*G.count.val+8*G.count.val*Laurent.size i)) := mul (sum univ _ (fun o _=> douse_k ho _ S _ p (fun i v=> le_sup (f:=fun i=>16*G.count.val+8*G.count.val*Laurent.size i) v) o)) _
 exact add (chirality he true) (chirality he false)
-- touch = relay at embedded query at projected channel. No path-label conditioning.
lemma coarse (i:Single n) : touch G false (patchQ G i).1=(ratio G).embed (Cube.node i.1.1):=rfl -- tune
lemma fine (i:Iota G) : touch G true i.1=node ((switchG G i).1.1):=rfl
end Stroke
end YM.CF.DPress.Chess.Symbol
