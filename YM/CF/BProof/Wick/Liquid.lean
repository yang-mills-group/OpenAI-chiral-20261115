import YM.CF.BProof.Wick.Taste

/-! plogRe cost separately purchased on real/determinant data. Loss priced with support
for all roots assessed in marker & vac. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory Stint
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]
def purse (T A P Q:Op I) := (1/2:ℂ) • (pencil (star T * T) + pencil (hutch A P-1) + pencil (hutch (1-wedgeQ A P) Q-1))
theorem poseQ (T A P Q:Op I) : Pose T A P Q=(purse T A P Q).trace.re:=by unfold Pose purse feeB; rw [Matrix.trace_smul, Matrix.trace_add,Matrix.trace_add]; simp; ring
-- root assessment f_z of B-loss. For price keep on Pi; equality assembled.
def periodQ (A C:Op I):= (1/4:ℂ) • pencil (-widthP A C)
theorem losses (A C:Op I): tickCost A C=(periodQ A C).trace.re:=by unfold tickCost periodQ; rw [ Matrix.trace_smul]; simp; ring
lemma widthN' (A P Q:Op I){T:Op I}{c r:ℝ}(b: Board A P Q c)(u:Align.Twig T P)(h:Shelf (floorH A P Q 0) T r): ‖widthP (entryP A P Q) T‖≤r^2:=by
 let V:=entryP A P Q; have ht: offCut (floorH A P Q 0) T= offCut V T:= b.PiHe ▸ Shoot b.p u (swapOrth b.p b.PiHp b.offPiH) b.PiHp -- tune
 apply (h.widthN).trans' ; unfold widthP; rw [ht]
variable {L c r:ℝ}(h:0≤L)(p:0<c)(g:0≤r)(t:r<1)
abbrev worksH(a b:Pay):= ((b.mul a).mul b).add (Pay.simple.add b)
omit h p t g in
lemma earnH {D G Y:Type}[Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}{a p:Pay}{u:Tag b}{P A:Raw D I}(h:Earn a u u A)(t:Earn p u u P): Earn (worksH a p) u u (fun i=> hutch (A i) (P i)):= (((t.times h).times t).plus ((Earn.one u).minus t))
include h p
theorem cash (a b q g:Pay):∃ u s:Pay,∀ {I Y D G:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{v:Stage Y I D G}{A P Q T:Raw D I}{k:Tag v}, Capacity v L → Earn a k k A → Earn b k k P→ Earn q k k Q→Earn g k k T→(∀ i, ‖T i‖≤ 1/2) → (∀ i, Board (A i) (P i) (Q i) c) → Earn u k k (fun i=> purse (T i) (A i) (P i) (Q i)) ∧ Earn s k k (fun i=> entryP (A i) (P i) (Q i)):=by
 let l:=Pay.simple; let f:=l.wage 0; obtain ⟨m,n,o,y,w,W⟩:=Stint.sphere L c h p a b q f; let R:=max (1/2:ℝ) (1-c); have ht:0<R:=lt_max_of_lt_left (by norm_num); have he:R<1:=max_lt (by norm_num) (by linarith); obtain ⟨u₁,t₁⟩:=pencilCost ht he h (g.mul g); obtain ⟨u₂,t₂⟩:=pencilCost ht he h ((worksH a b).add l); obtain ⟨u₃,t₃⟩:= pencilCost ht he h ((worksH (l.add (a.add n)) q).add l); refine ⟨((u₁.add u₂).add u₃).wage ‖(1/2:ℂ)‖, y.add b,?_⟩; intro I Y D G _ _ _ _ _ _ b A P Q T s V gA gP gQ gT Z H -- tune binders
 have hp: Earn f s s (fun _=> (0:ℝ) • 1):= (Earn.one s).wage (by simp)
 obtain ⟨hA,hB,k,w,X⟩:= W.applies (A:=A) (P:=P) (τ:=fun _=>0) V gP gQ gA hp (by simp) H; refine ⟨?_, w.minus gP⟩
 have e1(i:D): ‖star (T i)*T i‖≤R:=by rw [CStarRing.norm_star_mul_self]; apply le_trans ?_ (le_max_left ..); have hx:=Z i; nlinarith [norm_nonneg (T i)]
 have δ:=Earn.one s; let Y:= t₂ V ((earnH gA gP).minus δ) (fun i=> ((hutch_bound (H i).p (H i).a (H i).holes (H i).bare p).1).trans (le_max_right ..)); let S:=t₃ V ((earnH (δ.minus (gA.minus hB)) gQ).minus δ) (fun i=> ((hutch_bound (H i).q ((H i).leaves.one_sub) (H i).loftHole (H i).bare p).1).trans (le_max_right ..)); exact (((t₁ V (gT.adj.times gT) e1).plus Y).plus S).scalar le_rfl
include t g
omit p in
lemma lossCost (a b:Pay): ∃ v:Pay,∀ {I Y D G:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{v':Stage Y I D G}{A C:Raw D I}{k:Tag v'}, Capacity v' L→Earn a k k A→ Earn b k k.reverseV C→(∀ i, ‖widthP (A i) (C i)‖≤ r^2)→ Earn v k k (fun i=> periodQ (A i) (C i)):=by
 let A:Pay:= (a.mul b).mul (Pay.simple.add a); obtain ⟨ζ,hz,H⟩:= exists_between (pow_lt_one₀ (n:=2) g t (by omega)); obtain ⟨u,Y⟩:= pencilCost ((sq_nonneg r).trans_lt hz) H h (A.mul A); refine ⟨u.wage ‖(1/4:ℂ)‖,?_⟩; intro I Y' D G _ _ _ _ _ _ v B C k p' a' b' e; let f:=(a'.times b').times ((Earn.one k.reverseV).minus a'.ccUp); exact (Y p' (f.times f.adj).neg (fun i=> (norm_neg (widthP (B i) (C i))).trans_le ((e i).trans hz.le))).scalar le_rfl
end YM.CF.BProof.Wick
