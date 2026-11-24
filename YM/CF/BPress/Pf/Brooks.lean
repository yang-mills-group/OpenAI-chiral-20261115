import YM.CF.BPress.Pf.Broker
import YM.CF.BPress.Pf.Log
/-! Helix path supports. Strong matrix *site diagonal* continuation only price; invariance per-site for the real terms. Needn't claim that for the complex increment, which can use gauge covariance of its entire value. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock MeasureTheory Spin Spin.Cellar Spin.Cellar.Pass Spin.Pledge Branch Thera Helm Basement Currency RealBook Bridge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty} {r ε d:ℝ}
def streamR (F G:Finset I)(A T:Op I)(C C':ℝ→Op I):= (∫ v in (0:ℝ)..0+1,firstD A T (C 0) v)+(∫ v in (0:ℝ)..0+1,prepD A T (C v) (C' v))-(∫ v in (0:ℝ)..0+1,starD F G A T (C 1) v)+(∫ v in (1:ℝ)..1+1,passD F G A T (C v) (C' v))
lemma buys_base (H P W:Pledge)(h:0≤d)(p:0≤r)(q:r<1):∃ V:Pledge,∀{I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{A C M:Raw D I}, Capacity b d→H.Costs b A→P.Costs b C→W.Costs b M→(∀ i,Bore (A i) (C i) r)→ V.Costs b (fun i=> seedM (A i) (M i) (C i)) ∧ V.Costs b (fun i=> dinoM (A i) (M i) (C i)):=by
 let U:=unary; obtain ⟨V,v⟩:= contexts_budget U U U H P U (c:=1) zero_lt_one h r p q; let T:=W.times V; refine ⟨T.scales ‖(2:ℂ)⁻¹‖,?_⟩; intro I D Y _ _ _ _ _ _ b A C M c hA hC hM hb
 have ht:U.Costs b (fun _=>cutM (∅:Finset I)):=by simp_rw [show cutM (∅:Finset I)=0 from by unfold cutM; simp]; exact Costs.free
 have he : unary.Costs b (fun _=>0) := Costs.free
 exact ⟨(Costs.mul hM (Costs.transpose (v (D:=D) (K:=fun _=>(∅:Finset I)) (T:=fun _=>∅) (Y:=Y) (S:=fun _=>(1:Op I)) c ht ht Costs.one hA hC (fun i=> Arrange.regular (hb i)) Costs.one he he Costs.one))).up (scales_le T _), Costs.smul (Costs.mul (Costs.stalk hM) (Costs.transpose (v (D:=D) (K:=fun _=>(∅:Finset I)) (T:=fun _=>∅) (Y:=Y) (S:=fun _=>(1:Op I)) c ht ht Costs.one hA hC (fun i=> Arrange.regular (hb i)) he Costs.one he Costs.one))) _⟩
namespace Brooks
structure Feeds (T:Pledge)(b:Stage Y I D Empty)(F G:D→Finset I)(A M:Raw D I)(C C': D→ℝ→Op I): Prop where
 first : T.Costs (rope 0 b) (fun i=> firstD (A i.1) (M i.1) (C i.1 0) i.2.val)
 prep : T.Costs (rope 0 b) (fun i=> prepD (A i.1) (M i.1) (C i.1 i.2.val) (C' i.1 i.2.val))
 stir : T.Costs (rope 0 b) (fun i=> starD (F i.1) (G i.1) (A i.1) (M i.1) (C i.1 1) i.2.val)
 slips : T.Costs (rope 1 b) (fun i=> passD (F i.1) (G i.1) (A i.1) (M i.1) (C i.1 i.2.val) (C' i.1 i.2.val))
private lemma on0 (x:PartH 0):x.val∈Set.Icc (0:ℝ) 1:= by simpa only [PartH,zero_add] using x.property
private lemma on1 (x:PartH 1):x.val∈Set.Icc (1:ℝ) 2:= by simpa only [PartH, one_add_one_eq_two] using x.property

theorem feeds (P Q W H:Pledge)(p:0≤d)(u:0<ε)(h:0≤r)(v:r<1): ∃ T:Pledge,∀ {I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{F G:D→Finset I}{A M:Raw D I}{C C': D→ℝ→Op I}, Stoke F G A M C C' b P Q W H ε r d→Feeds T b F G A M C C':=by
 obtain ⟨T,t⟩:= buy_tilt P Q p; let L:= (unary.plus (W.plus W)); obtain ⟨U,f⟩:= funding W W L T u d p; let K:= U.times U; let X:=T.bond U; let D':= (H.bond Q).bond K; obtain ⟨B,w⟩:=buys_base X H D' p h v; refine ⟨B,?_⟩; intro I D Y _ _ _ _ _ _ b F G A M C C' S
 let E:Stage Y I (D × PartH 0) Empty:= rope 0 b; let C₀(i:D):= C i 0; let C₁ (i:D):=C i 1; let M' i:=mood (A i) (M i); have hb:=S.cap; let e(x: D × PartH 0):ℝ:= x.2.val; let c := spine 0 hb
 have he:T.Costs b M':= t hb (Spin.Hole.tuned_one b (1:ℝ) (by simp)) S.am S.wm (fun x=> (S.peak x).proj) (fun x=> (S.peak x).she)
 have ht:= t c (show Trans.Tune E e 1 from token_t) (pullT 0 _ S.am) (pullT 0 _ S.wm) (fun x=> (S.peak _).proj) fun x=> (S.peak _).she
 have hu: L.Costs b (fun i=> shun I (F i) (G i)):=Costs.sub Costs.one (Costs.plus S.pA S.pB)
 let h₀:=fun x=> cutM (F x); let h₁:=fun x=> cutM (G x); let pL(i:D):=shun I (F i) (G i)
 have p0:= f (h₀ ∘ Prod.fst) (h₁ ∘ Prod.fst) (pL ∘ Prod.fst) (M' ∘ Prod.fst) e c (fun x=> (S.peak _).rails) (pullT 0 _ S.pA) (pullT 0 _ S.pB) (pullT 0 _ hu) (pullT 0 M' he) token_t
 have p1:= f h₀ h₁ pL M' _ hb (fun i=> (S.peak i).rails) S.pA S.pB hu he (Spin.Hole.tuned_one b (0:ℝ) (by simp))
 have upH:H ≤ D':=(bond_lel H Q).trans (bond_lel ..); have ht':T≤X:=bond_lel ..; have hu':U≤X:=bond_ler ..
 refine ⟨?_ ,?_ ,?_,?_⟩
 · have hc:=pullT 0 _ (subview 0 0 (f:=C) (by simp [PartH]) S.walk1); exact (w c (ht.up ht') hc ((pullT 0 _ S.wm).up ((bond_ler H Q).trans (bond_lel ..))) (fun i=> (S.peak i.1).front i.2.val (on0 i.2))).1
 · exact (w c ((pullT 0 _ he).up ht') S.walk1 (S.der1.up upH) (fun i=> (S.peak i.1).center _ (on0 i.2))).2
 · have h':D'.Costs (rope 0 b) (fun t=> cue (F t.1) (G t.1) (A t.1) (M t.1) t.2.val):= (Costs.mul p0.incline p0.strat).up (bond_ler ..)
   exact (w c (p0.shear.up hu') (pullT 0 _ (subview 0 1 (by simp [PartH]) S.walk1)) h' (fun i=> (S.peak i.1).warp _ (on0 i.2))).1
 exact (w (spine 1 hb) ((pullT 1 _ p1.shear).up hu') S.walk2 (S.der2.up upH) (fun i=> (S.peak _).back _ (on1 i.2))).2

def quadruple(P:Pledge):= ((P.plus P).plus P).plus P
variable {T:Pledge}{F G:D→Finset I}{A M:Raw D I}{C C': D→ℝ→Op I}{b:Stage Y I D Empty}(h:Feeds T b F G A M C C')
include h
lemma sell : (quadruple T).Costs b (fun i=> streamR (F i) (G i) (A i) (M i) (C i) (C' i)):= Costs.plus (Costs.sub (Costs.plus (plan 0 (F:=fun x v=>firstD (A x) (M x) (C x 0) v) h.first) (plan 0 (F:=fun x v=> prepD (A x) (M x) (C x v) (C' x v)) h.prep)) (plan 0 (F:=fun x=> starD (F x) (G x) (A x) (M x) (C x 1)) h.stir)) (plan 1 (F:=fun x v=>passD (F x) (G x) (A x) (M x) (C x v) (C' x v)) h.slips)
lemma road (x:D): (streamR (F x) (G x) (A x) (M x) (C x) (C' x)).trace=sweepR (F x) (G x) (A x) (M x) (C x) (C' x) := by
 unfold streamR; rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_add, testTrace 0 (F:=fun x v=>firstD (A x) (M x) (C x 0) v) h.first, testTrace 0 (F:=fun x v=> prepD (A x) (M x) (C x v) (C' x v)) h.prep,testTrace 0 (F:=fun x=> starD (F x) (G x) (A x) (M x) (C x 1)) h.stir,testTrace 1 (F:=fun x v=>passD (F x) (G x) (A x) (M x) (C x v) (C' x v)) h.slips]; simp only [zero_add,one_add_one_eq_two]; rfl
end Brooks
end YM.CF.BPress.Pf
