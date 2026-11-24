import YM.CF.BPress.Pf.Currency
import YM.CF.BPress.Pf.Log
import YM.CF.BPress.Spin.Breach
/-! Costs while not constructing the geometry. Log €s don't need Wick continuity assumption. Real costs built WITHOUT looking at any path arguments (H,X, uniforms): thus can extend them to that space of arguments. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock MeasureTheory Spin Spin.Cellar Spin.Cellar.Pass Spin.Pledge Branch Thera Helm Basement Currency
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty} {r ε d:ℝ}
variable (T:Pledge)
namespace RealBook
lemma embrace (A:Op I) : ‖A‖≤1→ (1:ℝ) • (1:Op I) ≤ 1+star A*A ∧ 1+star A*A ≤ (3:ℝ) • 1:=by
 intro h; refine ⟨one_smul ℝ 1|>.le.trans (le_add_of_nonneg_right (star_mul_self_nonneg _)), (add_le_add le_rfl ((op_le_norm_one (IsSelfAdjoint.star_mul_self A)).trans (smul_le_smul_of_nonneg_right (?_ : ‖star A * A‖≤(2:ℝ)) zero_le_one))).trans_eq ?_⟩; swap; · module
 rw [CStarRing.norm_star_mul_self]; exact (mul_le_one₀ h (norm_nonneg _) h).trans (by norm_num)
def rangeS(A:Pledge)(B:Pledge):=((A.times B).times A).plus (unary.plus A)
lemma clocks{A B:Raw D I}{P Q:Pledge}(p:P.Costs b A)(h:Q.Costs b B): (rangeS P Q).Costs b (fun i=>terrace (A i) (B i)):=Costs.plus (Costs.mul (Costs.mul p h) p) (Costs.sub Costs.one p)
theorem reality(p:0<ε)(v:ε≤1)(h:0≤d)(L T U:Pledge): ∃ P:Pledge,∀{I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{A S:Raw D I}{B C:D→Finset I}, Capacity b d→(∀ x, IsStarProjection (A x))→ (∀ x,TagG (A x) (S x))→(∀ x,‖S x‖≤1)→(∀ x, Pass (cutM (B x)) (cutM (C x)) (shun I (B x) (C x)) (mood (A x) (S x)) ε)→
 T.Costs b A→ U.Costs b S→ L.Costs b (fun x=>cutM (B x))→ L.Costs b (fun x=>cutM (C x))→ P.Costs b (fun x=>permit (A x) (S x))∧ P.Costs b (fun x=>permitX (B x) (A x) (S x)) ∧ P.Costs b (fun x=>permitY (B x) (C x) (A x) (S x)) :=by
 let W:= unary.plus (L.plus L); obtain ⟨K,t⟩:=buy_tilt T U h; have he : ε < 3 := v.trans_lt (by norm_num)
 obtain ⟨R,r⟩:= Basement.funding L L W K p d h -- maybe namespace
 obtain ⟨M₀,H₀⟩:= rcpt (unary.plus (U.times U)) (by norm_num:0<(1:ℝ)) (by norm_num:(1:ℝ)<3) h; obtain ⟨M₁,H₁⟩:=rcpt (rangeS L K) p he h; obtain ⟨M₂,H₂⟩:=rcpt (rangeS L (unary.plus R)) p he h; let M:= (M₀.bond M₁).bond M₂; refine ⟨M.scales ‖(1/2:ℝ)‖,?_⟩; intro I D Y _ _ _ _ _ _ b A S X E B x y z n H G p₁ p₂
 let w:= (fun _:D=>(1:ℝ)); let ξ: Trans.Tune b w 1:=Spin.Hole.tuned_one b _ (by norm_num); have ht:= t B ξ H G x y; let T': Raw D I:= fun i=>mood (A i) (S i); have ht: K.Costs b T':=ht
 have hu:= (r _ _ _ _ w B n p₁ p₂ (Costs.sub Costs.one (Costs.plus p₁ p₂)) ht ξ).ray0
 have A₀:= H₀ B (Costs.plus Costs.one (Costs.mul (Costs.stalk G) G)) (fun i=>embrace _ (z i))
 have A₁:=H₁ B (clocks p₁ ht) (fun i=> let N:= n i; Issued.price1 (cutM_idp _) N.a N.payP p v)
 have A₂:= H₂ B (clocks p₂ (Costs.sub Costs.one hu)) (fun i=> let N:= n i; Issued.price1 (cutM_idp _) N.r0.one_sub N.pay0 p v)
 exact ⟨ Costs.scale (Costs.up (Q:=M) A₀ ((bond_lel M₀ M₁).trans (bond_lel ..))) _, Costs.scale (Costs.up (Q:=M) A₁ ((bond_ler M₀ M₁).trans (bond_lel ..))) _, Costs.scale (Costs.up (Q:=M) A₂ (bond_ler ..)) _⟩

section dynamic
structure Stoke (F G:D→Finset I)(A T: Raw D I)(C C': D→ℝ→Op I)(b:Stage Y I D Empty)(P W B H:Pledge) (ε r d:ℝ): Prop where
 peak:∀ x, Issued (F x) (G x) (A x) (T x) (C x) (C' x) r ε
 cap: Capacity b d
 am:P.Costs b A
 wm:W.Costs b T
 pA:B.Costs b (fun t=> cutM (F t))
 pB:B.Costs b (fun t=> cutM (G t))
 walk1:H.Costs (rope 0 b) (fun i=> C i.1 i.2.val)
 walk2:H.Costs (rope 1 b) (fun i=> C i.1 i.2.val)
 der1:H.Costs (rope 0 b) (fun i=> C' i.1 i.2.val)
 der2:H.Costs (rope 1 b) (fun i=> C' i.1 i.2.val)

lemma rampP (H P W B:Pledge)(h:0≤d)(p:0<ε) : ∃ S:Pledge,∀{I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{F G:D→Finset I}{A T:Raw D I}{C C': D→ℝ→Op I}{r:ℝ}, Stoke F G A T C C' b P W B H ε r d→ S.Costs b (fun i=> ramp (shun I (F i) (G i)) (cutM (F i)) (mood (A i) (T i))) :=by
 obtain ⟨K,k⟩:=buy_tilt P W h; obtain ⟨L,e⟩:= funding B B (unary.plus (B.plus B)) K p d h; refine ⟨L,?_⟩; intro I D Y _ _ _ _ _ _ b F G A T C C' r g
 let t: Trans.Tune b (fun _=>1) 1:= Spin.Hole.tuned_one b _ (by simp)
 exact (e _ _ _ _ _ g.cap (fun i=>(g.peak i).rails) g.pA g.pB (Costs.sub Costs.one (Costs.plus g.pA g.pB)) (k g.cap t g.am g.wm (fun i=>(g.peak i).proj) (fun i=>(g.peak i).she)) t).rump
lemma defray (H P W B:Pledge)(h:0≤d)(p:0<ε)(f:0≤r)(u:r<1):∃ S:Pledge,∀{I D Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{F G:D→Finset I}{A T:Raw D I}{C C': D→ℝ→Op I}, Stoke F G A T C C' b P W B H ε r d→ S.Costs b (fun i=> billZ (F i) (G i) (A i) (T i) (C i 2)):=by
 obtain ⟨K,k⟩:=rampP H P W B h p; let a:=(1+r^2)/2; have hv: r^2<1:=pow_lt_one₀ f u (by norm_num); obtain ⟨V,v⟩:= (Serve.tollP K H).zoom h (k:=a) (by unfold a; positivity) (by unfold a; linarith)
 refine ⟨V.scales ‖(1/4:ℝ)‖,?_⟩; intro I D Y _ _ _ _ _ _ b F G A T C C' X
 exact Costs.scale ((v X.cap (Costs.neg (Serve.loss_p (k X) (subview 1 2 (by rw [Currency.PartH]; norm_num) X.walk2))) (fun i=>(norm_neg ..).le.trans (((X.peak i).drum.backB.costs).trans (by unfold a; linarith)))).2) _
end dynamic
end RealBook
end YM.CF.BPress.Pf
