import YM.CF.BPress.Spin.Reeds
/-! Store pricing including mask bits. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin.Hole
open Function Filter NormedSpace Finset Lattice Fock SU Lat Cube Tenant Branch Tulip Scroll Dial Thera Nacre Laic Paint Eye Pledge Stride Quad Blank Cellar Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{c σ d:ℝ}{A: Raw (OpenW N d) (Single N)}{P:Pledge}{I:Type}

-- Finset default topology? need discrete
scoped instance (N:Side) : TopologicalSpace (Support N):= ⊥
scoped instance (N:Side): DiscreteTopology (Support N):=⟨rfl⟩
abbrev Painted (A: Raw (OpenW N d) (Single N))(c σ:ℝ):= {x: OpenW N d × Support N × Paint (More N)// Meets c x.2.1 (A x.1) ∧ MatLite x.2.2 σ}
namespace Painted
variable (x y:Painted A c σ)
def trueA := A x.val.1
def path := x.val.2.2
def p := x.val.2.1
def P' : Op (Single N):= Lock x.p true
def Pc (u:ℝ):= smoothP (pos x.p) (neg x.p) (loose x.p) x.trueA u
def tease (u:ℝ):= leak (x.Pc u) x.path
def turn (A:Raw (OpenW N d) (Single N))(c σ:ℝ): Form N (Painted A c σ):= {
 eval S x y:= invitation S x.val.1.val y.val.1.val + ((∑ i∈ news S, ‖path x (node i)- path y (node i)‖)+(∑ i∈news S, if (decide (i∈x.p)≠decide (i∈ y.p)) then 1 else 0))
 pos S x y:= add_nonneg invitation.positive (add_nonneg (sum_nonneg (fun _ _=>norm_nonneg _)) (sum_nonneg fun _ _=>ite_nonneg zero_le_one le_rfl))
 mono{S T} h x y:= by
    have he : news S⊆news T:=fun _ p=>mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp p).2⟩
    exact add_le_add (invitation.mono h) (add_le_add (sum_le_sum_of_subset_of_nonneg he (fun _ _ _=> norm_nonneg _)) (sum_le_sum_of_subset_of_nonneg he (fun _ _ _=> ite_nonneg zero_le_one le_rfl))) }
lemma seen (S:Support (More N))(i:Site N)(p:node i∈S): ‖path x (node i)-path y (node i)‖≤ (turn A c σ).eval S x y:=by
 let g(i:Site N):= ‖path x (node i)-path y (node i)‖; apply le_trans (single_le_sum (f:=g) (fun i _=> norm_nonneg _) (mem_filter.mpr ⟨mem_univ _,p⟩ : i∈news S)) (le_add_of_nonneg_left invitation.positive|>.trans' ?_); exact le_add_of_nonneg_right (sum_nonneg fun _ _=> ite_nonneg zero_le_one le_rfl)
lemma present : Bits (turn A c σ) (fun x=>x.p):=by
 intro S x y i hi v; let K(i:Site N):ℝ:=if (decide (i∈x.p)≠decide (i∈y.p)) then 1 else 0; have ht:K i=1:=by rcases v with ⟨v,u⟩|⟨v,u⟩ <;> simp [K,v,u]
 apply le_trans ?_ (le_add_of_nonneg_left invitation.positive); apply le_trans ?_ (le_add_of_nonneg_left (sum_nonneg fun _ _=> norm_nonneg _)); exact ht.symm.le.trans (single_le_sum (f:=K) (fun _ _=>ite_nonneg zero_le_one le_rfl) (mem_filter.mpr ⟨mem_univ _,hi⟩ : i∈news S))
lemma acquire (p:0<c)(h:c≤1)(m:∀ x,IsStarProjection (A x)): Pass (pos x.p) (neg x.p) (loose x.p) x.trueA c:= passed (m x.val.1) p h x.property.1
end Painted

lemma stream_node {D: Type}[TopologicalSpace D] (g:Form N D){C:ℝ}(U:D→ Paint (More N))(u:∀ x, MatLite (U x) C)(h:Continuous U)(v:∀ (X:Support (More N)) (x y:D) (i:Site N), node i∈X→ ‖U x (node i)-U y (node i)‖≤g.eval X x y) : Form.Comes g (stream C) (fun x=> coupling (U x)):=by
 let K:=max C 1; have ht:1≤K:=le_max_right ..; have hk:0≤K:=zero_le_one.trans ht
 refine (row_earn g.full Form.paid (show 0≤(1:ℝ) by norm_num) (fun i _=>Empty.elim i) (coupling_cont.comp h) hk 0 ?_ ?_ ?_).books (le_max_right ..)
 · exact fun x i j p=> by rw [comp_apply,atX]; exact if_neg fun s=>ne_of_gt p ((congrArg (g.stage.F.span (g.stage.home i)) ((congrArg node s).symm : g.stage.home j=g.stage.home i)).trans (separation_self _)) -- tune
 · exact fun i j x=> (norm_entry ..).trans (coupe_norm (fun b=> (u x b).trans (le_max_left ..)) hk)
 intro i j x y; let S:=bay (terr (More N)) (home N i) 0; rw [comp_apply,comp_apply,atX,atX]; split; swap; · rw [sub_self,norm_zero]; exact mul_nonneg hk (g.pos ..)
 refine (norm_entry (nodeC (U x (home N i))-nodeC (U y (home N i))) (i.1.2,i.2) _).trans ((node_move ..).trans ((v S x y _ ((bay_mem _).2 ((terr (More N)).reflex _ |>.le))).trans (le_mul_of_one_le_left (g.pos ..) ht)))

-- (adjust stream lemma to see node readings only beforehand).
lemma leak_budget (P:Pledge)(u:0<c)(s:c≤1)(σ:ℝ): ∃ U:Pledge, ∀{N:Side}{d:ℝ}{A: Raw (OpenW N d) (Single N)},(∀ x,IsStarProjection (A x))→(AtW N d).Comes P A→∀ i:ℝ, ‖i‖≤1→ (Painted.turn A c σ).Comes U (fun x=> x.tease i) :=by
 let B:= stream 1; let C:= unary.plus (B.plus B); let y:= stream σ; obtain ⟨W,H⟩:= Basement.funding B B C P u quota Form.paid; refine ⟨((unary.plus W).times y).times W,?_⟩; intro N d A h g v p
 let S:=Painted.turn A c σ; let t:=Painted A c σ
 have he(u): S.Comes B (fun (x:t)=> Lock (Painted.p x) u):=by
    apply trackprice S Painted.present _ u; intro i; have ht : Continuous (Painted.p (A:=A) (σ:=σ) (c:=c)):=continuous_fst.comp ((continuous_snd).comp continuous_subtype_val); let X:Set (Support N):={x : Support N|i∈x}; exact (isClopen_discrete X).preimage ht
 have hl : S.Comes C (fun (x:t)=> loose (Painted.p x)):=by simp_rw [(plusMinus _).l0]; exact Costs.sub Costs.one (Costs.plus (he true) (he false))
 have ht:= H _ _ _ _ _ S.full (fun (x:t)=> Painted.acquire x u s h) (he true) (he false) hl (Form.pulls g (fun (x:t)=> x.val.1) (continuous_fst.comp continuous_subtype_val) (F':=S) fun S x y=>le_add_of_nonneg_right (add_nonneg (sum_nonneg (fun _ _=>norm_nonneg _)) (sum_nonneg fun _ _=>ite_nonneg zero_le_one le_rfl))) (tuned_one S.stage v p)
 let V(x:Painted A c σ):= coupling x.path; have hv:S.Comes y V:= stream_node S (Painted.path (c:=c) (A:=A) (σ:=σ)) (fun x=>x.property.2) (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) (fun x y z i=> Painted.seen y z x i)
 exact Costs.mul (Costs.mul (Costs.sub Costs.one ht.shear) hv) (Costs.stars ht.shear)
end YM.CF.BPress.Spin.Hole
