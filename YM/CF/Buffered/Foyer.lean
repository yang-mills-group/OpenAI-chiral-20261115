import YM.CF.Buffered.TuneRequest
/-! Simultaneous level-zero tickets, no power-root loss after gauge selection. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 510000
noncomputable section
namespace YM.CF.Buffered.Alloy
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember Mint Mint.Roe Fock Dial Gall Advance Pastry MeasureTheory Push.SectorMeasure
open Ballad
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H L':ℝ}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
variable (F:∀ i,Loom (mid (N i) B)) (W:∀ᶠ i in atTop,SkinT (I i) (F i) e)
variable {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (U:Mint.Roe.Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)
variable {α k' R':ℝ}{hk kb:ℕ}
private lemma f_inc {N:Side}(Z:Pane N){x y:ℝ} (p:x≤y)(t:flags x Z=∅) : flags y Z=∅:=by apply Finset.eq_empty_iff_forall_notMem.mpr; intro i h; obtain ⟨f,u,v⟩:= (flags_spec ..).mp h; exact notMem_empty _ (t ▸ (flags_spec ..).mpr ⟨f,u,p.trans_lt v⟩)
include Z
private lemma owes (v:0<k'): ∀ᶠ i in atTop,(I i).p.threshold ≤ k':=(Z.support.and ((Mint.damp Z.path.rank).shrinks.eventually (ge_mem_nhds v))).mono fun _ h=>le_trans h.1.1.le h.2 -- include Z
include D Z W U g
lemma healing : ∀ᶠ i in atTop, ‖vac0 P (I i) (F i)‖ ≤ (2*E'+1)* drip (I i) P := by
 obtain ⟨Q,A,QF⟩:= caesar D Z; obtain ⟨Wk,Wb⟩:= surge Z d
 filter_upwards [Roe.touch D Z,Z.support,QF,W,Z.tend.eventually_ge_atTop (n₀:ℝ), Z.path.infl, allowance D Z 1 1 le_rfl one_pos, owes Z U.pit,((A 10).eventually (ge_mem_nhds U.knot)), Wb,Wk.shrinks.eventually (ge_mem_nhds one_pos)] with i ⟨u,p⟩ ⟨X',J,gx,hQ,w',v⟩ q F' hn ht A' fU hi ⟨a,v'⟩ t
 let Y:Mark (NP i):=1; have hN:n₀ ≤ (NP i).val:=Nat.cast_le.mp hn; let z:=drip (I i) P
 have hM:= U.site.trans hN
 rw [order_one]; apply le_trans (marked_up (F:=F') D hM Y 1 z (2*E') (rite_c (1:FC _)) (bonB J gx) zero_le_one p.le ?_ ?_) (by unfold z; nlinarith)
 · intro V₀ y; obtain ⟨f,d',gT,h⟩:=q.roll V₀.1 y
   have hu:= U.wear (N i) hN V₀.1 (I i).J.M _ _ (Q i) (spiral _ gT) q.pose q.data hi h; let vA:= bloom NP r x i; have he:= tile_p V₀.1 (show 0 ≤ tame x i from ht.2.2.1.le) Z.wind.le (show _ from (by rw [← X']; exact y)); refine le_trans (pace (d':=E'*Kea.angel (N i) P (I i).J.M) D (I i) (F i) F' hM J U.sap.le v' Z.wind.le (zero_le_one.trans Z.bold) Z.size Y V₀ y he ?_ ?_ a ?_ t) (le_of_eq (by ring))
   · change Gall.Yep _ (acts (star (1:FC _)) _) _ _; rw [star_one,act_one]; exact hu
   · exact mul_nonneg U.lark.le ((angel_p hP D.stmt (D.plan _ hM).1 D.p D.eP _ (D.plan _ hM).2).le) -- order stuck
   intro k; exact (U.draw _ hN _ (f_inc V₀.1 fU y) _ k).weigh g U.sap.le
 intro v h; refine le_trans (mask D (I i) (F i) F' hM J v h Z.wind.le Z.bold Z.size gx ht.2.1.le Z.clip.le hQ Y _) ?_; change ‖(1:FC _)‖*_≤_; rw [norm_one]; simpa using A' 0 (by exact_mod_cast Nat.zero_le _)

omit U g
variable {D₁ C₁ J₁ v₁:ℝ}{R w₁ t₁ t₂:ℕ}
include α -- tune not required
lemma marcs (T: Ballad.Tower D R D₁ H C₁ α J₁ w₁ t₁) (p:Crop j H R' v₁ t₂)(u:0<α)(k₁:R' ≤ h) : ∀ᶠ i in atTop, ∀ (J:Type) [Fintype J] [DecidableEq J],∀ (S:Single (NP i)→ J) (Q:J→ Melody B R) (b:Bool)(L:List J), L.Nodup → (L.length:ℝ) ≤ eur NP i^4 → (∀ j', LedgerR (NP i) j s' C₁ (α/8) b (Q j')) → Payments w₁ S Q →
    ‖num0 P (I i) (F i) (Melody.festival Q b L)‖≤ (2*D₁+1)*drip (I i) P*α^L.length := by
 obtain ⟨Q,A,QF⟩:= caesar D Z; obtain ⟨Wk,Wb⟩:= surge Z H; let k₀:=k+t₁+t₂
 let Y:=max 1 (Melody.cuts R 0)
 filter_upwards [Roe.touch D Z,Z.support,QF,W,Z.tend.eventually_ge_atTop (k₀:ℝ), Z.path.infl, allowance D Z Y α (le_max_left ..) u, owes Z p.width,((A 10).eventually (ge_mem_nhds T.size)), Wb,Wk.shrinks.eventually (ge_mem_nhds one_pos)] with i ⟨u',p'⟩ ⟨X',J,gx,hQ,w',v⟩ q F' hn ht A' fU hi ⟨a,v'⟩ t
 intro m' _ _ S Q' b₁ L hN n W' q'; let Z':= Melody.festival Q' b₁ L (N:=NP i); let x:=α^L.length; have hx:0<x:=pow_pos u _
 have hM:k₀ ≤ (NP i).val:= Nat.cast_le.mp hn; have hy:k ≤ (NP i).val:=by unfold k₀ at hM; omega
 refine le_trans (marked_up (F:=F') D hy Z' x (drip (I i) P*x) (2*D₁) (Env.compact (Melody.festival_cont ..)) (bonB J gx) hx.le (by positivity) ?_ ?_) (by unfold x; nlinarith);
 · intro V₀ y; obtain ⟨f,d',gT,h'⟩:=q.roll V₀.1 y
   have hu:= T.wear (m:=N i) (by change t₁ ≤ (NP i).val; unfold k₀ at hM; omega) m' S Q' (drawn (F i) V₀) b₁ L hN q' (I i).J.M f d' (Q i) (spiral _ gT) h' q.pose q.data hi W'; have he:= tile_p V₀.1 (show 0 ≤ tame _ i from ht.2.2.1.le) Z.wind.le (show _ from (by rw [← X']; exact y)); refine le_trans (pace D (I i) (F i) F' hy J T.loom.le v' Z.wind.le (zero_le_one.trans Z.bold) Z.size Z' V₀ y he hu ?_ a ?_ t) (le_of_eq (by unfold x; ring))
   · exact mul_nonneg (mul_nonneg T.cup.le ((angel_p hP D.stmt (D.plan _ hy).1 D.p D.eP _ (D.plan _ hy).2).le)) hx.le
   intro k; exact (p.costs (N:=NP i) (by unfold k₀ at hM; omega) V₀.1 (f_inc V₀.1 fU y) _ k).weigh k₁ T.loom.le
 intro v h; refine le_trans (mask D (I i) (F i) F' hy J v h Z.wind.le Z.bold Z.size gx ht.2.1.le Z.clip.le hQ Z' _) (le_trans (mul_le_mul_of_nonneg_right (le_trans (Melody.festival_norm _ _ _ _) ?_) (Real.exp_pos _).le) (A' L.length n))
 exact pow_le_pow_left₀ (by unfold Melody.cuts Melody.extra; have he :0 ≤ Melody.maximum R 0:= Lead.maximumV_nn ..; positivity) (le_max_right ..) _
#print axioms healing
#print axioms marcs
end YM.CF.Buffered.Alloy
