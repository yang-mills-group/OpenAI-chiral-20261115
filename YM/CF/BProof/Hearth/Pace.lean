import YM.CF.BProof.Hearth.Hoard
import YM.CF.BProof.Single.Lea
import YM.CF.BProof.Fig.Stroll

/-! Buying hole bounds with margins on the Uprice neighborhood. Keep qualification on the very
same post fields; board on all their gauge motion is guaranteed by law. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side} {A B: Op (Single N)}
lemma mortgage {P:Op (Single N)}(g:IsStarProjection P){m ε:ℝ}(h:m • P ≤P*B*P)(r: ‖(A-B)*P‖≤ ε) (u:IsSelfAdjoint (A-B)): (m-ε) • P ≤ P*A*P:=by
 let F:=P*(A-B)*P; have hp:IsSelfAdjoint F:=by unfold F IsSelfAdjoint; rw [star_mul,star_mul,u.star_eq,g.isSelfAdjoint,mul_assoc]
 have ht:‖F‖≤ε:=by unfold F; rw [mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (g.norm_le _)).trans r)
 have he:= star_left_conjugate_le_conjugate (op_ge_neg_scalar hp ht) P; rw [g.isSelfAdjoint,mul_neg,neg_mul, Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc,g.isIdempotentElem] at he
 have hx:P*F*P=F:=by unfold F; rw [←mul_assoc,←mul_assoc,g.isIdempotentElem,mul_assoc ((P*_)), g.isIdempotentElem] -- tune
 rw [hx] at he; refine le_trans (b:=(P*B*P)+F) ?_ (le_of_eq ?_); rw [sub_smul,sub_eq_add_neg (m • P) (ε • P)]; exact add_le_add h he; unfold F; noncomm_ring
abbrev CloseH (X:Bkg (More N))(v:ℝ)(S:Support N)(R:ℕ) := ∀ y∈ leaks (halo R (spot S)), scenery (X y) 1 ≤ v
variable {j:ℕ}{a b l r:ℝ} (P:Ready j a b l r)(F:Core j a b l r N) {d:ℝ}
def BoardH (F:Core j a b l r N)(X:Bkg (More N))(S:Support N)(c:ℝ):Prop:=Board (F.θ X 1) (bandCut S true) (bandCut S false) c
lemma peg (s:Support N)(g:P.minN≤N.val)(t:ℕ)(w:Shut t 0 s)(M:ℝ)(m:0<M)(hm:M ≤1)(H:∀ u,(2*M) • bandCut s u≤ bandCut s u*(if u then F.upright 1 else 1-F.upright 1)*bandCut s u) {δ:ℝ}(X:Bkg (More N))(hx:Guard X δ)(h:δ≤P.hT)(k:‖(F.θ X 1-F.θ 1 1)*strip (iron N P.hT δ).st (spot s)‖≤M): BoardH F X s M:=by
 let B:=F.upright 1; let A:= F.θ X 1; have hp: IsStarProjection B:= P.proj N g F.M 1 (guard0 P.hTpos.le); have hv:=F.θp P X g h hx 1; have hu(u): ‖(A-B)*bandCut s u‖≤M:=by
    rw [show B= _ from (F.θtriv P g 1).symm,← spot_strip s (iron N P.hT δ) u, ←mul_assoc]; apply (norm_mul_le ..).trans; exact (mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans k
 refine ⟨hv,(cutM_idp _),(cutM_idp _),duo s,?_,?_,m,hm⟩
 · rw [←show 2*M-M=M by ring]; exact mortgage (cutM_idp _) (H true) (hu true) (hv.isSelfAdjoint.sub hp.isSelfAdjoint) -- H true defeq
 rw [←show 2*M-M=M by ring]; apply mortgage (cutM_idp _) (B:=1-B) (H false) _ (hv.one_sub.isSelfAdjoint.sub hp.one_sub.isSelfAdjoint); rw [show (1-A)-(1-B)= -(A-B) from by abel, neg_mul,norm_neg]; exact hu false
lemma holeBuy(h:1≤j)(t:ℕ)(m:0<t): ∃ M:ℝ,0<M∧ M≤1∧∃ k:ℕ,∃ e:ℝ,0<e ∧ ∀ {N:Side}(F:Core j a b l r N), P.minN ≤ N.val→∀ (d:ℝ), 0≤d → d≤P.hT → ∀ (X:Bkg (More N))(S:Support N),Shut t 0 S→ Guard X d→ CloseH X e S k → BoardH F X S M:=by -- close strictly small gang
 obtain ⟨g,hp,W⟩:=nup h t m; let M:=min (g/2) 1; have ht:0<M:=lt_min (half_pos hp) one_pos; have hx:P.hT>0:=P.hTpos; obtain ⟨p,Y⟩:= Core.earnsθ P; obtain ⟨k,T⟩:= ((tailPaid p).eventually (gt_mem_nhds (show 0<M/4 by positivity))).exists; let C:=16*((k:ℝ)+1)^4*4; have hh:0<C:=by unfold C; positivity
 let u:=M / (2*p.cash); have he:= p.funding; have hu:0<u:=by unfold u; positivity
 refine ⟨M,ht,min_le_right ..,k,u*P.hT/C,(by positivity),?_⟩; intro n F w d q v X S f z e
 have hf:2*M ≤ g:=by linarith only [show M≤g/2 from min_le_left ..]
 apply peg P F S w t f M ht (min_le_right ..) (fun b=>le_trans (smul_le_smul_of_nonneg_right hf (cutM_idp _).nonneg) (W n 0 b _ S f)) X z v
 apply le_trans (cap_compare (Y F w v) (x:=⟨X,z⟩) (y:=⟨1,guard0 q⟩) k (spot S) hu.le ?_)
 · rw [show u*p.cash = M/2 from (by unfold u; field_simp)]; linarith only [T]
 intro i g; change fa X 1 (bay (terr (More n)) i k) / |P.hT| ≤ _; rw [abs_of_pos hx,div_le_iff₀ hx]; refine (fa_bay (show 0 ≤ u*P.hT/C by positivity) (fun i hx=> e i (leaks_up (show bay (terr (More n)) _ k ⊆ _ from (by rw [tract]; exact Corona.halo_mono le_rfl (singleton_subset_iff.mpr g))) hx))).trans_eq ?_
 change C*_=_; field_simp
end YM.CF.BProof.Hearth
