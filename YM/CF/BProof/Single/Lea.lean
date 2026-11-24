import YM.CF.BProof.Single.Atmos
import YM.CF.BProof.Stint.Functional
import YM.CF.BProof.Align.Gust
/-! Purchase B-Lspeed at actual tilt. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint SU.Pair Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r ε:ℝ}
structure Core (j:ℕ)(a b l r:ℝ)(N:Side) where
 M: Male
 aim: Buyer a b l r N
namespace Core
variable {N:Side}(F:Core j a b l r N)(P:Ready j a b l r)(X:Bkg (More N))
-- j_*
abbrev upright := spar j F.M X
abbrev wind := gust (F.upright X) (F.aim.val.den X)
abbrev bent (u:ℝ) := slit (F.upright X) (F.wind X) u
def θ (u:ℝ):= land (F.upright X) (F.bent X u)
include P
theorem leaning {d:ℝ}(h:P.minN≤N.val)(k:d≤P.hT)(g:Guard X d): Gust (F.upright X) (F.wind X):=gustH (P.proj N h F.M X (g.shrink k)) _
theorem θp {d:ℝ}(h:P.minN≤N.val)(k:d≤P.hT)(g:Guard X d)(u:ℝ): IsStarProjection (F.θ X u):=((F.leaning P X h k g).fit u).landed
omit P in
theorem windCost (h:IsStarProjection (F.upright X)): ‖F.wind X‖≤‖F.aim.val.den X‖:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (h.norm_le _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (h.one_sub.norm_le _))))
-- cost for shear
theorem earnsWind (h:P.minN≤N.val){d:ℝ}(k:d≤P.hT):let t:=(iron N P.hT d).mark; Earn (((Pay.simple.add P.hP).mul P.hP).mul P.hP) t t (fun x=>F.wind x.val):=by intro t; have he:=P.mat N h F.M d k; exact ((((Earn.one t).minus he).times (P.tilt N h F.aim d k)).times he)
theorem earnsθ : ∃ p:Pay, ∀ {N:Side}(F:Core j a b l r N), P.minN≤N.val→∀ {d:ℝ}, d≤P.hT→let t:=(iron N P.hT d).mark; Earn p t t (fun x=>F.θ x.val 1):=by
 let k:=P.hP; let w:=((Pay.simple.add k).mul k).mul k; let s:=(Pay.simple.add (w.wage 1)).mul k; obtain ⟨t,U⟩:=inverseCost (by norm_num: (0:ℝ)<1) quota_p.le ((s.mul s).add (.add Pay.simple k)); refine ⟨s.mul (t.mul s),?_⟩; intro n F h d g M; let f:= iron n P.hT d; have he:= P.mat n h F.M d g; have hs: Earn s M M (fun x=> F.bent x.val 1):= ((Earn.one M).plus ((F.earnsWind P h g).wage (c:=1) (by simp))).times he; exact hs.times ((U f.cap ((hs.adj.times hs).plus ((Earn.one M).minus he)) (fun i=>le_trans (Eq.le (one_smul ℝ 1)) ((F.leaning P i.val h g i.property).bound 1))).times hs.adj) -- tune
-- tilting at trivial remains upright
lemma θtriv(h:P.minN≤N.val)(u:ℝ) : F.θ 1 u=F.upright 1:=by
 have he:=P.proj N h F.M 1 (guard0 P.hTpos.le); let A:=F.upright 1; change IsStarProjection A at he; change land A (slit A _ u)=A; have ht:F.wind 1=0:=by unfold wind gust; rw [den_void,mul_zero,zero_mul];
 rw [ht,slit,Align.bend,smul_zero,add_zero,one_mul,land,send,entered,he.isSelfAdjoint, he.isIdempotentElem, add_sub_cancel,inv_one,one_mul,he.isIdempotentElem] -- tune
end Core
variable (P: Ready j a b l r)
include P
structure Shelter (P:Ready j a b l r)(δ ε:ℝ) : Prop where
 limit : δ≤P.hT
 lamp : ∃ v:ℕ, ∀ {N:Side}, v≤N.val→ ∀ F:Core j a b l r N, ∀ X:Bkg (More N),Guard X δ→ P.minN≤N.val ∧ ‖F.wind X‖≤1/2 ∧∀ B: Quilt N,(∀ i, SealH (B i))→ Speed X B δ → ∀ u:ℝ, ‖u‖≤1 → ‖F.θ X u * pair B - pair B * cc (F.θ X u)‖≤ε
lemma WindShield (h:1≤j)(u:0<ε) : ∃ δ:ℝ, 0<δ ∧ Shelter P δ ε:=by
 obtain ⟨d,hd,Z,n,F⟩:= roofLine P h (half_pos u); obtain ⟨e,he,w,K⟩:= P.small _ (lt_min (by norm_num : (0:ℝ)<1/2) (show 0<ε/16 by positivity)); let δ:=min d e; let Gx:= (min_le_left d e).trans Z; refine ⟨δ, lt_min hd he, Gx, max n (max w P.minN),?_⟩; intro N hp D X H; have ht:P.minN≤N.val:=by omega
 have hr:= D.leaning P X ht Gx H; have hz:‖D.wind X‖≤ min (1/2) (ε/16):=(D.windCost X hr.1).trans (K _ (by omega) D.aim X (H.shrink (min_le_right ..))); refine ⟨ht,hz.trans (min_le_left ..),fun B Hb Hx t hT=>?_⟩; let T:HScope N 1:=⟨B,fun i=>(CStarRing.norm_of_mem_unitary (Hb i).norm).le⟩
 let W:=pair B; have hw: ‖W‖≤1:=pair_bound zero_le_one T.property; have hh:= F (by omega) X T (H.shrink (min_le_left ..)) (Hx.weaker (min_le_left ..)) D.M
 let Y:= D.θ X t-D.upright X; have hg: ‖Y‖≤ 4* (ε/16):= (hr.closet hT (le_trans (hz.trans (min_le_left ..)) (by norm_num))).trans (mul_le_mul_of_nonneg_left (hz.trans (min_le_right ..)) (by norm_num)); change ‖_‖≤ε/2 at hh; rw [show D.θ X t=Y+D.upright X from by unfold Y; rw [sub_add_cancel],cc_add]; rw [add_mul,mul_add,add_sub_add_comm]; apply (norm_add_le ..).trans
 have h1:‖Y*W‖≤‖Y‖:=(norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) hw); have h2:‖W * cc Y‖ ≤‖Y‖:=by refine (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hw).trans_eq ?_); exact Scroll.norm_cc _ -- tune
 exact (add_le_add ((norm_sub_le ..).trans (add_le_add h1 h2)) hh).trans (by linarith only [hg])
end YM.CF.BProof.Spin
