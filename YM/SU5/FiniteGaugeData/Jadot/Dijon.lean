import YM.SU5.FiniteGaugeData.Jadot.Rheims
import YM.SU5.FiniteGaugeData.Brique.Cellar
/-! # Surgical lattice-weight repair, sparse purchase with **two** radii. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief Rheims
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
namespace Dijon
variable {n:Type*}[Fintype n][LinearOrder n]{L S T:Finset n}{A B C P M N Y Q:Op n}
-- patch A with B columns, charge only S. Important using overlap BOTH at spin & mode.
abbrev reforge (S:Finset n)(A B:Op n):= B+ (1-cutM S)*(A-B)*(1-cutM S)
variable {a b c d f m s p k l t u:ℝ} {x:Ket n}
namespace reforge
lemma ocean (S:Finset n)(A B:Op n):star (reforge S A B)=reforge S (star A) (star B):=by unfold reforge; rw [star_add,star_mul,star_mul,(cutM_idp S).one_sub.2,star_sub,mul_assoc] -- assoc tune
lemma touchesA (S:Finset n)(A B:Op n): reforge S A B*cutM S=B*cutM S:=by
 let K:=cutM S; let L:=1-K; have he:L*K=0:=by unfold L; rw [sub_mul,one_mul,show K*K=K from (cutM_idp _).1,sub_self]
 unfold reforge; rw [add_mul,mul_assoc ( (1-cutM S)*(A-B)), show (1-cutM S)*cutM S=0 from he,mul_zero,add_zero]
-- typo assoc star.t
lemma forA (p:acts (cutM S) x=x)(A B:Op n): acts (reforge S A B) x=acts B x:=by nth_rw 1 2 [←p]; rw [←act_mul,←act_mul,touchesA]
lemma subA (S:Finset n)(A B:Op n) : reforge S A B-A=(B-A)*cutM S+cutM S*(B-A)*(1-cutM S):=by unfold reforge; noncomm_ring
lemma fixH (p:0 ≤ A-M)(u:Canon n (1/2) ≤ M)(v:‖B-M‖≤ 1/8)(x:IsSelfAdjoint B)(y:IsSelfAdjoint M): Canon n (1/4)≤ reforge S A B:=by
 let V:=1-cutM S; let X:= V*(A-M)*V; let Z:= V*(B-M)*V; let K:= B-M-Z; have hv:IsStarProjection V:=(cutM_idp _).one_sub; have hz:‖Z‖≤ ‖B-M‖:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (hv.norm_le _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (hv.norm_le _))))
 have hK:‖K‖≤ 1/4:= (norm_sub_le ..).trans (by linarith)
 have he:0≤X:= hv.2.conjugate_nonneg p; have hh:IsSelfAdjoint K:= (x.sub y).sub ((x.sub y).conjugate_self hv.2) -- tune
 have ha: Canon n (-(1/4))≤ K:=(by rw [canon_map,map_neg]; exact (neg_le_neg (algebraMap_mono _ hK)).trans (IsSelfAdjoint.neg_algebraMap_norm_le_self hh))
 rw [show Canon n (1/4)=Canon n (1/2)+Canon n (-(1/4)) from by unfold Canon; rw [←add_smul]; norm_num, show reforge S A B=M+K+X from ?_]
 exact (add_le_add u ha).trans (le_add_of_nonneg_right he)
 unfold K X Z reforge; change B+V*(A-B)*V=M+(B-M-V*(B-M)*V)+V*(A-M)*V; noncomm_ring
lemma discS(h:Commute (cutM S) Q)(q:IsStarProjection Q)(a:Spear Q A)(b:Spear Q B): Spear Q (reforge S A B):= by
 let H:=cutM S; let V:=1-H; have he:Commute V Q:= (Commute.one_left _).sub_left h; have hw:Commute V (1-Q):= (Commute.one_right _).sub_right he; let Y:=A-B; have hp:Q*Y=Y:= by unfold Y; rw [mul_sub,a.up,b.up]; -- tune
 have hy:Y*(1-Q)=Y:=by unfold Y; rw [sub_mul,a.low,b.low]
 constructor
 · change Q*(B+V*Y*V)=B+_; rw [mul_add,b.up,←mul_assoc Q _ V,←mul_assoc Q,←he.eq,mul_assoc V Q Y,hp]
 change (B+V*Y*V)*(1-Q)=B+_; rw [add_mul,b.low,mul_assoc (V*Y),hw.eq,←mul_assoc, mul_assoc V Y (1-Q),hy]
lemma discR(h:Commute (cutM S) Q)(a:A*(1-Q)=1-Q)(b:B*(1-Q)=1-Q): reforge S A B * (1-Q)=1-Q:=by
 let H:=cutM S; let V:=1-H; have he:Commute V Q:= (Commute.one_left _).sub_left h; have hw:Commute V (1-Q):= (Commute.one_right _).sub_right he
 change (B+V*(A-B)*V)*(1-Q)=_; rw [add_mul,b,mul_assoc (V*(A-B)),hw.eq,←mul_assoc,mul_assoc V (A-B) (1-Q),sub_mul A B,a,b,sub_self,mul_zero,zero_mul,add_zero]
lemma band_op (G:Op n): ‖(1-cutM S)*G*(1-cutM S)‖≤‖G‖:=by
 let V:=1-cutM S; have hv:IsStarProjection V:=(cutM_idp S).one_sub; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (hv.norm_le _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (hv.norm_le _))))
lemma cost (h:‖A‖≤a)(p:‖B‖≤b): ‖reforge S A B‖≤b+(a+b):=(norm_add_le ..).trans (add_le_add p ((band_op _).trans ((norm_sub_le ..).trans (add_le_add h p))))
lemma cellM(S:Finset n)(A B:Op n)(i:n): cellZ (reforge S A B) i ≤ cellZ B i +(cellZ A i+cellZ B i):=by
 let V:=1-cutM S; let T:= A-B; unfold reforge; apply (cellZ_add ..).trans; refine add_le_add le_rfl ?_
 change cellZ (V*T*V) i ≤ _; apply le_trans (b:=cellZ T i) ?_ (cellZ_sub _ _ _); unfold cellZ V; rw [act_mul,act_sub,act_one,cut_basis]; by_cases t:i∈S
 · rw [if_pos t,sub_self,map_zero,norm_zero]; exact norm_nonneg _
 rw [if_neg t, sub_zero]; exact (cellZ_mul ..).trans (mul_le_of_le_one_left (cellZ_nn ..) ((cutM_idp S).one_sub.norm_le _))
lemma docket (h:cellU S (B-A) a)(p:cellU S (star (B-A)) a): Priced (reforge S A B-A) ((a* S.card)*2) ((a^2*S.card)*4):=by
 let K:=cutM S; let D:=B-A; have he:=Priced.curtain h; have ht:star (star D*K)=K*D:=by rw [star_mul,star_star,show star K=K from (cutM_idp _).2]
 have hx:Priced (K*D) (a*S.card) (a^2*S.card):= ht ▸ (Priced.curtain p).starP -- type?
 have hy:=he.plusP (hx.rP (show ‖1-K‖≤1 from (cutM_idp _).one_sub.norm_le _)); rw [subA]; exact hy.monotoneP (by exact le_of_eq (by ring)) (by exact le_of_eq (by ring))
lemma dockets(h:0≤a)(p:a≤1)(u:cellU S (B-A) a)(v:cellU S (star (B-A)) a): Priced (reforge S A B-A) (a*S.card*2) (a*S.card*4):= (docket u v).monotoneP le_rfl (by gcongr; nlinarith only [h,p])
end reforge
-- issue.P
variable [Nonempty n]
lemma Pall_feeP(h:Priced (A-M) a b)(p:Priced (B-N) c d)(u:‖M*P‖ ≤ t)(x:IsStarProjection P)(r:‖B‖≤ s) : Priced ((Pall A B - Pall M N)*P) (a*(1+s)+c*t) (2*(b*(1+s)^2+d*t^2)) := by
 rw [show (Pall A B-Pall M N)*P = (1-star B)*((A-M)*P)-star (B-N)*(M*P) from by unfold Pall; rw [star_sub]; noncomm_ring]
 have he:= ((h.rP (x.norm_le _)).lP (show ‖1-star B‖ ≤ 1+s from (norm_sub_le ..).trans (by rw [norm_star,norm_one]; exact add_le_add le_rfl r))).subP (p.starP.rP u); simpa only [mul_one,one_pow] using he
/- purchase at the following intrinsic price: a,t ∼ column accuracy chosen, b huge budget.Can overrequest different $nu*size$ purchase for L & Z. -/
variable {X R:Op n}
abbrev CFolio (a:ℝ)(S:Finset n):= a * S.card
/-- Plan is prepaid on $(Q,P,μ)$: $p,s$ are fine tolerances on columns relative to true μ cost;
 M,N approximants used; OpmL cost u; ℱcost c; $g$ smooth cert via $L_{coarse}$;
 Only opportunistically used on footprint S,T. -/
structure Currency (Q P:Op n)(μ p s u c:ℝ)(M N:Op n):Prop where
 topE:IsStarProjection Q
 topP:IsStarProjection P
 tLive : lit (Rheims.frost Q P μ)
 pace: 0≤μ
 roof: μ≤1
 trueL: ‖Lumi Q P μ‖ ≤ u
 trueC: cellU univ (Lumi Q P μ) c
 capM: ‖M‖≤u
 tinyA: 0≤p
 baseA: p≤1
 tinyB: 0≤ s
 baseB: s≤1
 mself : IsSelfAdjoint M
 mlower : M*(1-Q)=1-Q
 mQ: cellU univ (M-Lumi Q P μ) p
 nQ:Spear Q N
 zNum : ‖N‖ ≤ 2
 zCol : cellU univ (N-Zami Q P μ) s
 zRow : cellU univ (star (N-Zami Q P μ)) s
 guide: ∃ K:Op n, IsSelfAdjoint K ∧ K≤Lumi Q P μ ∧ Canon n (1/2)≤K ∧ ‖M-K‖≤1/8
namespace Currency
variable (h: Currency Q P k p s u c M N) {g:ℝ}
local notation "L₀"=> Lumi Q P k
local notation "Z₀"=> Zami Q P k
abbrev stageL(S:Finset n)(Q P:Op n)(μ:ℝ)(M:Op n):= reforge S (Lumi Q P μ) M
abbrev stageZ(S:Finset n)(Q P:Op n)(μ:ℝ)(M:Op n):= reforge S (Zami Q P μ) M
local notation "A_"=> stageL S Q P k M
local notation "Z_"=> stageZ T Q P k N
include h
lemma buildL_ticket : Canon n (1/4) ≤ stageL S Q P k M:=by obtain ⟨O,u,v,t,p⟩:=h.guide; exact reforge.fixH (sub_nonneg.mpr v) t p h.mself u
lemma buildL (p':Commute (cutM S) Q): Milieu Q (stageL S Q P k M):=⟨lit_of_fee (by norm_num) h.buildL_ticket, reforge.discR p' (pole h.topE h.tLive).lowerV h.mlower⟩
lemma buildZ(p':Commute (cutM T) Q): Spear Q (stageZ T Q P k N):= reforge.discS p' h.topE (heart h.topE h.tLive) h.nQ
lemma zNormL : ‖stageZ T Q P k N‖ ≤ 5 := (reforge.cost (revenueZZ h.topE h.tLive h.pace) h.zNum).trans_eq (by norm_num)
lemma lNormL : ‖stageL S Q P k M‖ ≤ 3*u:= (reforge.cost h.trueL h.capM).trans_eq (by ring)
lemma fee_turn: ‖1-star (stageZ T Q P k N)‖ ≤ 6:= (norm_sub_le ..).trans (by rw [norm_star,norm_one]; exact (add_le_add le_rfl h.zNormL).trans_eq (by norm_num)) -- nonempty
lemma fNormL : ‖Pall (stageL S Q P k M) (stageZ T Q P k N)‖ ≤18*u:= (norm_mul_le ..).trans ((mul_le_mul h.fee_turn h.lNormL (norm_nonneg _) (by norm_num)).trans_eq (by ring))
lemma cellC(i:n) : cellZ (stageL S Q P k M) i ≤ 3*c+2:=by
 have hx :cellZ M i≤ 1+c:=by nth_rw 1 [← sub_add_cancel M L₀]; exact (cellZ_add ..).trans (add_le_add ((h.mQ i (mem_univ i)).trans h.baseA) (h.trueC i (mem_univ i)))
 exact (reforge.cellM ..).trans ((add_le_add hx (add_le_add (h.trueC i (mem_univ i)) hx)).trans_eq (by ring))
lemma openingL : Priced (stageL S Q P k M - L₀) (CFolio p S*2) (CFolio p S*4):=by
 let V:= M-L₀; have H:IsSelfAdjoint V:= h.mself.sub (pole h.topE h.tLive).litA.isSelfAdjoint; have he:= cellU.trim h.mQ (subset_univ S); exact reforge.dockets h.tinyA h.baseA he (H.star_eq.symm ▸ he) -- ▸?
lemma openingZ : Priced (stageZ T Q P k N - Z₀) (CFolio s T*2) (CFolio s T*4):= reforge.dockets h.tinyB h.baseB (cellU.trim h.zCol (subset_univ _)) (cellU.trim h.zRow (subset_univ _))
abbrev GoalP(x:ℝ):= 300*x
local notation "Ξ"=> CFolio p S + CFolio s T  -- notation might parse wrong, add parentheses later
lemma cost_ready : Priced ((Pall (stageL S Q P k M) (stageZ T Q P k N) - Pall L₀ Z₀)*P) (GoalP (CFolio p S + CFolio s T)) (330*(CFolio p S + CFolio s T)):=by
 let a:= CFolio p S; let b:= CFolio s T; have hx:0≤a:=mul_nonneg h.tinyA (Nat.cast_nonneg _); have hy:0≤b:=mul_nonneg h.tinyB (Nat.cast_nonneg _); apply (Pall_feeP h.openingL h.openingZ (costLP h.topE h.topP h.tLive h.pace) h.topP h.zNormL).monotoneP; · change a*2*(1+5)+b*2*2 ≤ 300*(a+b); linarith only [hx,hy]
 change 2*(a*4*(1+5)^2+b*4*2^2)≤330*(a+b); nlinarith only [hx,hy]
lemma zRue (u: Commute (cutM S) Q) : -rueD (stageL S Q P k M) ≤ -rueD L₀ + CFolio p S*8:=by
 let L:=stageL S Q P k M; let a:=CFolio p S; have b:lit L:=(h.buildL u).litA; have hh:‖L⁻¹‖≤4:= (inv_power b (by norm_num) h.buildL_ticket).trans_eq (by norm_num)
 have hy : Trunk (L₀-L) (a*2):=by have hz:=Trunk.neg (h.openingL (S:=S)).nu; rw [neg_sub] at hz; exact hz -- tune precedence
 have hx:=rue_fix (pole h.topE h.tLive).litA b hh hy; change -rueD L≤ _+a*8; linarith
end Currency
end Dijon
end YM.CF.Fock.Reduction
