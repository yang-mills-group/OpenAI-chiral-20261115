import GaugeFieldConstruction.Hardrock
set_option autoImplicit false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Fock.Flux
open Finset Function Filter Lattice NormedSpace Set TopologicalSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I] {P E A B: Op I}
variable {J:Type*} [DecidableEq J]{x y:ℝ}
private abbrev zeroR {I:Type*}[LinearOrder I][Fintype I] (z c:ℂ)(A: FC I) := z • (A-c • 1)
private lemma commute_cen {A B:FC I}(h:Commute A B)(x y z w:ℂ):Commute (zeroR x y A) (zeroR z w B):=by apply Commute.smul_left; apply Commute.smul_right; apply Commute.sub_left _ ((Commute.one_left _).smul_left _); exact h.sub_right ((Commute.one_right _).smul_right _)
lemma scaled0 (H:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ)(z w:ℂ)(X:FC I): translateW P A B U b (zeroR z w X)=zeroR z w (translateW P A B U b X):=by unfold zeroR; rw [scale_crest,show translateW P A B U b (X-w • 1)=_ from (show _=translateW P A B U b X-translateW P A B U b (w • 1) from by unfold translateW; rw [mul_sub,sub_mul]),scale_crest, nilW H h]
lemma quo_c (v:Wave I)(p:‖v‖=1)(X:FC I)(z w:ℂ): quotation v (zeroR z w X)=z*(quotation v X-w):=by unfold zeroR; rw [quot_scale,quot_sub,quot_scale,quot_nil v p,mul_one]
lemma comm_bank (h:IsStarProjection P)(v:Valve P E A B)(S:J→ Finset I)(L:J→FC I)(C W:J→ℂ){D:ℝ}(U:UNI I)(q:List J)(p:Set.PairwiseDisjoint ↑q.toFinset S)
 {m:ℕ}(n:∀ i∈q,pressedF (S i) m D (L i)) (b:ℝ):let X(i):= zeroR (C i) (W i) (translateW P A B U b (L i)); ∀ i∈q,∀ j∈q,Commute (X i) (X j):=by
 intro X i k j u; by_cases e:i=j; · rw [e]
 apply commute_cen; unfold Commute SemiconjBy
 rw [← translate_prod v h,← translate_prod v h]
 obtain ⟨V,h,-,N⟩:=n i k; obtain ⟨A,g,-,M⟩:=n j u; rw [←N,←M]; rw [(nest_agrees h g (p (List.mem_toFinset.mpr k) (List.mem_toFinset.mpr u) e)).eq]
local notation "O"=> Set.Icc (0:ℝ) 1
variable {N:Side}
open Tulip
variable {P E A B: Op (Single N)} (U:UNI (Single N)) (C W:J→ℂ)(q:List J) {e d z v D K u:ℝ}{m:ℕ}
 (L:J→FC (Single N)) (S:J→ Finset (Single N))
variable (uP:IsStarProjection P)(t:Valve P E A B)(Ω:Wave (Single N))(hΩ:Sea P Ω)(w:q.Nodup)
variable (l:Set.PairwiseDisjoint ↑q.toFinset S)(zC:∀ i∈q, ‖C i‖≤z)(uZ:0≤z)(f:∀ i∈q,pressedF (S i) m v (L i)) (uW:∀ i∈q, ‖W i‖≤ u) (v':0 ≤ v) (u':0 ≤ u)
variable (eP:0<e)(g:0 ≤ d)(k:1 ≤ K)(kD:D≤ K)(χ:∀ b:ℝ,b∈O → PurchB d D b (oneWarp P A U b) ∧ PurchB d D b (star (onePeak P B U b)))
abbrev Crest (u v z K:ℝ)(m:ℕ):ℝ:= z*(v*K^m + u)
abbrev Tor (e d K z v:ℝ)(m:ℕ)(S:ℕ):ℝ:= (z*v* (2 * (m:ℝ)* K^m*(d*e)) +(z*(2*(d/e))*v*predrawn K m)^2)*S
local notation "c'"=> Crest u v z K m
include uP t w l zC uZ f v' g k kD χ hΩ Ω eP
abbrev stepF (T:J→FC I)(C W:J→ℂ)(i:J) := 1 + C i • (T i-W i • 1)
lemma mantle (hD:c'≤ 1/2) (uW:∀ i∈q, ‖W i‖≤u)(u':0≤u) (X:Wave (Single N)):
 let V:=translateW P A B U 0; let φ(i:J):= (C i*(quotation Ω (V (L i))- W i)).re
 ‖acts (V (rollC (stepF L C W) q)) X‖ ≤ Real.exp ((∑ i∈q.toFinset,φ i)+ Tor e d K z v m q.length + 2*c'^2*q.length)*‖acts (knight P 1) X‖:=by
 intro V φ; let Y(i):= zeroR (C i) (W i) (V (L i)); let A':=(∑ i∈q.toFinset,φ i); have hv: V (rollC (stepF L C W) q)=flowing Y q 1:=by
    have he(i:J): V (stepF L C W i)= tidef Y 1 i:= by unfold tidef; rw [one_smul,stepF,show V (1+(C i) • _) = _ from (show V (stepF L C W i)=V 1+V (zeroR _ _ (L i)) from translateW_sum ..),show V 1=1 from nilW t uP ..]; exact congrArg _ (scaled0 t uP ..)
    unfold V; rw [warp_word t uP]; unfold flowing; rw [funext he] -- warp_word transforms, then he
 have hu(k)(p:k∈O): 1-k∈ O:=by exact ⟨by linarith [p.2],by linarith [p.1]⟩
 have ht(k:ℝ)(i:J): tradeKm P Y k i=zeroR (C i) (W i) (translateW P A B U (1-k) (L i)):=by
    apply Eq.trans _ (scaled0 t uP U (1-k) (C i) (W i) (L i)); exact (show tradeKm P Y k i=knight P _* translateW P A B U 0 (zeroR _ _ (L i))*_ from by unfold tradeKm; rw [scaled0 t uP]).trans (rampW P A B (zeroR _ _ (L i)) U _).symm
 rw [hv]; apply sealed_flow uP Y q w (comm_bank uP t S L C W U q l f 0) X hD _
 · intro b p x r; let V':=translateW P A B U (1-b); let Z:=influence P A B U (1-b) e; let G(c:ℂ):= ‖c‖
   let N:= predrawn K m; have hk:0≤K:= zero_le_one.trans k; let vB:= χ _ (hu b p); let R:ℝ:=2*m*K^m*(d*e); let q':= q.toFinset
   have hL(i)(p:i∈q'): (quotation x (tradeKm P Y b i)).re ≤ φ i+z*(v*(N*Real.sqrt (Z (S i) x)+R)):=by
       have hp': i∈q:= List.mem_toFinset.mp p
       let X:= V' (L i); let T:=quotation Ω (V (L i)); let a:=quotation x X
       rw [ht b i,quo_c x r]; have hg: (C i*(a-W i)).re = φ i+(C i*(a-T)).re:=by
           unfold φ; change _=(C i* (T-W i)).re+_; rw [←Complex.add_re,show C i*(T-W i)+C i*(a-T)=C i*(a-W i) from (by ring)]
       rw [hg]; apply add_le_add_right; apply (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans; rw [norm_mul]
       have he := willow t uP hΩ r g vB.1 vB.2 k kD (f _ hp') eP
       exact mul_le_mul (zC i hp') (he.trans_eq (by unfold N R Z; ring)) (norm_nonneg _) uZ
   apply le_trans (sum_le_sum (fun i _=>hL i ‹_›))
   let a:= febrile P x; let C':= z*v*(predrawn K m)*(2*(d/e))
   have hs':(Real.sqrt ((q'.card:ℝ)))^2=(q'.card:ℝ):= Real.sq_sqrt (Nat.cast_nonneg _)
   let j(i):=Real.sqrt (Z (S i) x);
   have ht': (z*v*N) * ∑ i∈q',j i ≤ a+ C'^2*q.length:=by
       apply (mul_le_mul_of_nonneg_left (hue q' S l g uP vB.1 vB.2 x eP) (mul_nonneg (mul_nonneg uZ v') (pred_nonneg K hk m))).trans
       have he:(Real.sqrt a)^2=a:= Real.sq_sqrt (febrile_pos uP _); change z*v*N*( _*(2*(d/e))*Real.sqrt a)≤_
       rw [←List.toFinset_card_of_nodup w]; change _ ≤ a + C'^2*q'.card
       have hw:= mul_nonneg (sq_nonneg C') (Nat.cast_nonneg (α:=ℝ) q'.card); have hl:= sq_nonneg (Real.sqrt a-Real.sqrt (q'.card:ℝ)*C'); have ho:=congrArg (fun x:ℝ=>C'^2*x) hs'; unfold C' at *; unfold N; nlinarith only [he, hw,hl,ho,sq_nonneg (Real.sqrt a)] -- slack. tune timeout
   simp_rw [mul_add]; rw [sum_add_distrib, sum_add_distrib,←Finset.mul_sum, ←Finset.mul_sum, ←Finset.mul_sum,sum_const,nsmul_eq_mul]; unfold Tor; rw [show q.length=q'.card from (List.toFinset_card_of_nodup w).symm]; let T:=∑ i∈q',j i
   change A'+(z*(v*(N*T))+(q'.card:ℝ)*(z*(v*R))) ≤ a+(A'+ (z*v*R+ (z*(2*(d/e))*v*N)^2)*q'.card)
   rw [show z*(2*(d/e))*v*N= C' by unfold C' N; ring]
   rw [show q.length=q'.card from (List.toFinset_card_of_nodup w).symm] at ht'; change _* T ≤ _ at ht'; linarith only [ht']
 intro b p i w; rw [ht]; let hχ:= χ _ (hu b p); unfold zeroR; rw [norm_smul]; apply (mul_le_mul (zC i w) ?_ (norm_nonneg _) uZ)
 apply (norm_sub_le ..).trans; rw [norm_smul,norm_one,mul_one]; exact add_le_add (pulse t uP hχ.1 hχ.2 k kD (f i w)) (uW i w)
end YM.CF.Fock.Flux
end
