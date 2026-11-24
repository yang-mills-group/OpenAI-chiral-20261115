import YM.CF.Tale.Hand
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Tale
set_option quotPrecheck false
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
-- Transverse linear gauge moment, transported spot. canonical blocks only. no t-period interpolation
variable (k:ℝ)(j t:ℕ)(h:0<k)(p:4≤j)(v:4≤t)(P:Flight j t)
variable {f c:Side}(w:f.val=c.val *P.L.val)(o:Site f)(d b a:Axis)(i:TypeFace 1)
open MultiNext.SignedSource
local notation "Z"=> Exterior.coord d
local notation "L"=> P.L
local notation "G"=> deckY j t P w
local notation "R"=> Lt k j t P
local notation "T"=> advanceC L R [a]
local notation "y"=> (deckY j t P w).residue o
local notation "U"=> T (y,i) Z
open Next.SectorChange Pressure Tube
open MultiNext.SignedSource.Newt
local notation "D2"=>SU.group.Color
local notation "B_"=> Body 1 c
abbrev stem (cS:Side)(x: Cover)(l:Site cS):= l+wrap cS x
abbrev nickV (tV:SU.group.Color)(x: Cover)(s z:Axis)(b:TypeFace 1):SU.group.Color:= if b=Exterior.coord s then (x z:ℝ) • tV else 0
local notation "U'"=> ((G).parent o)
variable {C A R' a':ℝ}{m N:ℕ}(D: Co c (TypeFace 1) → SU.group.Color)(u:SU.group.Color)
omit a d b w p v h P i k j t o in
private lemma lend_G {E:Type*}[NormedAddCommGroup E][CompleteSpace E][NormedSpace ℝ E] {A F:Cover→E}{B:Cover→ℝ}{a M C:ℝ}(n:ℕ)(hp:∀ x:Cover,Laurent.size x≤n→ A x= F x)(h: Width a C B)(hF:Summable (fun x=>B x•F x))(t:∀ x,‖A x-F x‖≤ M*Real.exp ((a/2)*Laurent.size x))(p:0 ≤ M)(v:0 ≤ a) : Summable (fun x=> B x•A x) ∧ ‖(∑' x:Cover,B x•A x)-(∑' x:Cover,B x•F x)‖≤ Real.exp (-(a/2)*n)*M*C:=by
 let K:=Real.exp (-(a/2)*n)*M; let H'(x: Cover):= K*(Real.exp (a*Laurent.size x)*‖B x‖); have ht:Summable H':=h.2.1.mul_left _
 let X(x:Cover):=B x • (A x-F x); have he(x): ‖X x‖≤ H' x:=by
    unfold X H'; by_cases k: Laurent.size x≤n; rw [hp x k,sub_self,smul_zero,norm_zero]; unfold K; positivity
    rw [norm_smul]; unfold K; refine (mul_le_mul_of_nonneg_left (t x) (norm_nonneg _)).trans ?_; rw [show _ * (Real.exp _* ‖B x‖) = _ from (show Real.exp (-(a/2)*n)*M*(Real.exp (a*Laurent.size x)*‖B x‖)=‖B x‖*(M*(Real.exp (-(a/2)*n)*Real.exp (a* Laurent.size x))) by ring), ←Real.exp_add]; gcongr ‖B x‖*(M*Real.exp ?_ ); have hu:(n:ℝ) ≤ Laurent.size x:=Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge k)); nlinarith only [mul_le_mul_of_nonneg_left hu v] -- tune h bind k nested
 have hs : Summable (fun x=>‖X x‖):=ht.of_nonneg_of_le (fun x=>norm_nonneg _) he; have hp(z): B z • A z= X z+B z • F z:=by unfold X; rw [smul_sub,sub_add_cancel]
 constructor; · simp_rw [hp]; exact hs.of_norm.add hF
 simp_rw [hp]; rw [hs.of_norm.tsum_add hF,add_sub_cancel_right]; apply (norm_tsum_le_tsum_norm hs).trans; apply (hs.tsum_le_tsum he ht).trans; unfold H'; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (by unfold K; positivity)
include h p v w
lemma pipe_u (hx:b≠d)(hz: Row.strip T a' C)(hq:0 < a') (K:ℝ)(hp:0 ≤ K)(D': ∀ x:Cover,Laurent.size x≤ m→∀ i:TypeFace 1,D (stem c x U',i)= nickV u x d b i)(wz: ∀ x:Cover,∀ i:TypeFace 1, ‖D (stem c x U',i)- nickV u x d b i‖≤ K*Real.exp ((a'/2)* Laurent.size x)) : ‖MultiNext.SignedSource.Newt.load (installed G T) D (o,i) - modeT P.L a b i (Exterior.coord d) • u‖≤ Fintype.card (TypeFace 1) * (Real.exp (-(a'/2)*m)* K*C) :=by
 obtain ⟨i',he⟩:= vow_Q k j t h p v P w o d b a i (Ne.symm hx) -- d b ordering
 let F(q:TypeFace 1)(x:Cover):SU.group.Color:= nickV u x d b q; let B(q:TypeFace 1)(x:Cover):= T (y,i) q x -- notation S
 let B'(q:TypeFace 1):= ∑' x:Cover, B q x • F q x
 have hQ(q:TypeFace 1):Summable (fun x:Cover=>B q x • F q x) ∧ B' q=(if q=Z then modeT L a b i Z • u else 0):=by
    by_cases g:q=Z; swap; · simp only [g,B',F,nickV,if_false,smul_zero,tsum_zero,and_true]; exact summable_zero
    unfold B'; subst q; have hp(x:Cover): B Z x • F Z x= ((x b:ℝ) * U x) • u:=by unfold F; rw [nickV,if_pos rfl,smul_smul]; exact congrArg (fun r:ℝ=>r • u) (mul_comm ..)
    simp_rw [hp]; refine ⟨i'.smul_const _,?_⟩; rw [i'.tsum_smul_const,he,if_true]
 rw [MultiNext.SignedSource.Newt.tally (g:=G) (advanceC L R [a]) D hz hq, ← show (∑ j:TypeFace 1, B' j)=modeT L a b i Z • u from ?_, ←sum_sub_distrib]; swap; · simp [(hQ _).2] -- tune
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> Real.exp (-(a'/2)*m)* K*C) ?_).trans_eq (by simp)); intro i _; apply (lend_G m (fun x h=> D' x h i) (hz _ i) (hQ i).1 (fun x=>wz x i) hp hq.le).2 -- infer D
end YM.CF.Tale
