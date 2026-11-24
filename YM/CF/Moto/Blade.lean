import YM.CF.Moto.Road
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Moto
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Hove Haro
variable {n:Side}(o x y:Site n)(a b:Pal)(S T:Matrix (Single n) Kt ℂ)(P:Op (Single n))(k:ℕ)(gT:SU.E)(r:Bool)(i:Axis)
local notation "L"=> seed_k x y a
variable (h:ℕ)
local notation "V"=> bud_k o x y a
abbrev zone0(x:Site n)(u:ℕ):ℝ:= (1+(2:ℝ)*(u:ℝ))^k
lemma nit(x:Site n)(p:Kt)(hq:separation o x≤h):nook_T o k (hailV x p)≤zone0 k x h:=by -- binder tune
 unfold nook_T; rw [show (hailV x p).1.1=x from rfl,ζdist]; unfold zone0; push_cast; gcongr
abbrev chal (k h:ℕ)(c:ℝ):= (Fintype.card Kt:ℝ)^2*(2*((1+(2:ℝ)*(h:ℝ))^k)*c)
lemma fareL(hq:separation o x ≤ h)(hp:separation o y≤h)(d:ℝ)(p:‖a‖≤ d): paid_M o L k≤ chal k h d:=by
 let N:=Single n; let t:=nook_T o k; let H(i j:Single n) := (coyF t (i,j))*‖L i j‖
 have hc(f:Single n→ℝ):∑ i:N,f i=∑ i:Site n,∑ j:Kt,f (hailV i j):=by rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rfl -- tune
 unfold paid_M paidX; rw [Fintype.sum_prod_type,hc]; change (∑ x':Site n,∑ b:Kt, ∑ i':N,H (hailV x' b) i') ≤_; simp_rw [hc]; rw [sum_eq_single x]; swap
 · intro b _ u; refine sum_eq_zero fun j _=>sum_eq_zero fun i _=>sum_eq_zero fun l _=>?_ ; unfold H seed_k; simp [hailV,Ne.symm u]
 swap
 · simp
 let Z:=zone0 k x h; let B:=2*Z*d; refine (sum_le_sum (g:=fun _=>∑ i:Kt, B) ?_).trans ?_; swap
 · refine le_of_eq ?_; simp [chal,B,Z,zone0,nsmul_eq_mul]; ring -- pow typo
 intro i _; rw [sum_eq_single y]; swap
 · intro b _ u; apply sum_eq_zero; intro j _; unfold H seed_k; simp [hailV,Ne.symm u]
 swap
 · simp
 apply sum_le_sum; intro j _; unfold H; refine mul_le_mul ?_ ((le_of_eq (congr_arg norm ?_)).trans ((norm_entry a i j).trans p)) (norm_nonneg _) ?_ -- infer B reduce
 · unfold coyF; refine (add_le_add (nit o k h x i hq) (nit o k h y j hp)).trans_eq ?_; unfold Z zone0; ring -- args order
 · exact if_pos (And.intro rfl rfl)
 unfold Z zone0; positivity
lemma gone_l (v w:Single n)(p:bud_k o x y a v w ≠0): x=v.1.1∧ y=w.1.1:=by by_contra h; exact p (if_neg h)
def Fit (c:ℝ)(P:Op (Single n)):Prop:=(paid_M o P k ≤ c ∧ MarkPH P ∧ ∀ i j:Single n,P i j≠0→separation o i.1.1≤h∧ separation o j.1.1 ≤ h)
lemma fame(hq:separation o x ≤ h)(hp:separation o y≤ h)(d:ℝ)(p:‖a‖≤ d)(z:∀ g:SU.E, Commute a (KinX g)): Fit o k h (chal k h d) V:=by
 refine ⟨fareL o x y _ k h hq hp d (Eq.trans_le ?_ p),fun g u w=>?_ ,fun i j K=>⟨(gone_l _ _ _ _ _ _ K).1 ▸ hq,(gone_l _ _ _ _ _ _ K).2 ▸ hp⟩⟩
 · simp only [norm_smul,show ∀ x:Site n,‖rain_U o x‖=1 from fun _=>fee_norm _,one_mul] -- notation
 unfold bud_k; rw [star_P]; split; exact sc_m _ _ _ (sc_m _ _ _ (z g)); exact Commute.zero_left _
variable {d e:ℝ}{U:Op (Single n)}
lemma plus_R(p:Fit o k h d P)(u:Fit o k h e U) : Fit o k h (d+e) (P+U):=by
 refine ⟨(paidp_sum ..).trans (add_le_add p.1 u.1),fun g x y=>?_ ,fun i j t=>?_⟩
 · change Commute (matPH (P+U) _ _) _; rw [show matPH (P+U) x y=matPH P x y+matPH U x y from rfl]; exact (p.2.1 ..).add_left (u.2.1 ..)
 by_cases hx:P i j≠0; · exact p.2.2 _ _ hx
 exact u.2.2 _ _ fun v=>t (by rw [Matrix.add_apply,not_ne_iff.mp hx,v,zero_add])
lemma sub_R(p:Fit o k h d P)(u:Fit o k h e U): Fit o k h (d+e) (P-U):=by
 rw [sub_eq_add_neg]; refine plus_R _ _ _ _ p ⟨?_,fun g x y=>?_ ,fun i j p=> u.2.2 _ _ fun g=>p (by rw [Matrix.neg_apply,g,neg_zero])⟩
 · unfold paid_M; rw [show pinF (-U)=-pinF U from rfl,p_negative]; exact u.1
 rw [show matPH (-U) x y= -matPH U x y from rfl]; exact (u.2.1 ..).neg_left
lemma fitZ : Fit o k h 0 0:=by
 refine ⟨by unfold paid_M; rw [show pinF (0:Op (Single n))=0 from rfl]; simp [paidX],fun _ _ _=>?_,fun i j t=>False.elim (t rfl)⟩; exact Commute.zero_left _
lemma fitS{ι:Type*}[DecidableEq ι](S:Finset ι)(F:ι→Op (Single n))(z:ι→ℝ)(hX:∀ i∈S,Fit o k h (z i) (F i)): Fit o k h (∑ i∈S,z i) (∑ i∈S,F i):=by
 induction S using Finset.induction with
 | empty=> simp only [Finset.sum_empty]; exact fitZ ..
 | insert i s t u=>rw [sum_insert t,sum_insert t]; exact plus_R _ _ _ _ (hX i (mem_insert_self _ _)) (u (fun i p=> hX i (mem_insert_of_mem p))) -- tune
variable(Ψ:Dome)
abbrev chipZ(k:ℕ)(A:ℝ):= 17*chal k 1 A
lemma beam_l (p:Noble Ψ) : Fit o k 1 (chipZ k ‖Ψ‖) (spring_V Ψ o):=by
 let R:=bud_k o; let A:= chal k 1 ‖Ψ‖
 have hk(i:Axis): separation o (o+step i) ≤1:=UVNext.PricedKernels.oneStep_le o (posDir i)
 have hr:separation o o ≤ 1:=by simp
 have h₁:= fame o o o _ k 1 hr hr ‖Ψ‖ (show ‖Ψ.1‖≤‖Ψ‖ from norm_fst_le Ψ) (fun i=>(p.2 i).1); let G(i:Axis):=o+step i
 have hp(i:Axis):‖Ψ.2.1 i‖≤‖Ψ‖:=(norm_le_pi_norm _ _).trans ((norm_fst_le _).trans (norm_snd_le _))
 have hP(i:Axis):‖Ψ.2.2 i‖≤‖Ψ‖:=(norm_le_pi_norm _ _).trans ((norm_snd_le _).trans (norm_snd_le _))
 have he:=fitS o k 1 univ _ (fun _:Axis=> A+A+(A+A)) (fun i _=> plus_R o _ k 1 (sub_R o _ k 1 (fame o (G i) o _ k 1 (hk _) hr _ (hp i) (fun g=>(p.2 g).2.1 i)) (fame o o o _ k 1 hr hr _ (hp i) (fun g=>(p.2 g).2.1 i))) (sub_R o _ k 1 (fame o o (G i) _ k 1 hr (hk _) _ (hP i) (fun g=>(p.2 g).2.2 i)) (fame o o o _ k 1 hr hr _ (hP i) (fun g=>(p.2 g).2.2 i)))) -- tune
 rw [show chipZ k ‖Ψ‖=A+(∑ i:Axis,(A+A+(A+A))) from (by simp [chipZ,Axis]; unfold A; ring)]
 exact plus_R _ _ k 1 h₁ he
end YM.CF.Moto
