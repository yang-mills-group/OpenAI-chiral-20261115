import YM.CF.DPress.Analytic.Heed
import YM.CF.DPress.Analytic.Logs
import YM.CF.DPress.Fees.Hearth
import YM.CF.Pso.Fume
/-!
 eq:diffd and E_b estimate.input wisp not rotation.Generator H.%.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.Hues
open Function Filter Metric Lattice Cube RG MeasureTheory Finset Pastry Fock Lat Spire Skye Scree
open Vow Ione Larch Bake Lilt Hake Wray Push.AbsoluteSums Trees
open Fees Fees.Moral Fees.Rails Analytic Mew -- conflict CapF
open scoped Topology Classical ComplexConjugate BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{a b c δ h x y:ℝ} (F G : ℂ→ Pax n)(V:Orbit n)
-- reBook. Wisp across line. No continuity in z on splits.
section Repr
variable (L:∀ z,Wisp P (F z) (G z) h a b c)(Y: 1≤h)(H:x>1)(u:V.1=1)
abbrev jet (P:BudgetPoint)(x:ℂ) (i:Aura n):ℂ:= chipV ∅ (FeeD P (F x) i V - G x i V)
abbrev poleν (P:BudgetPoint) (x:ℂ) (i:Aura n):= zenS P i.val ∅ ((FeeD P (F x) i-G x i)-jet F G V P x i • (1:Copy n))
private lemma honor {L:Aura n→ℝ}{K:Aura n→ℝ}(v:L≤K)(c:ℝ)(P:BudgetPoint)(i:Seat n): tallB L P.B c i≤ tallB K P.B c i:=sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (v j) (Real.exp_pos _).le
include u
private lemma vbright(i:Aura n): pingS P.threshold (i.val\∅) V.1:=by rw [u,sdiff_empty]; exact ping_f P _
omit u
private lemma moneyV(z:ℂ): (chipV (n:=n) ∅) (z • (1:Cipher n))=z:=by rw [map_smul]; simp [Mew.chipV, crumb]
private lemma esteem (z:ℂ)(T S:Support (More n)): Medal P T S (z • (1:Copy n)) h ‖z‖:=by simpa only [mul_one] using num_h h P T S Medal.oneT z
include L u Y
lemma proofE (z:ℂ) : PactF P (P.supportExponent+1+1) h (poleν F G V P z) (2*c) ∧ ∀ x:Seat n,tallB (fun i=>|(jet F G V P z i).im|) P.B (P.supportExponent+1+1) x ≤ c:=by
 obtain ⟨K,Q,F₀,F₁,A,h,x,l,v,q,g,b,f,f'⟩:= (L z).keep; let τ:=P.supportExponent+1+1 -- duplicate? h x names shadow
 choose a₀ y using h; -- tune GrainP.eq; convert aR.real linear
 have hv(i:Aura n): K i= (a₀ i:ℂ) • (1:Copy n):=by rw [y]; funext x; rw [thim,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
 let a(i:Aura n):= jet F G V P z i-(a₀ i:ℂ); have hp(i)(p:Orbit n)(v:visible P i.val ∅ p.1): FeeD P (F z) i p-G z i p=K i p+ Q i p:=by rw [f i p v]; abel -- last projection f or split check
 have ht(i): a i=chipV ∅ (Q i V):=by unfold a jet; rw [hp i V (hates (vbright V u i)), map_add,hv, Pi.smul_apply, Pi.one_apply,moneyV]; ring
 have he(i):‖a i‖≤ F₁ i:=by rw [ht]; refine (YM.CF.norm_entry _ _ _).trans ((q i).capF Y V (vbright V u i)) -- tune shape
 refine ⟨⟨F₁+F₁,fun i=>?_,fun i=> le_trans ?_ (show c+c≤_ from le_of_eq (by ring))⟩,fun x=> le_trans (honor (fun i=>?_ ) _ P x) (b x)⟩
 · have hz : poleν F G V P z i= zenS P i.val ∅ (Q i - a i • (1:Copy n)):=by funext x; unfold poleν zenS; split; rename_i w; simp only [Pi.sub_apply,hp i x w,hv, a,sub_smul,Pi.smul_apply]; abel; rfl
   rw [hz]; exact zen_B P ((capM P _ _ _ Y).sub (q i) ((esteem (a i) i.val ∅).big (he i)))
 · rw [tall_add]; exact add_le_add (b _) (b _)
 change |(jet F G V P z _).im|≤ _; rw [show (jet F G V P z i).im= (a i).im by simp [a]]; exact (Complex.abs_im_le_norm _).trans (he _)
omit u Y L
abbrev Prosper (x:ℝ)(F:ℂ → Pax n):=∀ i:Aura n,∀ V:Orbit n,DifferentiableOn ℂ (fun z=>F z i V) (ank x)
def ξPaid(P: BudgetPoint)(θ:ℝ)(D:Aura n→ℝ)(c:ℝ):Prop:=∀ x:Seat n,tallB (fun i=>|D i|) P.B θ x ≤ c
-- use same names as text. diff log. no orbit cut
variable (p:Prosper x F) (q:Prosper x G)
local notation "Mh"=> (P.supportExponent+1+1)
local notation "wkT"=> jet F G V P
include L p Y
lemma pleasing : Prosper x (fun z=> FeeD P (F z)):=by
 choose Kx R Ll Z Y_ k l f g h i b Q Q' using fun z=>(L z).keep; exact fun i x=> glowing _ Metric.isOpen_ball F i x Y_ l (by linarith [P.exponent_pos]) Y f p -- tune
include q
lemma jet_v(i:Aura n):DifferentiableOn ℂ (fun z=> jet F G V P z i) (ank x):= (chipV (n:=n) ∅).differentiable.comp_differentiableOn (((pleasing F G L Y p) i V).sub (q i V))
include u H
lemma totalJet : ∀ i:Seat n,tallB (fun i' => ‖jet F G V P 1 i'-jet F G V P 0 i'‖) P.B (P.supportExponent+1+1) i ≤ 2*c/(x-1):=by
 intro i; let S:=univ.filter fun j:Aura n=>i ∈ j.val; have he(z)(a:z∈ank x): (∑ j∈S,currency P.B (Mh) j.val *|(jet F G V P z j).im|) ≤ c:= (by simp_rw [mul_comm _ (abs _)]; exact (proofE F G V L Y u z).2 i); unfold tallB; simp_rw [mul_comm _ (currency ..)]; exact Analytic.stageD S (fun i z=>jet F G V P z i) (fun i _=> jet_v F G V L Y p q i) _ (fun i _=>Fees.Rosy.ccur ..) he H -- tune Mh parent capture sub
omit u H q L p Y in
private lemma matDue {a b: Aura n→ℂ}(i:Aura n): |Mat_R (fun i=>(a i).re) i-Mat_R (fun i=>(b i).re) i| ≤ Mat_R (fun i=>‖a i-b i‖) i:=by
 unfold Mat_R; simp only [Pi.smul_apply,Finset.sum_apply,zeal_F,Function.comp_apply, smul_eq_mul]; rw [← mul_sub, abs_mul,abs_of_nonneg (envy n).le,← sum_sub_distrib]; refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum (?_ ))) (envy n).le; intro s _; exact Complex.abs_re_le_norm (a (moldA s i)-b (moldA s i)) -- tune namespace
local notation "D_"=> fun z=>curr_r P (G z) (F z) V -- notation tune
lemma diff_w(i:Seat n): tallB (fun j=>|(curr_r P (G 1) (F 1) V-curr_r P (G 0) (F 0) V) j|) P.B (P.supportExponent+1+1) i≤2*c/(x-1):= honor (P:=P) (L:=fun j:Aura n=> |((D_) 1-(D_) 0) j|) (fun i=> matDue (a:= wkT 1) (b:=wkT 0) i) _ i |>.trans (labourV _ _ _ (totalJet F G V L Y H u p q) i)
-- regular correction Δ.H. real.
abbrev shiftD (P: BudgetPoint)(z:ℂ): Pax n := fun i=> zenS P i.val ∅ ((jet F G V P z i-(↑(curr_r P (G z) (F z) V i):ℂ)) • (1:Copy n))
omit L Y H u p q in
lemma shifts (z:ℂ) : curr_X P (G z) (F z) V=poleν F G V P z+shiftD F G V P z:=by
 funext i x; unfold curr_X; change zenS P i.val ∅ _ _=zenS P i.val ∅ _ _+zenS P i.val ∅ _ _; unfold zenS; split; next p=> unfold cashV; simp only [Pi.sub_apply,sub_smul,Pi.smul_apply,Pi.one_apply,Lilt.thim, RCLike.real_smul_eq_coe_smul (K:=ℂ)]; abel -- tune ℂsmul
 next p=> simp
lemma payout : PactF P (P.supportExponent+1+1) h (curr_X P (G 1) (F 1) V - curr_X P (G 0) (F 0) V) (6*(c/(x-1))):=by
 let t(z):= poleν F G V P z; let K':=6*(c/(x-1)); let h':=2*c/(x-1); have h₁ : PactF P (P.supportExponent+1+1) h (t 1-t 0) h':= wage_c P h (P.supportExponent+1+1) (by linarith [P.exponent_pos]) Y t (fun i _=>(proofE F G V L Y u i).1) (fun i v g=> ?_) H -- tune `.h shadow`
 swap
 · unfold t poleν zenS; dsimp only; split; next p'=> exact DifferentiableOn.sub (f:=fun z=> FeeD P (F z) i v-G z i v) (((pleasing F G L Y p) i v).sub (q i v)) ((jet_v F G V L Y p q i).smul (differentiableOn_const 1)) -- tune
   next p'=> exact differentiableOn_const _
 let φ:= (wkT 1)-(wkT 0); let Q':= (curr_r P (G 1) (F 1) V)-(curr_r P (G 0) (F 0) V); let S: Aura n→ℝ:= (fun i=>‖φ i‖); let R: Aura n → ℝ:= (fun i=> |Q' i|); let V':= shiftD F G V P; have he:PactF P (P.supportExponent+1+1) h (V' 1-V' 0) (h'+h'):=by
    refine ⟨S+R,fun i=>?_,fun i=> by rw [tall_add]; exact add_le_add (totalJet F G V L Y H u p q i) (diff_w F G V L Y H u p q i)⟩
    let T (i:Aura n):=φ i- (↑(Q' i):ℂ); have hp(i): ‖T i‖≤ (S+R) i:=by unfold T; rw [Pi.add_apply]; exact (norm_sub_le ..).trans_eq (by rw [Complex.norm_real]; rfl)
    have ht:(V' 1-V' 0) i=zenS P i.val ∅ (T i • (1:Copy n)):=by
       funext j; unfold V' shiftD; simp only [Pi.sub_apply]; unfold zenS; split; next t=> unfold T φ Q'; simp only [Pi.sub_apply,Complex.ofReal_sub,sub_smul,Pi.smul_apply]; abel
       next t=>simp
    change Medal P i.val ∅ _ _ _; rw [ht]; exact zen_B P ((esteem (T i) i.val ∅).big (hp i))
 rw [shifts F G V 1, shifts F G V 0, add_sub_add_comm]; exact (fortune (n:=n) P h (P.supportExponent+1+1) Y).toReceipt.relax ((fortune (n:=n) P h (P.supportExponent+1+1) Y).add h₁ he) (Eq.le (by unfold h'; ring)) -- tune
end Repr
end YM.CF.DPress.Hues
