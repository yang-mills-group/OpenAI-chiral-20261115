import YM.CF.Continuum.Uniform
import YM.CF.Continuum.PastureCoe
import YM.CF.Continuum.Square
/-! Whole-volume and local pressure with matching factors. Here independent of
    radius except lower-pressure/admission (and tax grants). State quantifiers
    include bounds on loss parameter d; offset match for all frames within this
    economic environment. Does NOT give unbounded volume at a pivot. -/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Dial
open Graph Skye RG Laic MeasureTheory PathData Sods Precision Wilson Cascade CF.Paige Vault Nova YM.Next.Rank Emu Mint Mint.Roe
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {L' B m:Side}{j n n':ℕ}{a b c d v e k g C0 r h x y γ θ w γ' v' K V0 D C L μ σ h' :ℝ}{O:Odd L'.val}{Y:Pricing j L' O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
local notation "Λ"=> mid m B

def rateBet (V:GramM Λ) (S:Loom Λ)(P:Grasp Y B e):= ‖Complex.exp (-V.v)*partitionZ V P S‖
def TV (V:GramM Λ)(S:Loom Λ)(P:Grasp Y B e):= ∫ i:Orbit Λ, ‖recX P V S i‖ ∂city Λ
lemma price_vs(V:GramM Λ)(S:Loom Λ)(K:Integrable (denZ V P S) (city Λ)): rateBet V S P ≤ TV V S P:= by
 unfold rateBet; rw [partitionZ,←integral_const_mul]; apply le_trans (norm_integral_le_integral_norm _); have he(i:Orbit Λ):‖Complex.exp (-V.v)*beamZ Λ (denZ V P S i)‖ ≤ ‖recX P V S i‖:=by
    rw [recX,norm_smul,norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact (norm_inner_le_norm ..).trans_eq (by rw [(Dial.tickB Λ).2, one_mul]) -- infer
 exact integral_mono (((((beamL Λ).integrable_comp K).const_mul (Complex.exp (-V.v))).norm)) (K.smul (Complex.exp (-V.v))|>.norm) he
structure Tableau(m:Side)(V:GramM (mid m B))(S:Loom (mid m B))(P:Grasp Y B e)(g K:ℝ) : Prop where
 isPay : Integrable (denZ V P S) (city (mid m B))
 lowB : Real.exp (budgetCharge V g (-K)) ≤ rateBet V S P
 highB : TV V S P ≤ Real.exp (budgetCharge V g K)
lemma eqBudget(V:GramM Λ)(A B g:ℝ) : budgetCharge V g A+massMeter Λ*(B-A)=budgetCharge V g B:=by unfold budgetCharge; ring
lemma budgetLe(V:GramM Λ)(A B g:ℝ)(h:A≤B): budgetCharge V g A≤ budgetCharge V g B:= by unfold budgetCharge; gcongr

private def flagMultiplier(K C:ℝ):=4*C+3*K*2^4+180*45*6*C
private def vacuumMultiplier(b:ℝ):= b/(2*poseX)/2
-- state uniform pressure after considering budget constraints. Quantifiers are explicit to eventually project to sessions.
theorem uniform_meter(A:Pic.Span hP a b c d k r n)(S:HaarBudget group)(H:ℝ)(T:ℝ)(h0:0 ≤ T)(L A' B' C w:ℝ)(hw:0<w)(ht:0 ≤ B')(hC:0 ≤ C):∃ K:ℝ,0<K∧∀ m:Side,n ≤ (mid m B).val→∀ V:GramM (mid m B),∀ W:Loom (mid m B),Integrable (denZ V P W) (city _) → SkinT V W e →∀ v v' R q k,Ledger R v v' k C V→0≤k→1≤R→v ≤ T → v'≤ T → V.path.Bounds V.funds q B' L → ∀ g, 0<g→ g≤V.p.threshold → V.beta*g^2=1→ w≤V.funds.linear → V.funds.direct ≤ A'→ |Real.log g| ≤ massMeter (mid m B)*H→ V.beta*V.p.threshold^3≤1→ drip V P*(b/(2*poseX)/2) ≤ rateBet V W P→ Tableau m V W P g K:=by
  obtain ⟨Q,hq,U⟩:= angel_per_site A; let a:= min w 1; let X:=flagMultiplier T C
  let y:= upperMoney S B' L a H+X; let z:= lowerMoney S B' L A' H; let v0:=vacuumMultiplier b; let p:= -z +Q+|Real.log v0|
  let K:= max |p| |y| +1; have hp:0<K:=by unfold K; apply add_pos_of_nonneg_of_pos (le_max_of_le_left (abs_nonneg _)) one_pos
  refine ⟨K,hp,fun m e V W s u v v' R q' k ℓ he hu t t' Sν g b0 w b hW aH x cool dR=> ?_⟩
  let f:=massMeter (mid m B); have hc:1≤f:=money_pos _
  let l:= (mid m B).val; have hn:(l:ℝ)^4 ≤ f := by rw [show f=(l:ℝ)^4*2^4 from (matter_meter ..).symm]; exact le_mul_of_one_le_right (by positivity) (by norm_num)
  let γZ:= Graph.angle V; let σ:=budgetCharge V g; have hv0: 0<v0:=by unfold v0 vacuumMultiplier; have hp:= pose_p; have hs:=A.pos; positivity
  have hv: Real.exp (σ z) ≤ Graph.angle V:= le_trans (lowerRate S V ht b0 b x cool) (clearPaid S V Sν aH b0 w (variance_beta b0 b).le ht)
  have hi: -K ≤ -p:=neg_le_neg (by unfold K; exact (le_abs_self _).trans ((le_max_left ..).trans (le_add_of_nonneg_right (by norm_num))))
  constructor; exact s
  · apply le_trans _ dR; change Real.exp (σ (-K))≤ _*v0
    apply le_trans (b:=Real.exp (σ z)*Real.exp (-Q*f)*v0); swap
    · gcongr; unfold drip; apply mul_le_mul hv _ (Real.exp_pos _).le ((Real.exp_pos _).le.trans hv); exact le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr hq.le))) (U m e (V.J.M))
    rw [show Real.exp (σ z) * Real.exp (-Q*f) * v0=Real.exp (σ z + -Q*f + Real.log v0) by rw [Real.exp_add,Real.exp_add,Real.exp_log hv0]]; apply Real.exp_monotone; have heq:σ (-K)+f*(z+K)=σ z:=by rw [←sub_neg_eq_add z K]; exact eqBudget ..
    have hy : - f* |Real.log v0|≤Real.log v0:=by apply le_trans ?_ (neg_abs_le _); rw [neg_mul]; exact neg_le_neg (le_mul_of_one_le_left (abs_nonneg _) hc)
    have ht': f*p ≤ f*K:=mul_le_mul_of_nonneg_left (neg_le_neg_iff.mp hi) (zero_le_one.trans hc); unfold p at ht'; linarith
  have heB: a ≤ strength V.funds:=by unfold strength; apply le_min (min_le_right ..) ((min_le_left ..).trans hW)
  obtain ⟨l',z,F⟩:=u.wave; let U:= (payLedger (γ:=B') (P:=P) S V W ℓ Sν F b0 b w (A.plan _ e).1 hu he hC (s.smul (Complex.exp (-V.v))))
  apply U.trans; refine le_trans (mul_le_mul_of_nonneg_left (upperRate S V ht b0 b x cool a (lt_min hw zero_lt_one) heB) (Real.exp_pos _).le) ?_
  rw [←Real.exp_add]; apply Real.exp_monotone; let Y:= upperMoney S B' L a H
  change _+budgetCharge V g Y≤_; have he:= eqBudget V Y y g; have h:=budgetLe V y K g (by unfold K; exact (le_abs_self _).trans ((le_max_right ..).trans (le_add_of_nonneg_right zero_le_one))); have hs:flagBill (mid m B) v v' C ≤ massMeter (mid m B)*X:=flagBound _ T C _ _ t t' h0 hC -- h shadow. edit
  unfold y at he; change _ +massMeter _*(Y+X-Y)=_ at he; linarith
def soaked (x:ℝ):= (Real.sqrt x)⁻¹
section advent
variable{r₀:ℝ}
open Pressure Real
local notation "N"=> massMeter
lemma amplifier : ∀ x:ℝ, 0<x→4*hemp (fun _=>x) 0=soaked x ∧ soaked x ≤ temp x ∧ 0<soaked x∧x*soaked x ^2=1 := by
 intro x t; have he:0 < (Real.sqrt x)⁻¹:=by positivity
 refine ⟨by unfold soaked hemp; ring, le_mul_of_one_le_right he.le (Real.one_le_exp (sq_nonneg _)), he,?_⟩; unfold soaked; rw [inv_pow,Real.sq_sqrt t.le,mul_inv_cancel₀ t.ne']
-- order matters
universe u1
variable (X:Pic.Span hP a b c d k r₀ n)(hO:HaarBudget group){D d0 U f H : ℝ}(A:Port X U f h' D d0 n')(p:h' ≤ h) -- shadow
include A p hO
lemma basePrice (K0 γ' L' r μ L C w:ℝ) (hg:0<w)(hC:0 ≤ C)(hr:0≤γ') : ∃ K:ℝ,0<K ∧ ∀ (S:ℕ→Side)(x:ℕ→ℝ)(E:ℕ→ℝ)(X':∀ j,GramM (mid (S j) B))(Y:∀ j,Loom (mid (S j) B)),
   Pastures B S x h C r μ γ' w L L' E X' → (∀ᶠ i in atTop, |Real.log (soaked (x i))|≤ K0 * massMeter (mid (S i) B)) → (∀ᶠ i in atTop,SkinT (X' i) (Y i) e) → ∀ᶠ i in atTop, Tableau (S i) (X' i) (Y i) P (soaked (x i)) K:= by
  obtain ⟨K,cK,Xt⟩:= uniform_meter X hO K0 1 zero_le_one L' L γ' C w hg hr hC; refine ⟨K,cK,fun S x F E Y e hu p' => ?_⟩
  have ht:Tendsto (fun i=> (x i)*temp (x i)^3) atTop (𝓝 0):= (e.large.oneFlag_pow_temp 1).congr fun i=> by unfold oneFlag; ring
  filter_upwards [(e.costR X Y p' A p).1,p',e.tend.eventually_ge_atTop n,e.support0,hu,e.loc.shrinks.eventually (ge_mem_nhds one_pos),ht.eventually (ge_mem_nhds one_pos),e.path.rank.eventually_gt_atTop 0] with i z u n ⟨t,f,k,A',hS,w⟩ ht v b' k'
  obtain ⟨_,r,q,T⟩:= amplifier (x i) k'; have hz:= T; rw [← e.beta i] at hz; -- also soaked? nth
  refine Xt (S i) (Nat.cast_le.mp n) (E i) (Y i) z.1 u _ _ _ _ _ f e.wind.le e.bold v v k _ q (by rw [t]; exact r) (by rw [e.beta]; exact T) A' hS (ht.trans_eq (mul_comm ..)) ?_ z.2.2.2.2.2.2.1
  rw [t,e.beta]; exact b'
end advent

variable {V:GramM (mid m B)}{S:Loom (mid m B)}(p:Tableau m V S P g C)
namespace Tableau
local notation "N"=> mid m B
include p
lemma TV_price : TV V S P/rateBet V S P ≤ Real.exp (2*massMeter Λ*C):=by
 rw [div_le_iff₀ ((Real.exp_pos _).trans_le p.lowB)]; apply p.highB.trans; apply le_trans _ (mul_le_mul_of_nonneg_left p.lowB (Real.exp_pos _).le); apply le_of_eq; rw [←Real.exp_add]; congr 1; unfold budgetCharge; ring
lemma positiveBet : ∀ F:Evaluation Λ,F∈allObs Λ→∀ x:ℝ, (0≤x) → (∀ i, ‖F i‖≤ x) → ‖finiteForm Y P V S F‖ ≤ x*Real.exp (2*massMeter Λ*C) := by
 intro F h t ht f; rw [relative (m:=m) Y P V S F,norm_div]; apply le_trans (b:=t*(TV V S P/rateBet V S P)) _ (mul_le_mul_of_nonneg_left p.TV_price ht); rw [←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (norm_nonneg (Complex.exp (-V.v)*partitionZ V P S)) -- trim

 unfold moment; apply (norm_integral_le_integral_norm _).trans; unfold TV; rw [←integral_const_mul]; have he := p.isPay.smul (Complex.exp (-V.v)); apply integral_mono (integrable_read (W:=recX P V S) he F ((mem_allObs ..).mp h).1).norm ((show Integrable (recX P V S) _ from he).norm.const_mul _) fun i=>?_; let X:= recX P V S i; exact (norm_inner_le_norm (𝕜:=ℂ) (mateK Λ) (acts (F i.1) X)).trans (by
   rw [(tickB Λ).2,one_mul]; exact (spentS _ _ _).trans (mul_le_mul_of_nonneg_right (f _) (norm_nonneg _))) -- tune lemma
end Tableau
end YM.CF.Window
