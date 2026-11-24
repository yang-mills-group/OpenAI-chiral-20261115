import YM.SU5.FiniteGaugeData.Cuprite.Dash
import YM.SU5.FiniteGaugeData.Cuprite.Fist
/-! # Determinant Ledger, compounding over actual fields.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Cascade Pastry Scree Fist Hutch Drama Drama.Pack
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {n:Type*} [LinearOrder n][Fintype n]{A B P Q Y D X U W R S T:Op n}{a r μ b h C M e v δ H:ℝ}
namespace Jersey
abbrev Mix (μ M v:ℝ):= RedAccount μ M v + XrayPay μ M v/2
abbrev curlR (Q R W:Op n):=Poem Q (Q*R) (Q*(W-1)*R)
def pLine(Q R:Op n)(μ r:ℝ):ℝ:= rueD (spring Q (Q*R))/2 + horizonM Q (Q*R) μ r
variable [Nonempty n]
lemma Wallet {x p:Wave n}(Z:Pack μ M e Q P R X W) (g:‖W-1‖≤r)(t:P*X=P)(u:Sea P x)(w:Sea Q p)(A:ribbon n)(k:pointM n Q R C)(l:0≤C)(d:2*C+2≤h)(v':0<v)(f: tier h A.val≤ Real.exp H) : ‖Fist.shade W p x (tank P A) X‖ ≤ Real.exp (pLine Q R μ r + curlR Q R W + (H+(2*v*Fintype.card n + Mix μ M v *e))) :=by
 let V:=Q*W*(1-P); let T:=tangle (bloom Q (Q*W*X*P) μ) * Q * W; let F(i:n):=cardfee Q P R X W μ i; let G(i:LeanV n):=if i.1 then F i.2 else 0
 have hv: 1≤ h:=by linarith
 have hg(i:LeanV n):0≤ G i:=by unfold G; split; exact norm_nonneg _; exact le_rfl -- norm_nonneg unfold F
 have hp(i:LeanV n):TwistReceipt (T*(1-P)) i ≤ h*Real.exp (G i):=by
    rcases i with ⟨b,i⟩; cases b
    · change 1 ≤ h*Real.exp 0; simpa using hv
    rw [show T*(1-P)=tangle (bloom Q (Q*W*X*P) μ) * (Q*W*(1-P)) from by unfold T; simp only [mul_assoc]]; exact Z.cardpoint k i d
 apply (aimed Z.pos Z.smallB Z.q Z.p t u w _ (zero_le_one.trans hv) hg hp).trans; apply (mul_le_mul_of_nonneg_right f (Real.exp_pos _).le).trans; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
 have hu:= Z.photo v' g; have he: (∑ i,G i) ≤ v* Fintype.card n + RedAccount μ M v *e:=by
    have he:(∑ i,G i)=∑ i:n,F i:=by rw [Fintype.sum_prod_type]; simp [G]; -- tune
    rw [he]; exact Z.cardbill v'
 unfold pLine curlR Mix; linarith only [hu,he,mul_nonneg v'.le (Nat.cast_nonneg (α:=ℝ) (Fintype.card n))]
-- tank(clamp) tier built from actual pledged Ledger on THIS period. 
end Jersey
end YM.CF.Fock.Reduction
namespace YM.CF.Graph
open Function Filter NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial Skye Laic Reduction Reduction.Hutch Reduction.Drama Reduction.Drama.Pack Reduction.Jersey
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n N m B L: Side}{T:GramM N}{α η r v μ M e H₀ h ξ ν τ d g C b: ℝ}{j:ℕ}{σ:Odd L.val}{X:GramM (mid n B)}{V Y:Scree.Loom N}{A:Op (Single N)}
lemma backstage (p:0≤h)(u:Ledger h τ η r M T) (z:Orbit N): tier h (T.board z).val ≤ Real.exp ((τ+τ+η)*(More N).val^4) := by
 let P:=actG T z; let B:=fueled T.p T.K z; change tier _ ((exp P*B) : Cipher N).val≤_; rw [add_mul,Real.exp_add]; refine (tier_mul p (exp P) B).trans (mul_le_mul ((Fist.cheer P p).trans ?_) (toeF u.force p z) (Pastry.pitch p _) (Real.exp_pos _).le); exact Real.exp_le_exp.mpr (marks T z u.reg u.slip p)
open Thera
-- grant record spatial total later. v tune ε. ζΛν. Define Upper beam (ρ) interface uses gauge conditioned ξ and c.
open Paige Vault
variable {Yg:Pricing j L σ (Thread j)}{Ω: Grasp Yg B d} {W R: Op (Single (mid n B))}(U:Loom (mid n B))(i:Orbit (mid n B))
-- X.P path etc supplied; prices
local notation "P₁"=> spar j X.J.M (U i)
local notation "Θ₁"=> tickA (mid n B)
-- Real beam vs actual ANY W. scope
lemma whole (u:Ledger h τ η r M X)(p:Pack μ ν e (tickA (mid n B)) (spar j X.J.M (U i)) R (1+actF j X U i) W)(a:Sea P₁ (changeM Ω (U i) X.J.M))(o:pointM (Single (mid n B)) Θ₁ R C)(w:‖W-1‖≤ b)(b0:0≤C)(v':0<v)(t:2*C+2≤h)(f: ‖Pec.pigment X.J.I (U i)‖≤ ξ) :
 ‖inner ℂ (mateK _) (acts (quant W) (beam X Ω U i))‖ ≤ Real.exp (ξ+(pLine Θ₁ R μ b+curlR Θ₁ R W+((τ+τ+η)*(More (mid n B)).val^4+(2*v*Fintype.card (Single (mid n B)) + Mix μ ν v * e)))) :=by
 let P:= spar j X.J.M (U i); let Q:=tickA (mid n B); let X₁:= actF j X U i; have hh:P*X₁=0:=by unfold X₁ actF Kennel.capT; change P*((1-P)*_*P)=0; rw [← mul_assoc,←mul_assoc,Porth p.p,zero_mul,zero_mul]
 have hy:X₁*P=X₁:=by unfold X₁ actF Kennel.capT; rw [mul_assoc,show _*P=P from p.p.1] -- syntax
 let A:= X.board i; let c:= -(Pec.pigment X.J.I (U i)); have hX: X₁*X₁=0:=by nth_rw 1 [←hy]; rw [mul_assoc, hh,mul_zero]
 rw [Graph.beam,Graph.mile,act_smul,map_smul,inner_smul_right,norm_mul,act_mul,tallied _ hX, Real.exp_add]
 change ‖Complex.exp c‖ * ‖Fist.shade W (mateK _) _ (tank P A) (1+X₁)‖ ≤ _
 refine mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by unfold c; rw [norm_neg]; exact f))) ((Wallet p w (by rw [mul_add,mul_one,hh,add_zero]) a (tickB ..) A o b0 t v' (backstage (by linarith) u i))) (norm_nonneg _) (Real.exp_pos _).le
end YM.CF.Graph
