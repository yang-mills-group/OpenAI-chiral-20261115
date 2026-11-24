import YM.CF.Continuum.DawnClock
import YM.CF.Continuum.CityGate
import YM.CF.Continuum.LaurelBeam
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Window.Record
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Dial
open Graph Graph.Diff Graph.Angle Skye RG Laic MeasureTheory PathData Sods Precision Wilson Cascade CF.Paige Vault Nova YM.Next.Rank Emu Mint Mint.Roe
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {L B m n:Side}{j k t:ℕ}{a b c d v e g C₀ r h x y γ Vμ δ K D C H χ Λ vA:ℝ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{P:Grasp Y B e}
local notation "Π" => mid m B
local notation "φ" => CSide m B
variable (A B':GramM (mid m B))(S:Loom (mid m B))(A₀:Roof (mid m B) a e t S)(hm:P.roundZ≤ (mid m B).val)
local notation "Wκ"=> recX P
structure Cart (X Y:GramM n)(h x κ δ:ℝ): Prop where
 width: X.p=Y.p
 path: X.path=Y.path
 funds: X.funds=Y.funds
 org:X.J=Y.J
 income : |X.beta-Y.beta|≤δ
 spare:X.slip=0
 pole:Y.slip=0
 grant:ξX X Y κ h
 grip: δ * jumpTax X.p (More n) X.funds x ≤ 1/2
 eta: rankV n κ≤1/2
variable (D1:Cart A B' h C Vμ δ)
variable (ht:A.path.Bounds A.funds r C Λ) (K₀:Ledger h v v Vμ C₀ A) -- replace Vμ role rL
variable {κ0 Rv:ℝ}
variable (pw:Ledger h v v Rv C₀ A)(pu:Ledger h v v Rv C₀ B')(hp:1≤h)(vc:0≤v)(w:0≤C₀)(ur:0≤Rv)(pX:0≤C)
local notation "Δ"=> δ * jumpTax A.p (More Π) A.funds C
def paceZ (t:BudgetPoint)(N:Side)(U:Clip)(C δ κ:ℝ):=2*(δ * jumpTax t (More N) U C) + 3 * rankV N κ -- K needless.remove later
local notation "FQ"=>paceZ A.p Π A.funds C δ Vμ
include D1 ht pw pu vc w ur pX hp A₀ hm
lemma on_trace (x:Orbit Π) : ‖recX P A S x-recX P B' S x‖ ≤ past B' x.1*Real.exp (flagBill (mid m B) v v C₀)*paceZ A.p Π A.funds C δ Vμ:=by
 let K:= changeM P (S x) A.J.M; have he:‖K‖=1:= (sea_g hm (S x) (A₀.paid x) A.J.M).2
 let A':= beam A P S x; let D':= beam B' P S x; let σ:= past A x.1; let σ':=past B' x.1; let T:= Real.exp (flagBill Π v v C₀); let p:= Δ; let Z:=rankV Π Vμ; let hV:= (P.broadness _ hm A.J.M).projection _ (A₀.paid x)
 have hv: ‖A'‖≤T:= (spentS _ _ K).trans (by rw [he,mul_one]; exact extensive_mile pw _ ur hp w hV)
 have hx : ‖σ-σ'‖ ≤ σ'*(2*p):= arcshift x.1 ht pX D1.income D1.grip D1.width D1.path D1.funds
 have hc: A'- D'= acts (mile j A S x-mile j B' S x) K:=by rw [act_sub]; unfold A' D' Graph.beam; rw [←D1.org]
 have ht: ‖A'- D'‖ ≤ T*(3*Z):=by rw [hc]; exact (spentS _ _ K).trans (by rw [he,mul_one]; exact mile_diff A B' hp j D1.width D1.spare D1.pole D1.org pw pu S x D1.grant D1.eta hV ur vc)
 have hZ:0<σ':=Real.exp_pos _; rw [porch,porch]; change ‖σ • A'- σ' • D'‖≤ _; rw [show σ • A'-σ'• D'=(σ-σ')•A'+σ'•(A'- D') from by rw [sub_smul,smul_sub]; abel]; apply (norm_add_le ..).trans
 rw [norm_smul,norm_smul, Real.norm_of_nonneg hZ.le]; exact (add_le_add (mul_le_mul hx hv (norm_nonneg _) ((norm_nonneg _).trans hx)) (mul_le_mul_of_nonneg_left ht hZ.le)).trans_eq (by unfold paceZ; change _=σ'*T*(2*p+3*Z); ring)
lemma respects : 0 ≤ FQ:=by
 let i:Orbit Π:= (1,Classical.arbitrary _); let s:=on_trace A B' S A₀ hm D1 ht pw pu hp vc w ur pX i; exact nonneg_of_mul_nonneg_right ((norm_nonneg _).trans s) (mul_pos (Real.exp_pos _) (Real.exp_pos _)) -- left? implicit P inferred hm
variable (Aκ:HaarBudget group)(gt:0<g)(vB:B'.beta*g^2=1)(hB:g≤ B'.p.threshold)(sA:Integrable (denZ A P S) (city _))(sB:Integrable (denZ B' P S) (city _))
include gt vB hB sA sB
theorem illum : (∫ i:Orbit Π, ‖recX P A S i-recX P B' S i‖ ∂city _)≤ Real.exp (flagBill Π v v C₀)*fullRate Aκ B' C Λ g * FQ:= by
 let F:=flagBill Π v v C₀; let Q(x:Orbit Π):=Real.exp (-basal B' g x.1); let T:=taxY (More Π) B'.beta B'.p.threshold C Λ+Fintype.card (Face (Per (More Π)))/2; let y:=FQ*Real.exp (F+T);
 obtain ⟨t,h⟩:=repays Aκ B' gt; have hu:B'.path.Bounds B'.funds r C Λ:=by rw [← D1.funds,←D1.path]; exact ht
 have e':0≤paceZ A.p Π A.funds C δ Vμ:= respects A B' S A₀ hm D1 ht pw pu hp vc w ur pX -- h shadow
 have hi:(∫ x:Orbit Π, ‖recX P A S x-recX P B' S x‖ ∂city _) ≤ ∫ i:Orbit Π,y*Q i ∂city _:=by
    have hk:Integrable (fun i:Orbit Π=>recX P A S i-recX P B' S i) (city _):=(sA.smul (Complex.exp (-A.v))).sub (sB.smul (Complex.exp (-B'.v))); refine integral_mono hk.norm (t.const_mul y) fun i=>?_ ; apply (on_trace A B' S A₀ hm D1 ht pw pu hp vc w ur pX i).trans; have he:=past_budget B' hu gt vB hB i.1 (w:=0) le_rfl (Or.inr rfl) (Or.inr rfl); rw [zero_mul,mul_zero,zero_div,sub_zero] at he; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le) e').trans_eq (by
      try unfold y
      unfold F T Q; simp_rw [Real.exp_add]; ring) -- Q F T abbreviations tune
 rw [integral_const_mul] at hi; unfold fullRate; refine hi.trans ((mul_le_mul_of_nonneg_left h (mul_nonneg e' (Real.exp_pos _).le)).trans_eq ?_); unfold F T; simp_rw [Real.exp_add]; ring -- may need unfold
end YM.CF.Window.Record
