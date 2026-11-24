import YM.SU5.Lamour.Poise
import Verses.Policy
import Verses.Ocean
import YM.SU5.Relativistic.Raspa
import YM.CF.Continuum.Extensive
/-! # pinpoint charge. On clean ORBIT. (For unrepaired dirty count by t.) -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open CF.Window Matrix Papyrus.Granat Thera Graph Font Skye RG Laic Scree Branch Peaks Drapes BProof Spire
namespace Verses
set_option linter.unusedSectionVars false
variable {N:Side}{R:GramM N}{Q:Sweep N→Prop}{h a a' a'' b c:ℝ}
lemma board_catalog {P:Op (Single N)} (U:Shaft (Single N))(u:fiber U c)(v:0≤c)(p:IsStarProjection P)(t:condor P b)(t':0≤ b)(g:c*(1+b)≤h)(A:Orbit N)(f:IncX Q R.F R.p h a)(f':IncX Q R.slip R.p h a')(f'':Dark Q R.K R.p h a'') : ‖U.glow (tank P (R.board A))‖ ≤ Real.exp ((a+a'+a'')*(More N).val^4):=by
 let Y:= Graph.actG R A; let F:=fueled R.p R.K A; have he:0≤h:= (mul_nonneg v (by positivity :0 ≤ 1+b)).trans g
 apply (tank_glow U P h 0 ∅ _ he le_rfl ?_).trans
 · simp only [zero_mul,Real.exp_zero,mul_one]
   change tier h ((exp Y:Dough _).val*F.val)≤ _; rw [add_mul,Real.exp_add]; exact (tier_mul he _ F).trans (mul_le_mul ((dust_exp h Y he).trans (Real.exp_le_exp.mpr (Graph.marks R A f f' he))) (Graph.toeF f'' he _) (pitch he F.val) (Real.exp_pos _).le)
 intro i; simpa only [notMem_empty,↓reduceIte,mul_one] using (price_saber p U u b t t' v i).trans g

-- algebraic part in genuine horizon; outer Board estimate scalar; no measurability needed
abbrev shotOut (n k:ℕ)(Q:Op (Single N))(A:Op (Single N))(c C:ℝ)(d:Op (Single N))(z:ℂ) := stunt k (tickA N) Q + ((c*c+1)*entryBudget (A-Q)/2+((180*c)^2 * (1+C)*C*entryBudget d+‖z‖))
lemma kinetic {A Q₀:Op (Single N)}{H H₀ : Wave (Single N)} {D:Op (Single N)}{f:Skye.Orbit N} {z:ℂ}(X:UNI (Single N))(hx:twist X (tickA N)=tickA N)(qt:IsStarProjection Q₀)(hp:IsStarProjection A)(p:H∈{x|Sea A x})(p₀:Sea (tickA N) H₀) (t:condor X.val 180)(hQ:condor A c)(cg:0≤c)
    (k:ℕ)
    (u:fiber (Saber (B:=tickA N) qt k) b)(bg:0≤b)(hs:b*180*(1+c)≤h) (F:FC (Single N))(Fcost:ℝ)(F0: ‖((Saber (B:=tickA N) qt k).foldC (tailor X)).glow F‖≤ Fcost) (f₀:IncX Q R.F R.p h a)(f₁:IncX Q R.slip R.p h a')(f₂:Dark Q R.K R.p h a'') :
    let Z:= Complex.exp z • (tank A (R.board f)*exp (dg ((1-A)*D*A))); -- z directly exp. norm? RHS ‖z‖ in exponent via le
    let fX:= twist X A
    ‖inner ℂ H₀ (acts F (acts Z H))‖ ≤ Fcost*Real.exp (shotOut 0 k Q₀ fX b c D z+(a+a'+a'')*(More N).val^4):=by
 intro Z fX
 let y:=Saber (B:=tickA N) qt k; let Y:=y.foldC (tailor X); let L:= (c*(entryBudget D)); have hv:0≤ Fcost:= (norm_nonneg _).trans F0
 let F':=Y.glow F
 let A':=(1-A)*D*A; have he:entryBudget A' ≤ (1+c)*c* entryBudget D:=by
    have hh:=condor_one_sub A hQ
    have ht':entryBudget (D*A)≤L:= condor_right A D (by rw [hp.isSelfAdjoint]; exact hQ)
    unfold A'; rw [mul_assoc]; exact (condor_budget _ _ hh).trans ((mul_le_mul_of_nonneg_left ht' (by positivity:0≤1+c)).trans_eq (by unfold L; ring)) -- .. hh invalid
 have hy:fiber Y (180*b):=by rw [mul_comm]; exact trim_saber _ _ u bg _ t
 let E:=(180*b)^2*((1+c)*c)*entryBudget D
 have hN:0 ≤ 180*b:=by positivity
 have hu:‖Y.glow (exp (dg A'))‖≤ Real.exp E:=by
    rw [glow_thermal]
    apply (Graph.bootC _).trans (Real.exp_monotone _)
    change ‖_‖ ≤ _; apply (glow_dg Y hy hN _).trans ((mul_le_mul_of_nonneg_left he (show 0≤(180*b)^2 from sq_nonneg _)).trans_eq (by unfold E; ring)) -- ^2 defeq
 let r:= (a+a'+a'')*(More N).val^ (4:ℕ) -- coerce
 have hv':‖Y.glow (tank A (R.board f))‖ ≤ Real.exp r:=by apply board_catalog Y hy hN hp hQ cg _ f f₀ f₁ f₂; rw [mul_comm 180]; exact hs
 have hP: ‖Y.glow Z‖≤ Real.exp (‖z‖+r+E):=by
    rw [Real.exp_add,Real.exp_add,Y.glow_free,Y.glow_mult,norm_smul,mul_assoc (Real.exp ‖z‖)]
    exact mul_le_mul (Complex.norm_exp_le_exp_norm z) ((norm_mul_le ..).trans (mul_le_mul hv' hu (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le
 have hQX: IsStarProjection fX:=⟨(by change twist X A *twist X A=_; rw [←map_mul,hp.isIdempotentElem.eq]),(by change star (twist X A)=_; rw [←map_star,hp.isSelfAdjoint])⟩
 have hX1:Sea fX (acts (quant X.val) H):=Lamour.Bridge.lifted X p
 let B:= (b*b+1)*entryBudget (fX-Q₀)/2
 have hM:‖acts (quant Y.sell) H‖ ≤ Real.exp B:=by unfold Y Shaft.foldC tailor; simp only [quant_mul,act_mul]; exact attacking y Q₀ qt (Saber_holds qt _ _) u bg fX hQX _ hX1
 have hJ:Sea (tickA N) (acts (quant X.val) H₀):=hx ▸ Lamour.Bridge.lifted X p₀
 let s:=stunt k (tickA N) Q₀
 let Hyper:=acts (quant (star Y.buy)) H₀; have hh: ‖Hyper‖=Real.exp s:=by
    unfold Hyper; rw [show star Y.buy=(1-Comb (tickA N) Q₀ k)*X.val from (by unfold Y y Shaft.foldC tailor Saber; simp), quant_mul,act_mul]
    exact CF.Papyrus.Franc.purse qt (Cascade.plus_P N) _ _ hJ -- plus_P
 rw [←act_mul,Y.lawn,Y.glow_mult,act_mul]
 refine (norm_inner_le_norm ..).trans ?_; rw [show ‖(acts _ H₀:Wave (Single N))‖ = Real.exp s from hh]
 apply le_trans (mul_le_mul_of_nonneg_left ((Graph.spentS _ F' _).trans (mul_le_mul F0 ((Graph.spentS _ _ _).trans (mul_le_mul hP hM (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) hv)) (Real.exp_pos _).le)
 change Real.exp s*(Fcost*(Real.exp (‖z‖+r+E)* Real.exp B))≤_
 rw [mul_left_comm, ←Real.exp_add, ←Real.exp_add]; unfold shotOut; apply le_of_eq; congr 2; unfold s E B r; ring
end Verses
end YM.CF.Papyrus.Franc
