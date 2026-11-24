import YM.SU5.Lamour.Poise
import Verses.Policy
import Verses.Fusing
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
lemma forward_delta {A Q₀:Op (Single N)}{H H₀ : Wave (Single N)} {D:Op (Single N)}{f:Skye.Orbit N} {z:ℂ}(X:UNI (Single N))(hx:twist X (tickA N)=tickA N)(qt:IsStarProjection Q₀)(hp:IsStarProjection A)(p:H∈{x|Sea A x})(p₀:Sea (tickA N) H₀) (t:condor X.val 180)(hQ:condor A c)(cg:0≤c)
    (k:ℕ)
    (u:fiber (Saber (B:=tickA N) qt k) b)(bg:0≤b)(hs:b*180*(1+c)≤h) (F:FC (Single N))(Fcost:ℝ)(F0: ‖((Saber (B:=tickA N) qt k).foldC (tailor X)).glow F‖≤ Fcost) (αd:ℝ)(f₀:tier h (R.board f).val ≤ Real.exp αd) :
    let Z:= Complex.exp z • (tank A (R.board f)*exp (dg ((1-A)*D*A))); -- z directly exp. norm? RHS ‖z‖ in exponent via le
    let fX:= twist X A
    ‖inner ℂ H₀ (acts F (acts Z H))‖ ≤ Fcost*Real.exp (shotOut 0 k Q₀ fX b c D z+αd):=by
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
 let r:= αd -- coerce
 have hv':‖Y.glow (tank A (R.board f))‖ ≤ Real.exp r:=by
    let X0:=Y
    apply (tank_glow X0 A h 0 ∅ _ (show 0≤h from (mul_nonneg (mul_nonneg bg (by norm_num)) (by positivity)).trans hs) (le_refl _) ?_).trans
    · simp_rw [zero_mul,Real.exp_zero,mul_one]; exact f₀
    intro i; simp only [notMem_empty,↓reduceIte,mul_one]; exact (price_saber hp X0 hy c hQ cg (by positivity) i).trans (by rw [mul_comm 180]; exact hs)
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
