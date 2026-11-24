import YM.CF.Ups.Tot
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars true
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade.Earn
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)

open Corne

section all
variable {I:Type}[Fintype I][DecidableEq I](A:Matrix I I ℝ) (C:ℝ)
omit [DecidableEq I] in
private lemma sum_images(i:I) : ∑ j, |A i j| ≤ ‖paintO (τ:=I) A‖ :=by
 let v : Fish I:= fun j=> if A i j≥ 0 then 1 else -1
 have he:‖v‖ ≤ 1:= (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=> by unfold v; split_ifs<;> simp
 have hp:(∑ j,|A i j|)= paintO A v i:=by
    rw [paintO_p]; refine sum_congr rfl fun j _=>?_ ; change _=A i j*v j; unfold v; split_ifs with h; rw [abs_of_nonneg h,mul_one]; push Not at h; simp [abs_of_nonpos h.le]
 rw [hp]; exact (le_abs_self _ : paintO A v i ≤ |paintO A v i|).trans (((norm_le_pi_norm (paintO A v) _).trans (((paintO A).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) he)))) -- hp subst rhs?
private lemma orientedDet : |A.det| ≤ ‖paintO (τ:=I) A‖^Fintype.card I:=by
 let S(f:I→I):= ∏ i:I,|A i (f i)|; let e:Equiv.Perm I ↪ (I→I):=⟨fun p i=>p i,fun f g h=>Equiv.ext (congrFun h)⟩
 have hu(f):0≤S f:= prod_nonneg (fun i _=> abs_nonneg _)
 have hx:(∑ i:Equiv.Perm I,S (e i))= ∑ j∈ univ.map e,S j:=by simp
 rw [←Matrix.det_transpose, Matrix.det_apply]; apply (Finset.abs_sum_le_sum_abs ..).trans
 calc
    _ ≤∑ i:Equiv.Perm I,S (e i):=sum_le_sum fun i _=>by
       rcases Int.units_eq_one_or (Equiv.Perm.sign i) with h|h <;> simp [S,e,h,Matrix.transpose_apply,Finset.abs_prod]
    _ ≤ ∑ f:I→I,S f:=by rw [hx]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> hu i
    _ = ∏ i:I, ∑ j:I,|A i j|:= by
          convert (Finset.prod_univ_sum (fun _ : I=> (Finset.univ:Finset I)) (fun i j=> |A i j|)).symm using 2
          simp
    _ ≤ ∏ _:I, ‖paintO (τ:=I) A‖ := prod_le_prod (fun i _=>sum_nonneg fun _ _ => abs_nonneg _) (fun i _ =>sum_images A i)
    _ = _:=by simp
private lemma logSafe (e:0 < C) (h:‖paintO (τ:=I) A‖≤ C):Real.log A.det ≤ Fintype.card I * C:=by
 by_cases hp:A.det=0; rw [hp,Real.log_zero]; positivity
 calc
    _ = Real.log |A.det|:=(Real.log_abs _).symm
    _ ≤ Real.log (C^Fintype.card I):= Real.log_le_log (abs_pos.mpr hp) ((orientedDet A).trans (pow_le_pow_left₀ (norm_nonneg _) h _))
    _ = Fintype.card I * Real.log C:= by rw [Real.log_pow]
    _ ≤ _ := by gcongr; exact (Real.log_le_sub_one_of_pos e).trans (sub_le_self _ zero_le_one)
end all
lemma detPay (L:Patch)(K:Teller SU.group)(p:L.Branches K.bind SU.group): ∃ C:ℝ,0<C ∧∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(M:Monk SU.group S), ∀ T:Tube SU.group S, Cert L K S T x → -(Fintype.card (Site f):ℝ)*C≤ Corne.arcD T x M:=by
 obtain ⟨m,v,C,hm,hv,hC,h⟩:= Neige.bear K L 2 p; let s:= Fintype.card SU.group.ColorIndex; let i:ℝ:= s
 refine ⟨2*C*i+1,by unfold i; positivity,?_⟩; filter_upwards [h] with x h c f S M T t
 let k:= Corne.kist M; have hx:ShardIncome 2 x v C m T k.key k.park k.V k.k:= h S T t _ _ _ (PhysicalNext.JointLoad.Heir.noFlags ..|>.symm) _
 have he:Fintype.card (Active k.key x k.park) ≤ Fintype.card (Site f)*4:=by
    let I:= Active k.key x k.park; let e: I ↪ Edge (Site f):=⟨fun i=> i.val.val, fun u v p => Subtype.ext (Subtype.ext p)⟩
    exact (Fintype.card_le_of_embedding e).trans_eq (by rw [show Fintype.card (Edge (Site f))= Fintype.card (Site f)*Fintype.card Axis from Fintype.card_prod ..]; rfl) -- tune
 have hv:= logSafe _ _ hC (show ‖paintO (baseX T x k.key k.park k.k k.V)‖ ≤ C from by simpa [Function.comp_apply,Vmove] using hx.kernel.value)
 rw [Fintype.card_prod] at hv; unfold arcD; apply le_trans _ (mul_le_mul_of_nonpos_left hv (by norm_num)); push_cast
 calc
    _ ≤ -(Fintype.card (Site f):ℝ)* (2*C*i) :=by exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr (by positivity))
    _ = -(1/2:ℝ)*(((Fintype.card (Site f):ℝ)*4 *i)*C):=by ring
    _ ≤ _:=by
       apply mul_le_mul_of_nonpos_left _ (by norm_num); gcongr; exact_mod_cast he
end YM.CF.Jade.Earn
