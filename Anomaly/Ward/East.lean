import Anomaly.Ward.Island
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire Regis.Head Next.Rank.Spindle LampP
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
variable {n:Side}
namespace StageQ
local notation "Γ"=> More n
local notation "χ" => fieldDir SU.group (More n) 1
local notation "Πp"=> tangD n
open PotQ
variable {b k m:ℕ}{d c α C M w a z:ℝ}{P:BudgetPoint}{K:Loom n}{X:SOp n}{T E:tableQ SU.group (More n) ℂ} {x:Site n} (R:Knit X (node x) b d α M C w m T) (L:mintQ α C d m) (H:Roof n c d k K)(hb:b+k+10 ≤ P.B)(hp:P.threshold ≤ c)
variable (s:Rules SU.group) (g:2*(b+1)<(More n).val)(t:b ≤ P.B)(q:4*(b:ℝ)*P.threshold ≤ s.c)(r:8*b*P.threshold<α) (p:∀ u:SU.group.El,SU.group.chord u≤ z → ContinuousAt (SU.group.plog ∘ SU.group.mat) u) (hu:4*(b:ℝ)*P.threshold≤z)

-- ties.Movement
lemma movingRim {U:Pane n}(v:U∈rim P x)(V:Signed): flashA (gridTulip V x) U∈rim P x:=by
 let W:=gridTulip V x; have he:boxA W⁻¹ (node x)=node x:=by rw [sitU]; exact (Equiv.symm_apply_eq _).mpr (by rw [←nodeA,tieA])
 change Healthy _ _ _; unfold Healthy; rw [flagsA,← show (courtV P.B x).map (boxA W).symm.toEmbedding= courtV P.B x from sitU W ▸ screenχ P.B (node x) he]; exact Finset.disjoint_map _ |>.mpr v

include R L
lemma ballot_b (i:tangD n)(u:3 ≤ m)(v:‖i‖<α) : ‖stepQ X i - trim 2 (stepQ X) i‖≤2*C*M*‖i‖^3 := gaugeTaylor (norm_zero.trans_lt L.1) (fun x p=> (R.circle x p).order u) (step_idle _) R.roles v

abbrev stackT := onStage x (themis P x X b)
variable (u: 3 ≤ m) -- terms
local notation "ψ"=> themis P x X b
local notation "ℓx"=> stackT (b:=b) (P:=P) (x:=x) (X:=X)
include u s g t q r
lemma scannerCash (J:Jig x b (traceMeter P K x X) X T E P α (feeN M C) (gainN w)) (Q₀:Pane n)(f:Healthy P.threshold (Lattice.halo P.B {node x}) Q₀)(V':χ)(pw: Agrees (Lattice.halo b {node x}) Q₀ (represent V'))(v:‖collect SU.group V'‖<α) : ‖ℓx Q₀ - tariff E (receipt V')‖ ≤ feeN M C *‖collect SU.group V'‖^3:=by -- includes
 unfold stackT onStage; rw [J.transfer, show ∑ i:Signed,dollar i • ψ (flashA (gridTulip i x) Q₀)= (∑ i:Signed,dollar i • ψ (flashA (gridTulip i x) Q₀))-(∑ i:Signed,dollar i • (rawQ X 1)) from (by rw [blank_yaw_sum]; simp),← sum_sub_distrib,← sum_sub_distrib]; apply (norm_sum_le ..).trans ?_
 let Q:=Fintype.card Signed; unfold feeN; rw [mul_assoc,show (Q:ℝ)*_=∑ i:Signed, (2*C*M)*‖collect SU.group V'‖^3 from by simp [Q]]; apply sum_le_sum; intro i _
 rw [← smul_sub,← smul_sub,norm_smul,Real.norm_eq_abs,dollar_fixed,one_mul]; let h:=gridTulip i x; have he:boxA h (node x)=node x:=by rw [←nodeA,tieA]
 let U:rim P x:=⟨flashA h Q₀,movingRim (show Q₀∈rim P x from f) i⟩; let W':= sailH h V'; let V:=represent W'; have hz:V=flashA h (represent V'):=by simpa only [one_smul] using colorTravel h V' 1
 have hx: ‖collect SU.group W'‖≤‖collect SU.group V'‖:= by unfold W'; rw [← seaChange]; exact screenA ..
 rw [show ψ (flashA (gridTulip i x) Q₀)=rawQ X V from priceFog R L s g t q r U V (by rw [hz]; apply flashD; rw [show (courtV b x).map _= _ from screenχ _ _ he]; exact pw) (L.2.2.2.1 _ (hx.trans_lt v)),R.poses]
 exact (ballot_b R L _ u (hx.trans_lt v)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) (debit0 R L))

lemma stackSup (i:Pane n) : ‖ψ i‖ ≤ ‖rawQ X 1‖+maskBudget P b C M:=by
 have hx:=debit0 R L; unfold themis; by_cases l:i∈rim P x
 · rw [Set.indicator_of_mem l]; let v:=mapW b x i; let Y:=stepQ X
   have hu:= vetted s g t q x ⟨i,l⟩; have he:‖v‖≤8*b*P.threshold:= hu.1; let A:= increment 1 v; change ‖rawQ X A‖ ≤ _; rw [show rawQ X A=Y v+rawQ X 1 from (sub_add_cancel ..).symm]; refine ((norm_add_le ..).trans_eq (add_comm ..)).trans (add_le_add_right ?_ _)
   have hv: ‖trim 2 Y v‖ ≤ 2*C*M * ‖v‖^2:=by
      unfold Nacre.trim cake Tensor.diagonal; simp only [_root_.smul_apply,norm_smul,norm_inv]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [Nat.factorial])) ; refine ((iteratedFDeriv ℝ 2 Y _).le_opNorm _).trans ?_; simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right ((R.circle _ (norm_zero.trans_lt L.1)).2 2 (by omega)) (sq_nonneg _)
   refine (norm_le_norm_sub_add (Y v) (trim 2 Y v)).trans ((add_le_add (ballot_b R L v u (he.trans_lt r)) hv).trans (?_)); have ha:= pow_le_pow_left₀ (norm_nonneg _) he 2; have hr: ‖v‖^3 ≤ ‖v‖^2:= pow_le_pow_of_le_one (norm_nonneg _) ((he.trans r.le).trans L.2.1) (by omega); unfold maskBudget; nlinarith only [mul_le_mul_of_nonneg_left ha hx,mul_le_mul_of_nonneg_left hr hx,mul_nonneg hx (sq_nonneg ‖v‖)]
 rw [Set.indicator_of_notMem l,norm_zero]; exact add_nonneg (norm_nonneg _) (by unfold maskBudget; nlinarith only [mul_nonneg hx (sq_nonneg (8*(b:ℝ)*P.threshold))])

abbrev headline (B: BudgetPoint)(b:ℕ)(c C M:ℝ):= Fintype.card Signed*(c+maskBudget B b C M)
lemma stackH (i:Pane n): ‖ℓx i‖ ≤ headline P b (‖rawQ X 1‖) C M:=by refine (norm_sum_le ..).trans (?_); simp_rw [norm_smul,Real.norm_eq_abs,dollar_fixed,one_mul]; exact (sum_le_sum (fun s' _=>stackSup R L s g t q r u (flashA (gridTulip s' x) i))).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])
include p hu
lemma stack_env : Envelope ℓx:=by
 refine ⟨?_,headline P b (‖rawQ X 1‖) C M,fun i=>stackH R L s g t q r u i⟩
 exact Finset.measurable_fun_sum _ (fun i _=> (measurable_const (a:=dollar i)).smul ((certifiedCont R L s g t q r p hu).comp (revM (gridTulip i x)).measurable)) -- tune argument order
omit p hu u
lemma stackGauge (U:Pane n)(k:Seat n→ SU.group.El) : ℓx (gauge k U)=ℓx U:=by refine sum_congr rfl fun i _=>?_ ; rw [revG]; exact congrArg _ (bill_gauge R L s g t q r _ _)
omit R L s g t q r
private lemma fleetT (s:Sweep n)(i:Pane n)(p: Rue.FleetS P.threshold i): Rue.FleetS P.threshold (flashA s i):=by
 rw [revoke]; let U:= pull s.s ((assembly n).embed s.b) i; have he:Rue.FleetS P.threshold U:= fun j=>by rw [Face.send_price _ _ _ _ _ SU.group.chord_inv (fun u v=> SU.group.chord_conj ..)]; exact p _
 intro b; cases g:s.charge; exact he b
 exact (show SU.group.chord (faceValue (Reef.echo U) b)=_ from by unfold faceValue; rw [Reef.echo_t, Reef.cool]).symm ▸ he b -- tune
include R L s g t q r H hb hp
lemma pledgeH(i:Pane n)(v:Rue.FleetS P.threshold i): onStage x (traceMeter P K x X) i=ℓx i:= sum_congr rfl (fun j _=> congrArg (dollar j • ·) (nearMask R L H hb hp s g t q r _ (fleetT _ _ v)))
end StageQ
end YM.CF.Swell.Sonar
