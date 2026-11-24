import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion
import GaugeFieldConstruction.Matin
/- construct pure ge5 wing eqCost -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 120000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Laurent Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Work Tensor
open Fock Tulip Lat Spire Phase Cube
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
open F03
open TableF TableF.Lenten Haro Housing HushP
local notation "GS"=>SU.group
variable (o:Seat n)(q:Clip)(e: Axis)(f:PlaqAxes)(p:BudgetPoint)(b:ℝ)
private theorem spareZ: ∃ x:Axis,x≠e ∧ x≠ f.val.1 ∧ x≠f.val.2:= by
 have hp : ∀ x y z : Axis, ∃ w:Axis,w≠x∧w≠y∧w≠z:=by decide
 apply hp
abbrev spare:= (spareZ e f).choose
lemma spare_L: spare e f≠e∧spare e f ≠ f.val.1 ∧ spare e f ≠ f.val.2:= (spareZ e f).choose_spec
abbrev KitP: GateI:= (f,some (spare e f))
abbrev Lamp(A:Pane n):= πon o (KitP e f) p A
abbrev CupT(A:Pane n):= at_E o e (Lamp o e f p A)
abbrev Pudge : SU.group.Color→L[ℝ] tangD n:= (LinearMap.single (R:=ℝ) (φ:=fun _:Edge (Seat n)=>SU.group.Color) (o,e)).toContinuousLinearMap -- tune
lemma puillon: Pudge o e= ContinuousLinearMap.pi (fun i=> if i=(o,e) then ContinuousLinearMap.id ℝ _ else 0):=by
 apply ContinuousLinearMap.ext; intro i; funext j; change at_E (G:=GS) o e i j=_; by_cases h:j=(o,e) <;> simp [at_E,Pi.single_apply,h]
lemma puff: ‖Pudge o e‖≤1:=by rw [puillon]; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro a; simp only [ContinuousLinearMap.pi_apply]; split_ifs with p <;> simp
lemma pupq(X: SU.group.Color): Pudge o e X=at_E o e X:=rfl
lemma cup_local : LocalOn (Pach o) (CupT o e f p):=by
 -- don't assume p.order, use slot_local from walk. instead Pf grade using compact.p.L input; p general apply pearl with p.power.Le extends by altering unused power
 let p': BudgetPoint:={p with power:=2, order:=6, order_ge:=le_rfl,power_ge:=le_rfl}; obtain ⟨C,h,H⟩:= F_grade; have hh:= (H n o (KitP e f) p' (by change 2≤3; decide) (by change 6≤6; decide)).live; exact fun i j l=>congrArg (at_E o e) (hh _ _ l)
lemma bulb_T (A:Pane n): ContDiffAt ℝ ω (CupT o e f p ∘ increment A) 0:=by
 obtain ⟨C,h,w⟩:= slotChart SU.group 10 6
 exact (Pudge o e).contDiff.contDiffAt.comp (f:=Lamp o e f p∘increment A) _ (((w _ A o _ (stabL _)).analytic).const_smul (p.threshold)⁻¹)
open Next.SectorChange.Motion
lemma bulb_c (A:Pane n)(u:Seat n→ SU.E): CupT o e f p (gauge u A)= swing u (CupT o e f p A):=by
 funext i; unfold CupT at_E Lamp; rw [πGauge, swing_eval]; by_cases h:i=(o,e) <;> simp [h]
lemma flat_cup : CupT o e f p 1=0:=by rw [CupT,Lamp,π_flat,←pupq,map_zero]
abbrev ζcone (A:Pane n): tangD n →L[ℝ] ℝ := (b*Turret o (G:=GS) p.threshold A) • hue_T (Dorm o q) A - hue_T (Turret o p.threshold) A
abbrev RCore (A:Pane n):ℝ:= p.threshold * ζcone o q p b A (CupT o e f p A)
abbrev markFee(A:Pane n):ℂ:=Complex.ofReal ((1/(b*p.threshold^2):ℝ) * (RCore o q e f p b A : ℝ)) -- ↑ product coerced
lemma markGauge: GaugeInvariant (markFee o q e f p b):=by
 intro i U; unfold markFee; apply congrArg (fun x:ℝ=> (((1/(b*p.threshold^2))*x:ℝ):ℂ)); unfold RCore; rw [bulb_c]; let T:=gauge i U; let X:=ζcone o q p b T; let x:=CupT o e f p U; rw [show ζcone o q p b T (swing i x)=_ from (show X (swing i x)=ζcone o q p b U x from ?_)]
 let Y:=Turret o (G:=GS) p.threshold; let Z:=Dorm o q
 have hy: Y T=Y U:=turret_inv o p.threshold i U
 change b*Y T*hue_T Z T (swing i x)- hue_T Y T (swing i x)= b*Y U*hue_T Z U x - hue_T Y U x; rw [hy,show hue_T Z T (swing i x)=hue_T Z U x from DFunLike.congr_fun (hueGauge (G:=SU.group) U i Z (hotel_inv o q) (fun U=> dorm_π o U q)) x, show hue_T Y T (swing i x)= hue_T Y U x from DFunLike.congr_fun (hueGauge (G:=SU.group) U i Y (turret_inv o p.threshold) (turret_π o _)) x]
lemma zeta_jet(U:Pane n): ContDiffAt ℝ ω (ζcone o q p b ∘ increment U) 0:= ((contDiffAt_const.mul (turret_π o p.threshold U)).smul (turn_c U (dorm_π o U q))).sub (turn_c U (turret_π o _ U))
lemma mark_jet(U: Pane n): ContDiffAt ℝ ω (markFee o q e f p b ∘ increment U) 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=fun x=> ((1/(b*p.threshold^2):ℝ) * (RCore o q e f p b) (increment U x))) _ (contDiffAt_const.mul (contDiffAt_const.mul ((zeta_jet o q p b U).clm_apply (bulb_T o e f p U)))) -- tune coe
lemma mark_local : LocalOn (Pach o) (markFee o q e f p b):=by intro U V h; unfold markFee RCore ζcone; rw [turret_sees o _ _ _ h,cup_local o e f p U V h,hue_loc _ (turret_sees o _ ) U V h,hue_loc _ (hotel_sees o _) U V h]
lemma milk_core (v':ℝ)(v:0≤v')(P:Haw p o (Pach o) (πon o (KitP e f) p) v')(R:Pane n)(h:pingS p.threshold (Pach o) R)(T:ℝ)(L:ℝ)(hx:0≤T)
 (s: Allows (p.order+1) (Turret (G:=GS) o p.threshold ∘ βten p.threshold R) 0 T)(r:Allows (p.order+1) (Dorm o q ∘ βten p.threshold R) 0 (L * p.threshold^2))(w:p.order ≤6)(z:0<b)(k:1≤b*p.threshold^2): let γ:=‖Complex.ofRealCLM‖; let a:ℝ:=2^6
 Jet.Allows p.order (markFee o q e f p b ∘ solo p.threshold R) 0 (γ*(T*(1+a*L))*a*v'):=by
 intro γ a; let t:= p.threshold; have hp:0<t:=p.threshold_pos; let M:=solo t R; let C:=CupT o e f p; let F:= Lamp o e f p; let X:=Dorm o q; let Y:=Turret (G:=GS) o t; let V:=markFee o q e f p b
 have H:Jet.Allows p.order (C ∘ M) 0 v':=by have he:=(milk_H o P R h).linear (Pudge o e) (puff o e); rw [one_mul] at he; exact he
 have uX:= pull_turn R r; have uY:= pull_turn R s; let Q:= turnq X t; let W:=turnq Y t
 have hz:Jet.Allows p.order (Y∘M) 0 T:=by
    have hv':‖fog GS (More n)‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=>by change ‖((v,0):tandem GS (More n))‖≤_; simp
    have hg:= packs (fog GS (More n)) (Y∘βten t R) s hv'
    have hv:Allows p.order (Y ∘ M) 0 T:=(hg.germ (Eventually.of_forall (fun i=> ?_))).order (Nat.le_succ _) -- tune
    · exact ⟨hv.analytic.of_le le_top,hv.norm_le⟩
    change Y (increment (increment R _) (t • (0:tangD n)))= _; rw [smul_zero]; simp [M,solo,fog]
 let G(i:Pane n):= b • (Y i • Q i)- W i
 have he: V=fun i=>(((1/(b*t^2):ℝ)*(G i (C i)) :ℝ):ℂ):=funext fun i=>by
    unfold V markFee; apply congrArg Complex.ofReal; change 1/_*(t*(b*Y i * (hue_T X i (C i))-hue_T Y i (C i)))=1/(b*t^2)*_; unfold G Q W; simp only [_root_.sub_apply, _root_.smul_apply,tone_s (L:=X) _ (fun v=> dorm_π o v q),tone_s (L:=Y) _ (turret_π o _), RingHom.id_apply,smul_eq_mul]; ring
 have ht:Jet.Allows p.order (G ∘ M) 0 (b*(a*T*(L*t^2))+T):=by
    let m:ℝ:=2^p.order; let P0:= Q ∘ M; let Q0:= Y ∘ M; let E:=tangD n→L[ℝ] ℝ
    have hQ:Jet.Allows p.order (fun i=>Q0 i • P0 i) 0 (m*T*(L*t^2)):=by
      have hx:=hz.bilinear (ContinuousLinearMap.lsmul ℝ ℝ) uX (ContinuousLinearMap.opNorm_lsmul_le); rw [mul_one] at hx; exact hx -- tune
    refine Jet.Allows.mono ((hQ.smul b).add (uY.smul (-1))|>.germ (Eventually.of_forall fun i=>?_)) ?_
    · change _+(-1:ℝ) • _=_ - _; rw [neg_smul,one_smul, sub_eq_add_neg]; rfl
    rw [abs_of_pos z,abs_neg,abs_one,one_mul]; have hv:= r.nonneg; unfold m a; gcongr; norm_num
 have hφ: Jet.Allows p.order (fun i=> G (M i) (C (M i))) 0 ((2:ℝ)^p.order*(b*(a*T*(L*t^2))+T)* v'):=by
    have he:= ht.bilinear ((ContinuousLinearMap.apply ℝ ℝ).flip) H (K:=v') (M:=1) ?_; rw [mul_one] at he; exact he -- tune p usage
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by change ‖(_ : tangD n→L[ℝ] ℝ)‖≤_; rw [show (ContinuousLinearMap.apply ℝ ℝ).flip i=i from rfl,one_mul]
 change Jet.Allows p.order (V ∘ M) _ _; rw [he]; apply Jet.Allows.mono ((hφ.smul (1/(b*t^2))).linear Complex.ofRealCLM le_rfl)
 rw [abs_of_pos (by positivity : 0<1/(b*t^2))]; have hx':(2:ℝ)^p.order ≤ a:= pow_le_pow_right₀ (by norm_num) w
 have hK:b*(a*T*(L*t^2))+T ≤ b*t^2*(T*(1+a*L)):=by nlinarith only [mul_le_mul_of_nonneg_right k hx] -- formula? =T add, actually T(1+aL), good
 rw [mul_assoc γ, mul_assoc γ]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg Complex.ofRealCLM) -- tune use op
 apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul hx' hK ht.nonneg (by positivity)) v) (by positivity)); apply le_of_eq; field_simp
end Shield
end YM.CF.XGarden
end
