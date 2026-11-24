import GaugeFieldConstruction.Tarots
/- White charge EOM catalogue -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 70000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Laurent Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
open F03
open TableF TableF.Lenten Haro Housing HushP
local notation "GS"=>SU.group
variable (o:Seat n)(q:Clip)(e: Axis)(f:PlaqAxes)(p:BudgetPoint)(b:ℝ)(C A:tangD n)(Z:SU.group.Color)
lemma turn_flat: ζcone o q p b 1=0:=by
 let D:=Dorm o q; let X:= Turret o (G:=GS) p.threshold; have hx:hue_T D 1=0:=(yuppie o q).2.1; have hz:hue_T X 1=0:=(huppy o p.threshold).2.1; change _ • hue_T D 1-hue_T X 1=_; rw [hx,hz]; simp
lemma crank : fderiv ℝ (ζcone o q p b ∘ increment 1) 0 C A= b* ∑ f∈ slab o,inner ℝ (area f C) (area f A):=by
 let D:=Dorm o q; let X:=Turret o (G:=GS) p.threshold; let Y:= b • (X ∘ increment 1); let V:= hue_T D ∘ increment 1; let H:= hue_T X ∘ increment 1; let F:=ζcone o q p b; have hp:F ∘ increment 1=(fun x=> Y x • V x-H x):=rfl
 have hh: V 0=0:=by unfold V Function.comp; simp; exact (yuppie o q).2.1 -- tune
 have he: Y 0=b:=by change b*(X ∘ _ ) 0=_; rw [show (X∘increment 1) 0=1 from (huppy o p.threshold).1,mul_one]
 have hD:= dorm_π o (1:Config SU.group (More n)) q; have hX:ContDiffAt ℝ ω (X ∘ increment 1) 0:=turret_π o _ _; have hv:ContDiffAt ℝ ω Y 0:=hX.const_smul b
 have hg:=((hv.differentiableAt (by simp)|>.hasFDerivAt).smul ((turn_c _ hD|>.differentiableAt (by simp)).hasFDerivAt)).sub ((turn_c (L:=X) _ hX|>.differentiableAt (by simp)).hasFDerivAt)
 have ht:fderiv ℝ V 0 C A=∑ f∈ slab o, inner ℝ (area f C) (area f A):= (turn_slope (L:=D) 1 hD (yuppie o q).2.1).trans ((yuppie o q).2.2 C A)
 have hz:fderiv ℝ H 0 C A=0:= (turn_slope (L:=X) 1 hX (huppy o p.threshold).2.1).trans ((huppy o p.threshold).2.2 C A); change fderiv ℝ (F ∘ _) _ _ _=_; rw [hp, show fderiv ℝ (fun x=> Y x • V x-H x) 0=_ from hg.fderiv]; change (Y 0 * fderiv ℝ V 0 C A + (fderiv ℝ Y 0 C)*(V 0 A))-fderiv ℝ H 0 C A=_; rw [hh,he,ht,hz]; simp
-- HX slopes
lemma corner_P (i:Seat n)(p':10<(More n).val)(s':separation i o≤1)(Q: Gem)(Z: SU.group.Color): area (i,f) (gateC o t (hem Q Z))=t • (Q.val f.val.1 f.val.2 • Z):=by
 change faceCurl (i,f) (mapCo (plot o (formC (hem Q Z)) t))= _; rw [liaison_h (formC (hem Q Z)) _ _ _ (by omega) (by omega) t,formC_flux]; rfl -- tune ..
lemma corner_R (i:Seat n)(p':10<(More n).val)(s':separation i o≤1)(Q: Sut)(Z:SU.group.Color): area (i,f) (gateT o t (loomH Q Z))= t • faceT (loomH Q Z) f.val.1 f.val.2 (stem o i):=by
 change faceCurl (i,f) (mapCo (plot o (formT (loomH Q Z)) t))= _; rw [liaison_h (formT (loomH Q Z)) _ _ _ (by omega) (by omega) t,formT_flux]
private lemma closer_(v:Axis): separation (o-step v) o≤1:= by
 unfold separation; rw [show o-step v-o=-(step v) by abel,pdist_neg]; exact pdist_step _
lemma far_s(k:Axis)(t:10<(More n).val): stem o o=stem o (o-step k)+step k:=by
 have he: 10*separation (o-step k) o<(More n).val:=by have hx:= closer_ o k; omega
 rw [← stem_f o _ k he t.le]; simp
lemma crust_P (u:10<(More n).val)(Q:Gem)(Y X:SU.group.Color): fderiv ℝ (ζcone o q p b ∘ increment 1) 0 (gateC o p.threshold (hem Q Y)) (at_E o e X)=0:=by rw [crank o q p b,face_hill]; let C:= gateC o p.threshold (hem Q Y); apply mul_eq_zero.mpr; right; apply sum_eq_zero; intro k _; split_ifs <;> simp only [corner_P o _ o u (by simp) Q Y,corner_P o _ _ u (closer_ o _) Q Y,sub_self,inner_zero_left]
abbrev divWhite(Q:Sut):=∑ f:PlaqAxes, ((if e=f.val.1 then Q.val f.val.2 f.val.1 f.val.2 else 0)-(if e=f.val.2 then Q.val f.val.1 f.val.1 f.val.2 else 0))
lemma crust_R (u:10<(More n).val)(Q:Sut)(Y X:SU.group.Color): fderiv ℝ (ζcone o q p b ∘ increment 1) 0 (gateT o p.threshold (loomH Q Y)) (at_E o e X)= b*(divWhite e Q*(p.threshold*inner ℝ Y X)):=by
 rw [crank o q p b,face_hill]; apply congrArg (b * ·); unfold divWhite; rw [sum_mul]; apply sum_congr rfl; intro f _; have hp(k:Axis): area (o,f) (gateT o p.threshold (loomH Q Y))-area (o-step k,f) (gateT o p.threshold (loomH Q Y))= p.threshold • (Q.val k f.val.1 f.val.2 • Y):=by
    rw [corner_R o f o u (by simp),corner_R o f (o-step k) u (closer_ o k), ← smul_sub]; rw [far_s o _ u]; apply congrArg (p.threshold • ·); exact congrFun (face_stepT (loomH Q Y) _ _ k) _
 split_ifs <;> (try simp only [hp,real_inner_smul_left]) <;> ring
abbrev WaxB(x:tangD n):= CupT o e f p (increment 1 x)
private lemma wax_H (i:GateI)(X:tangD n)(d:SU.group.Color)(h:i= KitP e f)(v:HasDerivAt (fun t:ℝ=> πon o i p (increment 1 (t • X))) d 0): fderiv ℝ (WaxB o e f p) 0 X=at_E o e d:=by
 let F:= WaxB o e f p; subst i; refine (Push.side F ((bulb_T o e f p 1).differentiableAt (by simp)) X).unique ?_; exact ((Pudge o e).hasFDerivAt.comp_hasDerivAt _ v)
private lemma stamp (h:b≠0)(A B:tangD n): let Q:= fderiv ℝ (ζcone o q p b ∘ increment 1) 0; let V:=fderiv ℝ (WaxB o e f p) 0; iteratedFDeriv ℝ 2 (markFee o q e f p b ∘ increment 1) 0 ![A,B]=Complex.ofReal ((1/(b*p.threshold))*(Q A (V B)+Q B (V A))):=by
 intro Q V; let T:=p.threshold; let R:= ContinuousLinearMap.apply ℝ ℝ (E:=tangD n) -- tune arg
 let L:ℝ→L[ℝ]ℂ:= (1/(b*T)) • Complex.ofRealCLM
 let F:=ζcone o q p b; let Z:= F ∘ increment 1; let Y:= WaxB o e f p; let C (x):=Z x (Y x)
 have ht:(markFee o q e f p b ∘ increment 1)=L ∘ C:=funext fun i=>by
    change Complex.ofReal (1/(b*T^2)*(T* _))=(1/(b*T):ℝ) • Complex.ofRealCLM (C i); rw [← (Complex.ofRealCLM.map_smul (1/(b*T)) (C i))]; apply congrArg Complex.ofReal; change 1/_ * (T*C i)=1/(b*T)*C i; have hp:T≠0:=p.threshold_pos.ne'; field_simp
 have hv:= zeta_jet o q p b (1:Pane n); have hh:=bulb_T o e f p (1:Pane n); rw [ht,L.iteratedFDeriv_comp_left (f:=C) (show ContDiffAt ℝ ω C 0 from hv.clm_apply hh) le_top]; change L (iteratedFDeriv ℝ 2 C 0 ![A,B])=_; rw [show iteratedFDeriv ℝ 2 C 0 ![A,B]=Q A (V B)+Q B (V A) from hessian_B Z Y _ _ _ R.flip (hv.of_le le_top) (hh.of_le le_top) (by simp [Z]; exact turn_flat ..) (by unfold Y WaxB; simp [flat_cup])]; exact (Complex.ofRealCLM.map_smul (1/(b*T)) _).symm -- arg
lemma prints_wave_a(D:10<(More n).val)(i j:Gem)(v:SU.group.Color)(h:b≠0): iteratedFDeriv ℝ 2 (markFee o q e f p b ∘ increment 1) 0 ![gateC o p.threshold (hem i v),gateC o p.threshold (hem j v)]=0:=by
 rw [stamp o q e f p b h]; let he(k:Gem):= wax_H o e f p _ _ _ rfl (π_sun (o:=o) D k v p (KitP e f)); rw [he i,he j, crust_P o q e p b D, crust_P o q e p b D]; simp
lemma prints_wave_b(D:10<(More n).val)(i:Gem)(j:Sut)(v:SU.group.Color)(p':‖v‖=1)(h:b ≠0): iteratedFDeriv ℝ 2 (markFee o q e f p b ∘ increment 1) 0 ![gateC o p.threshold (hem i v),gateT o p.threshold (loomH j v)]=Complex.ofReal (i.val f.val.1 f.val.2 * divWhite e j):=by
 rw [stamp o q e f p b h]
 have he:= wax_H o e f p _ _ _ rfl (π_sun (o:=o) D i v p (KitP e f)); have hx:= wax_H o e f p _ _ _ rfl (π_shadow (o:=o) D j v p (KitP e f)); rw [he,hx, crust_P o q e p b D, crust_R o q e p b D j v, real_inner_smul_right,real_inner_self_eq_norm_sq, p']; have hp:=p.threshold_pos; rw [show acCue i (KitP e f)=i.val f.val.1 f.val.2 from rfl]; apply congrArg Complex.ofReal; field_simp; ring
lemma prints_zero: markFee o q e f p b 1=0:=by unfold markFee RCore; rw [flat_cup,map_zero]; simp
end Shield
end YM.CF.XGarden
end
