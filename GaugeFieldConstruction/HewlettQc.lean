import GaugeFieldConstruction.RhojiQc
/-!
# Blank slot contour
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7200
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ}{S:City}(Y:AreaQc S)
-- Freeze x. marginal
lemma FrezQc (x:E4):ContDiff ℝ ∞ (cons (n:=n) x):=fuse.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)
lemma frozenSubQc (x:E4)(p:Test (n+1)): tsupport (p ∘ cons x) ⊆ cons x ⁻¹' tsupport p:= closure_minimal (fun _ h=>subset_closure h) ((isClosed_tsupport _).preimage (FrezQc x).continuous)
noncomputable def frozenQc (x:E4)(p:Test (n+1)): Test n:= ⟨p ∘ cons x,p.contDiff.comp (FrezQc x),by
   have he:IsCompact (riders '' tsupport p):=(show IsCompact _ from p.hasCompactSupport).image riders.continuous; refine he.of_isClosed_subset (isClosed_tsupport _) (fun y h=>?_); exact ⟨cons x y,frozenSubQc _ _ h,(Prod.mk.inj (helm_consQ x y)).2⟩,fun y h=> tail_in (x:=cons x y) (p.tsupport_subset (frozenSubQc x p h))⟩ -- tune tail eta
lemma frostQuietQc {b}(p:Test (n+1))(x:E4)(h:Works b p 0): Quiet (frozenQc x p) b:=by
 intro y v i; change y i ∉ b.run; simpa [cons] using (h.direct _ (frozenSubQc x p v) i.succ i.succ_ne_zero)
-- unit freezes target x, kernel order becomes name list external. push into z-first. pay affine path T can any centered smooth without shape. 
noncomputable def StandbyQc (t:E4): Points (n+1)→ Points (n+2):=fun y=> rearrange rotor (cons t y)
lemma CostByQc (t:E4)(y:Points (n+1)): helm (StandbyQc t y)=helm y∧ riders (StandbyQc t y)=cons t (riders y):=by
 constructor
 · rw[StandbyQc,tops,Prod.mk.inj (helm_consQ t y)|>.2]
 ext1 i; refine Fin.cases ?_ ?_ i
 · rw [show riders (StandbyQc t y) 0= helm (cons t y) from hop (cons t y)]; simp [helm_head,cons]
 intro j; change (riders (riders (StandbyQc t y))) j=_; rw [StandbyQc,scrap,Prod.mk.inj (helm_consQ t y)|>.2]; simp[cons]
lemma standbyΦQc (t:E4)(i:Axis)(f:Points (n+2)→ℝ)(x:Points (n+1))(h: DifferentiableAt ℝ f (StandbyQc t x)): D (direction 0 i) (f ∘ StandbyQc t) x = D (direction 0 i) f (StandbyQc t x):=by
 let R:= arrangeL rotor (n:=n+2); let L:= fun u:Points (n+1)=> ((t,u):E4×Points (n+1)); let F:E4 × Points (n+1)→L[ℝ] Points (n+2):=fuse.symm.toContinuousLinearMap; let G:=direction (n:=n+1) 0 i
 have hp:DifferentiableAt ℝ L x:=by unfold L; fun_prop
 change fderiv ℝ (f ∘ (R ∘ F ∘ L)) x G= _; rw [fderiv_comp x (show DifferentiableAt ℝ f ((R ∘ F ∘ L) x) from h) (R.differentiableAt.comp x (F.differentiableAt.comp x hp))]; rw [ContinuousLinearMap.comp_apply]; unfold D; congr 1
 rw [fderiv_comp _ R.differentiableAt (F.differentiableAt.comp _ hp), fderiv_comp _ F.differentiableAt hp,R.fderiv,F.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
 have he:fderiv ℝ L x G=(0,G):=by rw [show fderiv ℝ L x = _ from ((show HasFDerivAt L _ x from (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)).fderiv)]; rfl -- tune id
 rw [he]; have ht:F (0,G)=direction (Fin.succ (0:Fin (n+1))) i:=by apply (fuse (n:=n+1)).injective; rw [show fuse (F _)=(0,G) from (fuse (n:=n+1)).apply_symm_apply _]; apply Prod.ext; exact (nope (0:Fin (n+1)) i).symm; exact (on_rail (0:Fin (n+1)) i).symm -- parentheses tune
 rw [ht,← head']; exact directed .. -- lemma
noncomputable def StandQC (t:E4)(K:Payroll (n+1)): Payroll n where
 K j y:= K.K j (StandbyQc t y)
 sm j:= (K.sm j).comp ((arrangeL rotor).contDiff.comp (FrezQc t))
 skew a b x:= by
    change D (direction 0 a) (K.K b ∘ StandbyQc t) x= - D (direction 0 b) (K.K a ∘ StandbyQc t) x
    rw [standbyΦQc,standbyΦQc,K.skew]; exact (K.sm _).differentiable (by simp) _; exact (K.sm _).differentiable (by simp) _
lemma StandiQc (p:Test (n+1))(K:Payroll (n+1))(b:Bulb)(u:Works b p 0)(t:E4)(i j:Axis)(x:Points (n+1)): testcut K p b u.cared i j (StandbyQc t x)=testcut (StandQC t K) (frozenQc t p) b (cares (frostQuietQc p t u)) i j x:=by
 obtain ⟨H,B⟩:= CostByQc t x; rw [testcut_v,testcut_v,H,B]; rfl
include Y

lemma vacantQc (A:SymT)(J:Fin n→l)(p:Test (n+1))(K:Payroll (n+1))(b:Bulb)(h:Works b p 0)(c:Conserves (S.armed (prints A) J)): delta K p b h.cared (S.armed (prints A) (Fathom.add (Empire.one five) J))=0:=by
 let w(i j:Axis):=testcut K p b h.cared i j; let T(i j:Axis):=prints A i j; let s (i j:Axis):=Fathom.add (T i j) J
 let f(i j:Axis)(x:Points (n+2)):= perm rotor (w i j) x*Y.fee (n+2) (Fathom.add (Empire.one five) (s i j)) x
 have hp(i j:Axis): S.armed (prints A) (Fathom.add (Empire.one five) J) i j (w i j)= ∫ x, perm rotor (w i j) x* Y.fee (n+1) (s i j) (riders x):=by
    unfold armed; rw [tagged_cost,← S.rearr rotor,Y.price, rotor_inv, on_labels]; apply integral_congr_ae; filter_upwards[rooted_genericQc (n+2)] with x h; exact congr_arg _ (Y.unit _ (s i j) x h)
 let G(i j:Axis)(x:Points (n+2)):= perm rotor (w i j) x*Y.fee (n+1) (s i j) (riders x)
 have hG (i j):Integrable (G i j):=by
    have ht:Integrable (f i j):=BondCostQc _ _ (Y.reg ..)
    refine ht.congr ?_; filter_upwards [rooted_genericQc (n+2)] with x h; exact congr_arg (fun y=>perm rotor (w i j) x*y) (Y.unit _ (s i j) x h)
 let M(i j:Axis):= G i j ∘ (fuse (n:=n+1)).symm
 have hM(i j):Integrable (M i j):= measuredQc.integrable_comp_of_integrable (hG i j)
 have Φ(i j:Axis): (∫ x,G i j x)=∫ z:E4,∫ x:Points (n+1), M i j (z,x):=((measuredQc.integral_comp (fuse.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding) (G i j)).symm).trans (integral_prod _ (hM i j))
 have hΡ (z:E4)(i j:Axis): (∫ x:Points (n+1), M i j (z,x))=S.armed (prints A) J i j (testcut (StandQC z K) (frozenQc z p) b (cares (frostQuietQc p z h)) i j):=by
    unfold armed; rw[tagged_cost,Y.price]; apply integral_congr_ae; apply Eventually.of_forall; intro x; unfold M G; simp only [Function.comp_apply]; rw [fuse_m, Prod.mk.inj (helm_consQ z x)|>.2, perm_app]; exact congr_arg (fun y:ℂ=> y* Y.fee _ (s i j) x) (StandiQc p K b h z i j x)
 change (∑ i:Axis, ∑ j:Axis, S.armed (prints A) (Fathom.add (Empire.one five) J) i j (w i j))=_ -- tune
 have T'(i): (∑ j:Axis, ∫ z:E4,∫ x:Points (n+1), M i j (z,x))= ∫ z:E4,∑ j:Axis,∫ x:Points (n+1), M i j (z,x):=(integral_finsetSum _ (fun j _=>(hM i j).integral_prod_left)).symm
 simp_rw[hp, show ∀ i j,(∫ x:Points (n+2),perm rotor (w i j) x* Y.fee (n+1) (s i j) (riders x))= _ from Φ, T'] -- tune
 rw[←integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>(hM i j).integral_prod_left))]; simp_rw[hΡ]
 have hw(z:E4):(∑ i: Axis,∑ j:Axis,S.armed (prints A) J i j (testcut (StandQC z K) (frozenQc z p) b (cares (frostQuietQc p z h)) i j))=0 := plume _ _ _ (frostQuietQc p z h) _ c
 refine Eq.trans (integral_congr_ae (g:=fun x:E4=>(0:ℂ)) (Eventually.of_forall hw)) (integral_zero ..)
#print axioms vacantQc
end YM.GaugeFieldConstruction.Ember.Hulse
