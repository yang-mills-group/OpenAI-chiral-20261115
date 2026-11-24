import GaugeFieldConstruction.Lozenges
import GaugeFieldConstruction.Rinket
/- GE bare jet on Root -/
set_option autoImplicit false
set_option maxHeartbeats 110000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Laurent Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Work Tensor
open Exterior
variable {E F Z:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup Z][NormedSpace ℝ Z] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
open F03
variable (q:Clip)
private lemma credit_deriv (f:Face (Per n))(A:Directions G n): HasDerivAt (fun i:ℝ=> G.mat (faceValue (increment 1 (i • A)) f)) (G.colorMat (faceCurl f (mapCo A))) 0:=by
 have he:= face_deriv f (mapCo A); simp_rw [show ∀ t:ℝ,t • mapCo A=mapCo (t • A) from fun t=>rfl,represent_p] at he; exact he
lemma credit_rule (f:Face (Per n))(A:Directions G n): faceCurl f (mapCo A)= A (edges f 0) + A (edges f 1)-A (edges f 2)-A (edges f 3):=by
 ext j; unfold faceCurl dColor; dsimp only; change (Exterior.d 1 n*ᵥ Exterior.parts G 1 (mapCo A) j) (f.1,plaquette f.2)=_; rw [d_plaquettes]; unfold Exterior.parts mapCo; simp_rw [← coord_map,Equiv.symm_apply_apply]; change _= A _ j+A _ j-A _ j-A _ j; simp only [edges, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]; simp -- abel after
 abel
lemma priced0 (f:Face (Per n)): let F (i:Directions G n):= G.price (faceValue (increment 1 i) f)
 F 0=0∧ fderiv ℝ F 0=0∧∀ i j, iteratedFDeriv ℝ 2 F 0 ![i,j]=inner ℝ (faceCurl f (mapCo i)) (faceCurl f (mapCo j)):=by
 intro F; refine hessian_of_limit ((price_smooth ((mat_face_inc f 1).contDiffAt)).of_le le_top) ?_ ?_ ?_ -- tune ambiguity
 · intro i; rw [real_inner_self_eq_norm_sq]; exact price_limit (V:=fun t:ℝ=> faceValue (increment (1:Config G n) (t • i)) f) (by simp [face_one]) (credit_deriv f i)
 · intro i j k; rw [show faceCurl f (mapCo (i+j))= _ from (show faceCurl f (mapCo (i+j))=faceCurl f (mapCo i)+faceCurl f (mapCo j) from (by rw [credit_rule,credit_rule,credit_rule]; simp only [Pi.add_apply]; abel)), inner_add_left]
 intro i j; exact real_inner_comm ..
local notation "GS"=> SU.group
lemma loads_E(q: Clip)(f:Face (Per n))(X:E→ Config SU.group n)(h:ContDiffAt ℝ ω (fun i=>SU.group.mat (faceValue (X i) f)) 0): ContDiffAt ℝ ω (fun i:E=> coinF q (faceValue (X i) f)) 0:=by
 let F(i:E):= faceValue (X i) f; let S(i:E):= Reef.qG (F i)
 have ht(U:E→SU.group.El)(p:ContDiffAt ℝ ω (fun i=> SU.group.mat (U i)) 0): ContDiffAt ℝ ω (energyF q ∘ U) 0:=by
    have hh:ContDiffAt ℝ ω (Quad.surplusMat ∘ fun i=> SU.group.mat (U i)) 0:=(Quad.surplusMat_diff (G:=GS)).contDiffAt.comp 0 p -- tune
    apply ContDiffAt.sub (price_smooth p); refine contDiffAt_const.mul (?_ : ContDiffAt ℝ ω (fun i=> surplus (G:=GS) (U i)) 0); simpa only [Function.comp_def,Quad.surplus_actual] using hh
 exact ((ht F h).add (ht S (Reef.chill.toContinuousLinearMap.contDiff.contDiffAt.comp _ h))).div_const 2
lemma bankShape(q:Clip)(f:Face (Per n)) : let F:=fun i:Directions GS n=> coinF q (faceValue (increment 1 i) f)
 F 0=0∧fderiv ℝ F 0=0∧∀ i j,iteratedFDeriv ℝ 2 F 0 ![i,j]=inner ℝ (faceCurl f (mapCo i)) (faceCurl f (mapCo j)):=by
 intro F; let W(i: Directions GS n):= faceValue (increment 1 i) f; let Y(i):= SU.group.price (W i); have ⟨hx,hs,hv⟩:= priced0 (G:=GS) f
 let S(i):= Reef.qG (W i); let a:=Design.bulk q; let H(x:SU.group.El):=surplus x
 have he : F=Y- ((a/2) • ((H ∘ W)+(H ∘ S))):= funext fun i=>by change (_+_)/2=_ - (a/2)*(_ + _); unfold energyF; rw [Reef.cold]; change _=SU.group.price _ - (Design.bulk q /2)*(_+_); change _=SU.group.price _ - (Design.bulk q /2)*(surplus (G:=GS) (faceValue (increment 1 i) f)+surplus (G:=GS) (Reef.qG (faceValue (increment 1 i) f))); ring
 have hx':ContDiffAt ℝ ω (fun i=> SU.group.mat (W i)) 0:=(mat_face_inc f _).contDiffAt; have hu:ContDiffAt ℝ ω (fun i=> SU.group.mat (S i)) 0 := Reef.chill.toContinuousLinearMap.contDiff.contDiffAt.comp _ hx'; have hW: W 0=1:=by simp [W,face_one]
 have hh:ContDiffAt ℝ ω (H∘W) 0:=(residual_smooth f 1).contDiffAt; have hk:ContDiffAt ℝ ω (H ∘ S) 0:=by
    have hq:= Quad.surplusMat_diff.contDiffAt.comp 0 hu; apply hq.congr_of_eventuallyEq; exact Eventually.of_forall fun i=> (Quad.surplus_actual _).symm
 have he' (i:ℕ)(p:i≤4):iteratedFDeriv ℝ i F 0=iteratedFDeriv ℝ i Y 0:=by
    rw [he,iteratedFDeriv_sub_apply (show ContDiffAt ℝ i Y 0 from (price_smooth hx').of_le le_top) (show ContDiffAt ℝ i ((a/2) • ((H∘W)+(H∘S))) 0 from ((hh.add hk).const_smul (a/2)|>.of_le le_top)),iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ i ((H∘W)+(H∘S)) 0 from (hh.add hk).of_le le_top),iteratedFDeriv_add_apply (hh.of_le le_top) (hk.of_le le_top), show iteratedFDeriv ℝ i (H∘W) 0=0 from surplus_jet _ hW hx' _ (by omega), show iteratedFDeriv ℝ i (H ∘ S) 0=0 from surplus_jet _ (by simp [S,hW]) hu _ (by omega),add_zero, smul_zero, sub_zero]
 refine ⟨?_,?_,fun i j=> (congrArg (fun u:Tensor.T _ _ 2=> u ![i,j]) (he' 2 (by decide))).trans (hv i j)⟩
 · change Y 0=0 at hx; simpa only [hx,iteratedFDeriv_zero_apply] using congrArg (fun u:Tensor.T (Directions GS n) _ 0=> u (fun i=> Fin.elim0 i)) (he' 0 (by decide))
 have hp:= congrArg norm (he' 1 (by decide)); rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one,show fderiv ℝ Y 0=0 from hs,norm_zero] at hp; exact norm_eq_zero.mp hp
end Shield
end YM.CF.XGarden
end
