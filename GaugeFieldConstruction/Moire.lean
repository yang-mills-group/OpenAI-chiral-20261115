import GaugeFieldConstruction.Pendant
import GaugeFieldConstruction.Melo
import GaugeFieldConstruction.Bower
import GaugeFieldConstruction.Prairie
import GaugeFieldConstruction.Lepta
import GaugeFieldConstruction.Retic
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Prism Tap FlightFlux TableF Boom Axon
open Lenten.ModuleB Flot Taxi
open Planned.PrimaryIntegral295
variable {N P B J : Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S} {Xs:GramM (mid N B)}{Y:GramM (mid P B)}(p:BudgetPoint){s ξ μ k x σ C:ℝ}{R:Patch}
abbrev Manor (p:BudgetPoint)(o:Seat N)(X:Support (More N))(v:ℕ):=brim p v X • silo p o
lemma reprV (o:Seat N)(X:Support (More N))(v:ℕ)(g:o∈X)(t:tangD N): p.threshold • lineP p o X v (Manor p o X v t)= highlight X t:=by
 rw [ContinuousLinearMap.smul_apply,map_smul,leg_r p o X v g]; unfold rodV; simp only [ContinuousLinearMap.comp_apply, smul_apply,trench,no_w,smul_inv_smul₀ p.threshold_pos.ne']
lemma manor_v (o:Seat N)(X:Support (More N))(v:ℕ)(g:o∈X)(t:tangD N)(e:p.dirBound o t): ‖Manor p o X v t‖≤ brim p v X:=by
 rw [ContinuousLinearMap.smul_apply,norm_smul,Real.norm_of_nonneg (zero_le_one.trans (verge_p p o X v g))]; refine mul_le_of_le_one_right (zero_le_one.trans (verge_p p o X v g)) ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i=>?_))
 change ‖(Lyre.width p o i)⁻¹ • t i‖ ≤_; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (Lyre.width_pos ..)).le, inv_mul_le_iff₀ (Lyre.width_pos ..),mul_one]; exact e i
lemma highlight_A (X:Support (More N))(W:tangD N): Agrees X W (highlight X W):=by
 intro i v g; have ht:pinPos i⊆ X:=insert_subset v (singleton_subset_iff.mpr g); simp only [highlight,ContinuousLinearMap.pi_apply, if_pos ht]; rfl
lemma highlight_D (X:Support (More N))(o:Seat N)(U:tangD N)(h:p.dirBound o U):p.dirBound o (highlight X U):=by
 intro i; unfold highlight; simp only [ContinuousLinearMap.pi_apply]; split; · exact h i
 rw [ContinuousLinearMap.zero_apply,norm_zero]; exact (Lyre.width_pos ..).le
lemma Creep (U:tangD N)(o:Seat N)(v:ℕ)(h:p.dirBound o U)(k:p.power=3):Carrier.Carries (W_form _ _ (Tale.curt v o U) o) 3 p.threshold:=by
 apply Lifter o _ p.threshold_pos.le; intro i; rw [Tale.curtP]; split; · rw [←k]; exact h i -- separation oriented?
 rw [norm_zero]; exact mul_nonneg p.threshold_pos.le (Heir.spine_pos ..).le
open TableF Carrier
omit p
variable {i:Roc (mid P B)} {W:tangD (mid N B)→ tangD (mid P B)}
abbrev Arrow (i:Roc (mid P B))(F:Wheel Axis SU.group.Color): Wheel Axis SU.group.Color:=risen T.R.A0 (Xs.p.threshold • F) (Lattice.lift (S.ratio.residue i.1.val.1))
abbrev cog (Y:Support (Domain N B))(x:ℝ)(v:tangD (mid N B)):= (fderiv ℝ (W∘ (Bindδ (temp x) (S.ratio.parent i.1.val.1) Xs.p Y (radiusB x))) 0) v
-- strip & reach conditions as stored
structure Gatehouse(Xs: GramM (mid N B))(Y:GramM (mid P B))(σ C:ℝ)(x:ℝ) (M:ℕ)(t: Tube SU.group S): Prop where
 rate:0<σ
 paid:0≤ C
 account:t.R.A0.strip σ C
 head:Xs.p.power=3
 tempo:Xs.p.threshold=temp x
 door:M≤ Heir.reach x
 markA:M+1 ≤1000*radiusB x
 range:2*M<(Domain N B).val
variable {m:ℕ}(hB:Beacon (R:=R) (T:=T) (x:=x) (Xs:=Xs) (Y:=Y) 1 i s W 1 ξ)
include hB
lemma begin_X : ‖W 0‖ ≤ ξ * Y.p.threshold:=by
 have he:=(hB.full 0 (by omega) Fin.elim0 (fun i=> Fin.elim0 i)).2; rw [(EventuallyEq.iteratedFDeriv ℝ (Siete.sphere_pin (m:=mid N B) _ _) 0).eq_of_nhds] at he; simpa only [iteratedFDeriv_zero_apply,map_zero,sub_zero] using he -- tune implicit n.more/m
variable (A:Support (Domain N B))(hA:A=halo (1000*radiusB x) {S.ratio.parent i.1.val.1})(g:Gatehouse Xs Y σ C x m T)(u:i.1.val.2 ⊆ halo 24 {i.1.val.1})
include g hA u
abbrev nodalK (L:Side) := (96+4*L.val:ℕ)
abbrev leadDue(ξ σ C:ℝ)(P Q:BudgetPoint)(L:Side)(m:ℕ):ℝ:= ξ+ 2*P.threshold/Q.threshold*(Real.exp (-(σ/2)*m)*(4*C*(1+(nodalK L:ℝ))^3*Real.exp (σ/2 * (nodalK L:ℝ))*widthCost (σ/2) 3))
-- at masked direction undo brim. No Θ choice in stencil test.
lemma arrowing (F:Wheel Axis SU.group.Color)(hr: Carrier.Carries (Function.swap F) 3 1)(hi:Xs.p.dirBound (S.ratio.parent i.1.val.1) (plot (S.ratio.parent i.1.val.1) F Xs.p.threshold)) (j:Bond (Domain P B))(hj:j.1∈i.1.val.2): let r:= plot (S.ratio.parent i.1.val.1) F Xs.p.threshold; ‖cog (Xs:=Xs) (i:=i) (S:=S) (W:=W) A x (Manor Xs.p (S.ratio.parent i.1.val.1) A (radiusB x) r) j- camW i.1.val.1 (Arrow (T:=T) (Xs:=Xs) i F) j‖ ≤ leadDue ξ σ C Xs.p Y.p S.ratio.count m* Y.p.threshold:=by
 let X:=Xs.p; let I:= S.ratio.parent i.1.val.1; let o:=i.1.val.1; let L:= S.ratio.count; intro r
 let z:= Manor X I A (radiusB x) r; let D:= highlight A r; let C':= Tale.curt (Heir.reach x) I D; let V:= W_form _ _ C' I; let U:= Function.swap (X.threshold • F); let g0:= Route_home S T ⟨σ,C,g.rate,g.account⟩ C' o
 let t0:= Bindδ (temp x) I X A (radiusB x); let v:= cog (Xs:=Xs) (S:=S) (i:=i) (W:=W) A x z; have hp: I∈A:=hA.symm ▸ halo_subset _ _ (mem_singleton_self _)
 have he: v=(fderiv ℝ W 0) D:=by
    have hy:t0 0= 0:= t0.map_zero; unfold v cog; change fderiv ℝ (W∘ t0) 0 z= _; rw [fderiv_comp 0 ?_ t0.differentiableAt, ContinuousLinearMap.fderiv, hy]; swap; · rw [hy]; exact hB.touch.smooth.differentiableAt (by norm_num)
    have ht:t0 z =D:=by rw [show t0=(temp x) • lineP X I A (radiusB x) from rfl, ContinuousLinearMap.smul_apply,←g.tempo]; exact reprV X _ _ _ hp _ -- tune rw dependence
    rw [ContinuousLinearMap.comp_apply,ht]
 have hμ:D= highlight A r:=rfl
 have hF:X.dirBound I D:= highlight_D _ _ _ _ hi
 have hv := (hB.full 1 (by omega) (fun _=>D) (fun i=>hF)).2
 have hm': ‖v-Heir.route T C'‖ ≤ ξ * Y.p.threshold:=by
    rw [(EventuallyEq.iteratedFDeriv ℝ (Siete.sphere_pin (m:=mid N B) I _) 1).eq_of_nhds, iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,ContinuousLinearMap.fderiv] at hv; rw [he]; exact hv
 have hT': Carries V 3 X.threshold:= Creep _ _ _ _ hF g.head
 have hg:Carries U 3 X.threshold:=by
    refine ⟨X.threshold_pos.le,fun i v=>?_⟩; change ‖X.threshold • F v i‖ ≤_; rw [norm_smul,Real.norm_of_nonneg X.threshold_pos.le]; exact mul_le_mul_of_nonneg_left ((hr.2 i v).trans_eq (one_mul _)) X.threshold_pos.le
 have hh(j:Cover)(v:lateral j ≤ m): V j=U j:=by
    funext k; let t:= I+wrap (Domain N B) j
    have he:separation I t ≤ m:=by unfold t separation; rw [show I-(I+wrap _ j)=-wrap _ j from (by abel), pdist_neg]; exact (wrap_month _).trans v
    have hδ:t∈ A:= hA.symm ▸ (halo_spec.mpr ⟨I,mem_singleton_self _, he.trans (by have he:=g.markA; omega)⟩)
    have hV: t+step k∈ A:= hA.symm ▸ (halo_spec.mpr ⟨I,mem_singleton_self _, (separation_triangle I t _).trans ((Nat.add_le_add he (Work.E01.sep_step_le t k)).trans g.markA)⟩)
    change C' (t,k)= _; unfold C'; rw [Tale.curtP,if_pos (he.trans g.door),hμ,← highlight_A A r _ hδ hV]; change X.threshold • F k (FlightFlux.stem I t)= _; rw [show FlightFlux.stem I t=j from lift_path (add_sub_cancel_left ..) (by have he:=g.range; omega)]; rfl -- tune add_sub_cancel
 let x₀:= FlightFlux.stem o j.1; let x':= x₀ +Lattice.lift (S.ratio.residue o); let q₀:= nodalK L
 have hx: lateral x' ≤ q₀:=by
    have hV:=u hj; obtain ⟨p,a,b⟩:=halo_spec.mp hV; rw [mem_singleton.mp a] at b; refine (lateral_add ..).trans (Nat.add_le_add ?_ (lift_moon _)); have he:separation j.1 o ≤24:= (separation_comm ..).trans_le b; exact (stem_t o j.1).trans (by omega)
 have hz:= lip_equ x' g.rate g.paid g.account hT' hg hh j.2; have hx: ((size x':ℕ):ℝ)≤ q₀:= by exact_mod_cast hx
 let Φ:= Heir.route T C'
 have hδ: Φ j= applyLine T.R.A0 V x' j.2:= by
    rw [show applyLine T.R.A0 V x' j.2=W_form _ _ Φ o x₀ j.2 from (congrFun (congrFun g0 x₀) j.2).symm]; unfold W_form; rw [show wrap _ x₀=_ from wrap_lift _,add_sub_cancel]
 apply (norm_sub_le_norm_sub_add_norm_sub (v j) (Φ j) _).trans
 have ht:‖v j-Φ j‖ ≤ ξ * Y.p.threshold:= (norm_le_pi_norm (v-Φ) j).trans hm'
 apply (add_le_add ht (hδ.symm ▸ hz)).trans -- ht syntax Sub.Real
 have hh:0 <Y.p.threshold:=Y.p.threshold_pos
 unfold leadDue; rw [add_mul ξ]; apply add_le_add_right; let d:= (1+(nodalK L:ℝ))^3; let t:= Real.exp (σ/2*(nodalK L:ℝ)); let T1:= Real.exp (-(σ/2)*m); let e:= widthCost (σ/2) 3; let H:=T1*(4*C*d*t*e)
 have ht := g.paid; have hc:=g.rate; have he:=X.threshold_pos; have hz: 0≤e:= zero_le_one.trans (widthCost_ge (half_pos hc) _)
 apply le_trans (b:= (X.threshold+X.threshold)*H); unfold H t d; unfold liftCost; unfold e at hz; gcongr
 change _ ≤ 2*X.threshold/Y.p.threshold*H*Y.p.threshold; exact le_of_eq (by field_simp; ring)
end
end YM.CF.Oath
end
