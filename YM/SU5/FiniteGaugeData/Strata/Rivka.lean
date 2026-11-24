import YM.SU5.FiniteGaugeData.Strata.Molto
import YM.SU5.FiniteGaugeData.CodaT.Niagara
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.CodaT Eight
/-! # Authorized source for Leaning program. -/
open Fock.Reduction.Drama.Pack Fock.Relief YM.SU5.FiniteGaugeData.Cuprite.Spirit
variable {N M:Side}{S:Finset Cover}{T U:Finset (Site N)}{K:Calibration}{W':W K}{c r s t ε ν H:ℝ}{G Q:Op (Single N)}{n m k d w:ℕ}
namespace Pharos
open Primitives -- tune
open Niagara Chisel Steam Strata
local notation "𝑃"=> plane 3 0
def crown: Walk:= square 0 1
def studio (x:Cover):Finset Cover := (visits x crown).toFinset
lemma reflection_c(x:Cover): studio ((𝑃).motion x)= refract 3 0 (studio x):=by
 let e(y:Cover):= (𝑃).motion y
 have h(i:Axis)(q:i≠3)(x:Cover): e (x+step i)=e x + step i:=by funext j; dsimp only [e]; by_cases H:j=3 <;> simp [fling_move,H,Ne.symm q,q,Ne.symm] -- tune
 have he(x:Cover):x+step 0+step 1+-step 0=x+step 1:=by abel
 unfold e at h
 simp [studio,refract,crown,square,Lattice.visits,he,h 0 (by decide),h 1 (by decide)] -- let abbrevi fail
lemma pilot_c(x z:Cover)(p:z∈studio x): z 3=x 3:=by
 simp [studio,crown,square,visits] at p; rcases p with p|p|p|p|p <;> rw [p] <;> norm_num [step,Pi.single_apply,show (3:Axis)≠0 from by decide,show (3:Axis)≠1 from by decide] -- tune
-- samples
abbrev ψc(x:Cover)(U:Pane N):SU.E:=Lattice.travel (onC N U) x crown
lemma Ψc_eq(x:Cover)(U:Pane N):ψc x U= Lattice.travel U (wrap (More N) x) crown:=(press_face (x,⟨(0,1),by decide⟩) (U,U)).symm
lemma Ψc_rev(x:Cover)(U:Pane N):ψc x (fling 3 0 N U)=ψc ((𝑃).motion x) U:=by
 rw [Ψc_eq,Ψc_eq,fling_eq,travel_pull, show List.map _ _=crown from rfl]; congr 1; exact ((𝑃).anno x) -- tune
-- Pivot (x,0) gauge. independence on distinct slots for this reflection. Require Hosp for union of BOTH studios. h' pole position strictly positive. no support drift.
local notation "μ"=> SU.group.probHaar
local notation "νᵢ"=> Wilson.prior SU.group (More N)
local notation "T" U:max=> (matter U)
-- deterministic high-order interface: pull σ along measure preserving Haar update. Keep telescope opaque.
private lemma Valentine (rot:SU.E→Pane N→Pane N)(Q:Pane N→ℂ)(h:MeasurableSet {x:SU.E× Pane N| (Q∘ (fun w:SU.E × Pane N=> rot w.1 w.2)) x ≠0})(p:∀ v,∀ᵐ u∂μ,Q (rot u v)≠0):∀ᵐ u∂μ,∀ᵐ v∂νᵢ,Q (rot u v)≠0 := (Measure.ae_ae_comm (p:=fun u x=> Q (rot u x)≠0) («μ»:=μ) (ν:=νᵢ) h).mpr (Eventually.of_forall p)
private lemma gapY{I:Type}[Fintype I][DecidableEq I](A:Op I)(g:SU.E):∀ᵐ u∂μ,Seal A (u*g) ≠0 :=by
 let Ui:= (measurePreserving_mul_right (μ) g); have ht:∀ᵐ z∂μ, Seal A z ≠0:=Strata.tent (Seal A) (Seal.legal A) (Seal.hotel A) (Seal.free A); let S(z:SU.E):= Seal A z ≠0; exact Ui.quasiMeasurePreserving.ae (p:=S) ht
private lemma Heal{I:Type}[Fintype I][DecidableEq I](A:Op I)(g:SU.E):Seal A g≠0 → IsUnit (1-foldMo A g):=fun p=>(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr p)
private lemma recolor (rot:SU.E→Pane N→Pane N)(Q:Pane N→ℂ)(hp:∀ᵐ u∂μ,∀ᵐ v∂νᵢ,Q (rot u v)≠0)(p:∀ i y, rot i (rot i⁻¹ y)=y)(L:∀ u,MeasurePreserving (rot u) νᵢ νᵢ):∀ᵐ y∂νᵢ,Q y≠0:=by
 obtain ⟨u,t⟩:= hp.exists; filter_upwards [(L u⁻¹).quasiMeasurePreserving.ae t] with Y H; exact p u Y ▸ H
set_option maxRecDepth 3500 in
lemma much_c {x:Cover}(h:0<x 3)(p:Hosp (studio x ∪ refract 3 0 (studio x)) N): ∀ᵐ U∂νᵢ, IsUnit (1-foldMo (CF.cc (T (ψc x (fling 3 0 N U))).val) (ψc x U)):=by
 let W:= More N; let Ψ(x:Cover):= wrap W x; let y:= (𝑃).motion x; let z:= Ψ x; let S:=studio x ∪ refract 3 0 (studio x); let V:= Ψ y; let U:Edge (Site W):= (z,0)
 have he :∀ y'∈studio y,z ≠ Ψ y':=by
    intro y' p' hh; have hS0 : x∈ S:= mem_union_left _ (by unfold studio; simp [crown,square,visits]); have hS:y'∈ S:=mem_union_right _ (by rw [← reflection_c]; exact p'); have hx: y 3=-(x 3):=(by simp [y,fling_move]); have hk:=pilot_c y y' p'; have hg:=congrFun (p.seat_ hS0 hS hh) 3; omega
 let spin(u:SU.E)(x:Pane N): Pane N:= Function.update x U (u*x U)
 have hr(u:SU.E): MeasurePreserving (spin u) νᵢ νᵢ:=by
    apply Fixed.Pivots.update_preserve; · exact measurable_const.mul (measurable_pi_apply U)
    intro v; simp_rw [Function.update_self]; exact measurePreserving_mul_left μ u
 have hM:Continuous fun x: SU.E ×Pane N=> spin x.1 x.2:=by
    apply continuous_pi; intro i; by_cases p:i=U; · simp_rw [p,spin,update_self]; fun_prop
    simp_rw [spin, Function.update_of_ne p]; fun_prop
 let A(x':Pane N):= cc (T (ψc y x')).val; let G(x':Pane N):= ψc x x'; let L(x':Pane N):= Seal (A x') (G x')
 have hm(x:Cover): Continuous (ψc x (N:=N)):=by simp_rw [funext (Ψc_eq x (N:=N))]; exact Wilson.continuous_travel .. -- tune
 have hl: Continuous L:=by
    apply Continuous.matrix_det; apply Continuous.sub continuous_const; apply continuous_matrix; rintro ⟨i,j⟩ ⟨u,v⟩; exact (continuous_star.comp ((matter_cont.comp (hm y)).matrix_elem i u)).mul ((matter_cont.comp (hm x)).matrix_elem j v)
 have hα(u:SU.E)(Y:Pane N): A (spin u Y)=A Y:=by
    have hq: V+step (1:Axis) = Ψ (y+step 1):=by unfold Ψ V; rw [map_add, wrap_step]
    have hw: V ≠ z:=Ne.symm (he y (by simp [studio,crown,square,visits])); have hh: V+step (1:Axis) ≠ z:=by rw [hq]; refine Ne.symm (he _ (by simp [studio,crown,square,visits]; right; right; right; left; abel))
    unfold A; rw [Ψc_eq,Ψc_eq]; unfold spin crown; rw [Fixed.Pivots.square_formula SU.group,Fixed.Pivots.square_formula SU.group]; change cc (T (update Y U _ (V,0)*update Y U _ (V+step 0,1)*(update Y U _ (V+step 1,0))⁻¹*(update Y U _ (V,1))⁻¹)).val=_; have h₁ : ∀ v:Seat N, (v,(1:Axis)) ≠ U:= fun i=> fun e=> (by decide:(1:Axis) ≠ (0:Axis)) (congrArg Prod.snd e) -- tune step Axis One
    simp_rw [Function.update_of_ne (show (V,(0:Axis)) ≠ U from by simp [U,hw]),Function.update_of_ne (show (V+step 1, (0:Axis))≠ U from by simp [U,hh]), Function.update_of_ne (h₁ _)]; rfl
 have hβ(u:SU.E)(Y:Pane N): G (spin u Y)=u*G Y:=by
    have hw: z+step (1:Axis)≠ z:=by
       intro H; have hh : (1:Per (More N))=0:=(by simpa using congrFun H 1); haveI: Fact (1<(More N).val):= ⟨by change 1 < N.val*2; have he:=N.property; exact lt_of_lt_of_le one_lt_two (le_mul_of_one_le_left (by decide : (0:ℕ)≤2) he)⟩; exact one_ne_zero hh
    unfold G; rw [Ψc_eq,Ψc_eq]; unfold crown spin; rw [Fixed.Pivots.square_formula SU.group,Fixed.Pivots.square_formula SU.group]; have h₁ : ∀ v:Seat N, (v,(1:Axis)) ≠ U:= fun i=> fun e=> (by decide:(1:Axis) ≠ (0:Axis)) (congrArg Prod.snd e);
    change update Y U _ U * update Y U _ (z+step 0,1) * (update Y U _ (z+step 1,0))⁻¹*(update Y U _ (z,1))⁻¹=_; simp_rw [Function.update_self,Function.update_of_ne (show (z+step 1, (0:Axis))≠ U from by simp [U,hw]), Function.update_of_ne (h₁ _),mul_assoc]; rfl
 have hJ:∀ᵐ u∂μ,∀ᵐ x∂νᵢ,L (spin u x)≠0:=by
    
    let Q:= L ∘ fun x:SU.E × Pane N=> spin x.1 x.2
    have h':Measurable Q:= (hl.comp hM).measurable
    have hm:MeasurableSet {x:SU.E ×Pane N| Q x ≠0}:=h' (measurableSet_singleton 0).compl
    refine Valentine spin L hm fun v=>?_
    unfold L; simp_rw [hα,hβ]; exact gapY _ _
 have hc(u:SU.E)(Y:Pane N):spin u (spin u⁻¹ Y)=Y:=by funext i; by_cases p:i=U<;> simp [spin, Function.update_of_ne,p]
 filter_upwards [recolor spin L hJ hc hr] with Y H
 rw [Ψc_rev]; exact Heal (A Y) (G Y) H
#print axioms much_c
end Pharos
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
