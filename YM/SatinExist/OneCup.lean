import YM.SU5.Six.PairChoices
import YM.SU5.Six.SplitPredict
/-! # CONDITIONAL FORECAST. An explicit projection onto the pure gauge leg. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
namespace OneCup
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
variable (K:Calibration)
local notation "Ω"=> Dome K
/-! The actual marginal comparison is well-defined on the whole Dome, even
though no global regulator probability interpretation is used. -/
private abbrev RawCouple (K:Calibration):= {x:Dome K // PureGauge K x} × {x:Dome K // PureMatter K x}
private def combine (x:RawCouple K):Ω:= x.1.val * x.2.val
private def bill (X:Ω→ₗ[ℂ]ℂ)(x:RawCouple K):Ω:= X x.2.val • x.1.val
private lemma surj : Function.Surjective (Finsupp.linearCombination ℂ (combine K)) := by
  rw [← LinearMap.range_eq_top,Finsupp.range_linearCombination]
  refine top_unique (fun f _=>?_) -- f implicit
  have hp:= fixed_illumined K (precinct K f) (fun _=>1) (fun _ _=>rfl) (precinct_spec K f)
  apply Submodule.span_mono _ hp
  rintro z ⟨f,g,p,q,_,e⟩
  exact ⟨(⟨f,p⟩,⟨g,q⟩),e.symm⟩
section
private lemma dome_eval {I:Type*}(D:Finset I) (a:I→Ω)(r:I→ℂ)(n:Side)(v:Fields (K.c n)) :
    (∑ i∈ D, r i • a i).val n v=∑ i ∈ D, r i • (a i).val n v:= by
  change ( (screenHall K).val (∑ i∈ D,r i • a i) ) n v = _
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply]; rfl
variable (E:Dome K →ₗ[ℂ]ℂ)
private lemma wellDefined (l:RawCouple K→₀ℂ)(p:Finsupp.linearCombination ℂ (combine K) l=0):
    Finsupp.linearCombination ℂ (bill K E) l=0:= by
  let I:=l.support
  let J:Type:=RawCouple K
  let a(i: RawCouple K):=i.1.val
  let b(i: RawCouple K):=i.2.val
  choose D U Z R using fun i:RawCouple K=>show PureGauge K (a i) from i.1.property
  let S:= (I.biUnion D) ∪ I.biUnion (fun i=> precinct K (b i))
  obtain ⟨m,hp⟩:= (separates K S).exists
  let n:=K.c m
  have hc(i)(x:i∈I):D i ⊆ S:= (subset_biUnion_of_mem D x).trans subset_union_left
  have hb(i)(x:i∈I): b i∈ (bay K S true).toSubmodule:= tallerBay K _ _ ((subset_biUnion_of_mem (fun i=>precinct K (b i)) x).trans subset_union_right) (precinct_spec K _)
  have hu (V:PairsC) : (∑ i∈I,(l i* U i V) • b i)=0:= by
    let g:=∑ i∈I,(l i*U i V) • b i
    have hg:g∈(bay K S true).toSubmodule:= Submodule.sum_mem _ fun i x=>Submodule.smul_mem _ _ (hb i x)
    have he: (∑ i∈I,l i • combine K i)=0:=p
    let M:=replant S n V
    have hy(i)(x:i∈I): (a i).val m M= U i V • (1:FC (Single n)):= by
      rw [R]
      let q:LinksC:=onC n M.1; let t:LinksC:=onC n M.2
      exact congrArg (fun c:ℂ=> c • (1:FC _)) (((Z i).mono (hc i x)).locus (q,t) V
        (fun _ j _ => Satin.tail S n ⟨hp⟩ _ _ j) (fun _ j _=> Satin.tail S n ⟨hp⟩ _ _ j))
    apply Subtype.ext; apply box_ext K S ((locates K S true).1 hg) ((locates K S true).1 (bay K S true).zero_mem) ⟨hp⟩
    funext X
    change _ = 0
    rw [dome_eval]
    calc _ = ∑ i∈I,l i • (combine K i).val m M:= by
                     apply sum_congr rfl
                     intro i j
                     change _= l i • ((a i).val m M*(b i).val m M)
                     rw [hy i j,Algebra.smul_mul_assoc,one_mul,smul_smul]
                     exact congrArg ((l i*U i V) • ·) (show _=_ from i.2.property m X M)
         _ = 0:= (dome_eval K I _ l m M).symm.trans (congrArg (fun x:Ω=>x.val m M) he)
  let y (i:RawCouple K):= l i * E (b i)
  have hx : (∑ i∈I,y i • a i)=0:= by
    apply Subtype.ext; funext N T; change _=0
    rw [dome_eval]
    let W:PairsC:=(onC _ T.1,onC _ T.2)
    have he:∑ i∈I,(l i*U i W)*E (b i)=0:=by
      simp_rw [← smul_eq_mul (l _* U _ W),←map_smul E,← map_sum,hu,map_zero]
    calc _ = (∑ i∈I,(l i*U i W)*E (b i)) • (1:FC _):= by
                  rw [sum_smul]; refine sum_congr rfl fun i j=>?_
                  rw [R]; change (l i*E (b i)) • (U i W • (1:FC _))= _; rw [smul_smul,mul_right_comm]
         _=0:=by rw [he,zero_smul]
  change (∑ i∈I,l i • (E (b i) • a i)) = 0
  simp_rw [smul_smul]
  exact hx
private lemma splitLin {V W:Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f:V→ₗ[ℂ]W) (h:Function.Surjective f): ∃ F:W→ₗ[ℂ]V,f.comp F=LinearMap.id:=
  LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr h)
private lemma slice_exists : ∃ L:Ω→ₗ[ℂ]Ω, ∀ g b:Ω,PureGauge K g→PureMatter K b→L (g*b)=E b • g:=by
  let f:= Finsupp.linearCombination ℂ (combine K); let c:= Finsupp.linearCombination ℂ (bill K E)
  obtain ⟨F,h⟩:= splitLin f (surj K)
  refine ⟨c.comp F,fun g b u v=>?_⟩
  let x:RawCouple K:= (⟨g,u⟩,⟨b,v⟩); let y:RawCouple K→₀ℂ:= Finsupp.single x 1
  have hp:f y= g*b:=by simp only [y,f,Finsupp.linearCombination_single,one_smul]; rfl
  have hz:f (F (g*b)-y)=0:=by rw [map_sub,show f (F (g*b))= _ from LinearMap.congr_fun h _,LinearMap.id_apply,hp,sub_self]
  have ht: c (F (g*b)-y)=0:= wellDefined K E _ hz; rw [map_sub] at ht
  change c (F (g*b))= _
  rw [sub_eq_zero.mp ht]; simp only [c,y,Finsupp.linearCombination_single,one_smul]; rfl
noncomputable def slice:Ω→ₗ[ℂ]Ω:= (slice_exists K E).choose
lemma slicer (a b:Ω)(h:PureGauge K a)(p:PureMatter K b): slice K E (a*b)= E b • a:= (slice_exists K E).choose_spec a b h p
private lemma tally (a:Ω)(u:PureGauge K a)(b:Ω): slice K E (a*b)=a * slice K E b := by
  obtain ⟨l,rfl⟩:= surj K b
  change slice K E (a*(∑ i∈l.support, l i • combine K i))= a*slice K E (∑ i∈l.support, l i • combine K i)
  simp_rw [map_sum,mul_sum,map_sum,map_smul, Algebra.mul_smul_comm,map_smul]
  apply sum_congr rfl; intro i _; unfold combine; rw [slicer K E _ _ i.1.2 i.2.2, ←mul_assoc _ i.1.val i.2.val, slicer K E _ _ (gaugePure_mul K u i.1.property) i.2.property, Algebra.mul_smul_comm]
end
variable {K} {E X:Dome K→ₗ[ℂ]ℂ}
lemma slicing (u:Comparison K E X)(b:Dome K): X b= E (slice K E b):=by
 obtain ⟨l,rfl⟩:= surj K b
 change X (∑ i∈l.support, l i • combine K i) = E (slice K E (∑ i∈l.support, l i • combine K i)); simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro i _
 unfold combine; rw [slicer K E _ _ i.1.property i.2.property, u.factors _ _ i.1.property i.2.property, u.link _ i.1.property,u.matter _ i.2.property,map_smul, smul_eq_mul (E _) (E _),mul_comm (E i.1.val)]
lemma slicerLink (E:Dome K→ₗ[ℂ]ℂ)(a b:Dome K)(p: PureGauge K a): slice K E (a*b) = a *slice K E b:= tally K E a p b
lemma slicedLink (b:Dome K): slice K E b ∈ gaugePlane K:=by
 obtain ⟨l,rfl⟩:= surj K b
 change slice K E (∑ i∈l.support, l i • combine K i) ∈_; rw [map_sum]; refine Submodule.sum_mem _ fun i _=>?_
 rw [map_smul]; apply Submodule.smul_mem; unfold combine; rw [slicer K E _ _ i.1.property i.2.property]; exact Submodule.smul_mem _ _ i.1.property
lemma slicing_color (w:MatterWard K E)(g:Cover→SU.E)(b:Dome K): slice K E (pennant K g b)=pennant K g (slice K E b):=by
 obtain ⟨l,rfl⟩:= surj K b
 change slice K E (pennant K g (∑ i∈l.support, l i • combine K i))=pennant K g (slice K E (∑ i∈l.support, l i • combine K i)); simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _=>?_
 unfold combine; rw [map_mul,slicer K E _ _ (pennantPure K _ i.1.property) (ward_preserves_matter K g _ i.2.property),slicer K E _ _ i.1.property i.2.property,map_smul,w g _ i.2.property]
lemma slicing_enclave (w:MatterWard K E)(b:Dome K)(r:b∈enclave K): slice K E b ∈ enclave K:= (colorFixed K).2 (fun g=> (slicing_color w g b).symm.trans (congrArg _ ((colorFixed K).1 r _)))
#print axioms slice
#print axioms slicing_enclave
end OneCup
end YM.CF.Buffered.Afterglow.Six
