import Mathlib.Analysis.InnerProductSpace.TensorProduct
import YM.SU5.Six.RawWard
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
namespace Gourd
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
private lemma wellDefined (Y:Ω→ₗ[ℂ]ℂ) (l:RawCouple K→₀ℂ)(p:Finsupp.linearCombination ℂ (combine K) l=0):
    Finsupp.linearCombination ℂ (fun i:RawCouple K=>Y i.1.val*E i.2.val) l=0:= by
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
  have ht:∑ i∈I,y i • Y (a i)=0:=by simp_rw [←map_smul Y, ← map_sum, hx, map_zero]
  refine Eq.trans ?_ ht
  change (∑ i∈I,l i • (Y (a i)*E (b i)))=_
  refine sum_congr rfl fun i j=>?_
  simp only [smul_eq_mul,y]; ring


variable {D:Type} [AddCommGroup D] [Module ℂ D]
lemma splitLin {V W:Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f:V→ₗ[ℂ]W) (h:Function.Surjective f): ∃ F:W→ₗ[ℂ]V,f.comp F=LinearMap.id:=
  LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr h)
lemma liftLin {V W:Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f:V→ₗ[ℂ]W) (h:f.ker=⊥): ∃ F:W→ₗ[ℂ]V,F.comp f=LinearMap.id:=
  LinearMap.exists_leftInverse_of_injective f h

theorem lift_split {α:Type}(φ:Ω→Ω→D)
    (χ:α→D→ₗ[ℂ]ℂ)
    (sep:∀x, (∀ i, χ i x=0) → x=0)
    (rel:∀i, ∃ A B:Ω→ₗ[ℂ]ℂ,∀ a b, χ i (φ a b)= A a*B b) :
 ∃ ψ:Ω→ₗ[ℂ]D, ∀ f g, PureGauge K f→PureMatter K g→ψ (f*g)=φ f g:=by
-- if p for all φ=f ..* then for all φ by finite-dimensionality.
 let f:= Finsupp.linearCombination ℂ (combine K)
 let g:= Finsupp.linearCombination ℂ (fun i:RawCouple K=>φ i.1.val i.2.val)

 obtain ⟨F,u⟩:= splitLin f (surj K)
 let X:=g.comp F
 have hw(l:RawCouple K→₀ℂ)(h:f l=0):g l=0:=by
    apply sep; intro i; obtain ⟨A,B,r⟩:=rel i
    change χ i (∑ j∈l.support, l j • φ j.1.val j.2.val)=0
    simp_rw [map_sum,map_smul,r]
    exact wellDefined K B A l h
 have ht(i:RawCouple K): X (combine K i) = φ i.1.val i.2.val:=by
    let x:RawCouple K →₀ℂ:= Finsupp.single i 1
    have hx:f x=combine K i:=by simp [f,x]
    have he:g x= φ i.1.val i.2.val:=by simp [g,x]
    have hk : f (F (combine K i)-x)=0:=by rw [map_sub, show f (F (combine K i))= combine K i from LinearMap.congr_fun u _, hx,sub_self]
    have h := hw _ hk
    rw [map_sub] at h
    exact (sub_eq_zero.mp h).trans he
 exact ⟨X, fun a b p q=>ht ⟨⟨a,p⟩,⟨b,q⟩⟩⟩

open scoped TensorProduct

variable {H:Type}[NormedAddCommGroup H][InnerProductSpace ℂ H]
local notation "T"=> (H ⊗[ℂ] H)
private abbrev Quad(B:Type):= B × B × B × B
local notation "C"=> (T →L[ℂ] T)

def pairing {G:Type}[NormedAddCommGroup G][InnerProductSpace ℂ G] (x y:G) : (G→L[ℂ]G)→ₗ[ℂ]ℂ where
 toFun a:= inner ℂ x (a y)
 map_add' _ _:=inner_add_right ..
 map_smul' _ _:=inner_smul_right ..
private def check (p:Quad H) : (T→L[ℂ]T)→ₗ[ℂ]ℂ :=
  pairing (p.1 ⊗ₜ p.2.1) (p.2.2.1 ⊗ₜ p.2.2.2)
private lemma separates (F:C) (h:∀ p, check p F=0): F=0:=by
 have ht(x y:T):inner ℂ x (F y)=0:=by
    induction y using TensorProduct.induction_on with
    | zero=>simp
    | tmul a b=>
      induction x using TensorProduct.induction_on with
      | zero=>simp
      | tmul c d=>exact h (c,d,a,b)
      | add x y h t=>rw [inner_add_left,h,t,zero_add]
    | add x y u v=>rw [map_add,inner_add_right,u,v,zero_add]
 exact ContinuousLinearMap.ext (fun y=>show F y=0 from (inner_self_eq_zero (𝕜:=ℂ) ..).mp (ht _ y))


theorem request ( f:Ω→ₗ[ℂ](H→L[ℂ]H) ) :
  ∃ g:Ω→ₗ[ℂ] C,∀ a b, PureGauge K a→PureMatter K b→ g (a*b)=TensorProduct.mapL (f a) (f b):=
 lift_split K (fun a b=> TensorProduct.mapL (f a) (f b)) check separates
   (fun p=> ⟨(pairing p.1 p.2.2.1).comp f,(pairing p.2.1 p.2.2.2).comp f,fun _ _=> rfl⟩)
