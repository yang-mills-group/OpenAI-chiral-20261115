import YM.SU5.Six.RawWard
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
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
private def bill (X:Ω→ₗ[ℂ]ℂ)(x:RawCouple K):ℂ:= X x.1.val*X x.2.val
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
lemma ward_preserves_matter (g:Cover→SU.E)(x:Ω)(h:PureMatter K x):PureMatter K (pennant K g x):=by
  let f:=pennant K g x
  obtain ⟨S,v⟩:= findsBay K x
  obtain ⟨m,b⟩:= (separates K S).exists
  obtain ⟨u,e⟩:=scoreTrace g (⟨b⟩:Hosp S (K.c m))
  have he:= pennantLocal K S g v
  change f∈bay K S true at he
  have hp(U V:Fields (K.c m)): f.val m U=f.val m V:=by
    let T:=twist (quantU (tradew (K.c m) u))
    apply T.injective
    have ht:=pennantTrace K S g v m u e
    exact (ht U).symm.trans ((h m _ _).trans (ht V))
  obtain ⟨X,p⟩:= circulation S K ((locates ..).1 he)
  apply (linkIndependent_iff K S ((locates ..).1 he)).mpr
  let T:=tagWord S
  let F (i:Evens S):= Sound.sing K (T i.val)
  let z(i:Evens S):=(X i).val (1,1)
  let V:= ∑ i:Evens S, z i • F i
  have hx: V=f.val:= by
    refine box_ext K S (InTest.sum _ _ fun (i:Evens S) _=> InTest.smul (f:=F i) _ (i.property ▸ Sound.sung K _ (Satin.brand S i.val))) ((locates ..).1 he) ⟨b⟩ ?_
    funext w; rw [hp w (1,1), p]; unfold V; simp_rw [Finset.sum_apply,note_v]
    exact sum_congr rfl fun i _=> (congrArg (z i • ·) (wordIndependent K _ m w (1,1)))
  rw [← hx]
  exact Submodule.sum_mem _ fun i _=>Submodule.smul_mem _ _ (Submodule.subset_span (show _∈_ from ⟨i,rfl⟩))

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
  have ht:∑ i∈I,y i • E (a i)=0:=by simp_rw [←map_smul E, ← map_sum, hx, map_zero]
  refine Eq.trans ?_ ht
  change (∑ i∈I,l i • (E (a i)*E (b i)))=_
  refine sum_congr rfl fun i j=>?_
  simp only [smul_eq_mul,y]; ring
end
-- unique answer at each height
structure Comparison (E X:Dome K→ₗ[ℂ]ℂ) : Prop where
  factors : Factors K X
  link : ∀ x,PureGauge K x→ X x=E x
  matter : ∀ x,PureMatter K x→ X x=E x
variable (E:Dome K→ₗ[ℂ]ℂ)
private lemma splitLin {V W:Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f:V→ₗ[ℂ]W) (h:Function.Surjective f): ∃ F:W→ₗ[ℂ]V,f.comp F=LinearMap.id:=
  LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr h)
theorem comparison_exists (p:E 1=1) : ∃ X, Comparison K E X:=by
  let f:= Finsupp.linearCombination ℂ (combine K)
  let g:= Finsupp.linearCombination ℂ (bill K E)
  obtain ⟨F,u⟩:= splitLin f (surj K)
  let X:=g.comp F
  have ht(i:RawCouple K): X (combine K i) = E i.1.val * E i.2.val:=by
    let x:RawCouple K →₀ℂ:= Finsupp.single i 1
    have hx:f x=combine K i:=by simp [f,x]
    have he:g x= E i.1.val*E i.2.val:=by simp [g,x,bill]
    have hk : f (F (combine K i)-x)=0:=by rw [map_sub, show f (F (combine K i))= combine K i from LinearMap.congr_fun u _, hx,sub_self]
    have h : g (F (combine K i)-x)=0:= wellDefined K E _ hk
    rw [map_sub] at h
    exact (sub_eq_zero.mp h).trans he
  have h(f b:Ω)(r:PureGauge K f)(q:PureMatter K b) : X (f*b)= E f * E b:= ht (⟨f,r⟩,⟨b,q⟩)
  have H(x)(s:PureMatter K x) : X x=E x:=by simpa only [one_mul,p] using h 1 x (pure_unit K).1 s
  have H'(x)(s:PureGauge K x) : X x=E x:=by simpa only [mul_one,p] using h x 1 s (pure_unit K).2
  exact ⟨X,fun f g p q=> by rw [H' f p,H g q]; exact h _ _ p q,H',H⟩
theorem Comparison.unique {X Y}(h:Comparison K E X)(p:Comparison K E Y) : X=Y:=by
  ext x
  obtain ⟨l,rfl⟩:= surj K x
  change X (∑ i∈l.support, l i • combine K i)=Y (∑ i∈l.support,l i • combine K i)
  simp_rw [map_sum,map_smul]
  refine sum_congr rfl fun i _=> ?_
  have H(Q)(s:Comparison K E Q) : Q (combine K i)=E i.1.val*E i.2.val:= by
    rw [combine,s.factors _ _ i.1.property i.2.property,s.link _ i.1.property,s.matter _ i.2.property]
  rw [H _ h,H _ p]
lemma Comparison.matterWard {X}(h:Comparison K E X)(p:MatterWard K E):MatterWard K X:=fun g f q=> by rw [h.matter _ (ward_preserves_matter K g f q),p g f q,h.matter f q]
lemma Comparison.gaugeWard {X}(h:Comparison K E X)(p:GaugeWard K E):GaugeWard K X:=fun g f q=> by rw [h.link _ (pennantPure K g q),p g f q,h.link f q]
lemma Comparison.unit {X} (h:Comparison K E X)(p:E 1=1):X 1=1:=(h.link 1 (pure_unit K).1).trans p
end YM.CF.Buffered.Afterglow.Six
