import YM.CF.BPress.Envelope
import YM.CF.BPress.Palmer.Graph
/-! block-specific readings. Independence version with π measures NOT necessarily probabilities on the excited variables. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Contour
open RG Wilson Lattice Finset MeasureTheory Function Palmer
open scoped Classical Topology BigOperators ENNReal
variable {Y I: Type*}{Φ:Y→Type*}[DecidableEq Y]{L:Type*}
def ScopedB (F:(∀ i, Φ i)→ L)(S:Finset Y):Prop:= ∀ u v:(∀ i,Φ i), (∀ i∈S,u i=v i) → F u=F v
variable {S T:Finset Y}{F G:(∀ i,Φ i)→L}
lemma ScopedB.widen (h:ScopedB F S)(p:S⊆T):ScopedB F T:=fun u v e=> h u v (fun i l=> e i (p l))
lemma ScopedB.prod [CommMonoid L](S1:Finset I)(f:I→ (∀ i,Φ i)→L)(h:∀ i∈S1,ScopedB (f i) T):ScopedB (fun v=>∏ i∈ S1,f i v) T:=fun u v e=> prod_congr rfl fun i p=> h i p u v e
lemma ScopedB.mul [Mul L](h:ScopedB F T)(p:ScopedB G T): ScopedB (fun v=>F v*G v) T:= fun u v e=>congrArg₂ (·*·) (h u v e) (p u v e)
lemma ScopedB.norm [Norm L](p:ScopedB F T): ScopedB (fun v=>‖F v‖) T:= fun u v e=>congrArg (‖·‖) (p u v e)
variable [Fintype Y][∀ i, MeasurableSpace (Φ i)] [∀ i,Nonempty (Φ i)] (μ ν:∀ i, Measure (Φ i))[∀ i,IsProbabilityMeasure (μ i)][∀ i,IsFiniteMeasure (ν i)]
def attend (E:Finset Y)(i:Y):= if i∈E then ν i else μ i
instance attend.finite (E:Finset Y)(i:Y): IsFiniteMeasure (attend μ ν E i):=by unfold attend; split <;> infer_instance
abbrev century (E:Finset Y):= Measure.pi (attend μ ν E)
instance : IsProbabilityMeasure (century μ ν ∅):=by rw [century, show attend μ ν ∅=μ from funext fun i=>if_neg (notMem_empty _)]; infer_instance
variable [RCLike L]
lemma autumn (E E':Finset Y)(p: E⊆ S)(q:E'⊆T)(h:ScopedB F S)(t:ScopedB G T)(d:Disjoint S T):
 (∫ x,F x*G x ∂century μ ν (E∪E'))=(∫ x,F x ∂ century μ ν E)*(∫ x,G x ∂ century μ ν E'):=by
 let U0:= E∪E'; let W:= MeasurableEquiv.piEquivPiSubtypeProd Φ (·∈S); let Θ(A:Finset Y):= fun i:{i:Y//i∈S}=> attend μ ν A i.val; let Γ(A:Finset Y):= fun i:{i:Y//¬i∈S}=>attend μ ν A i.val
 let X(A:Finset Y):= @Measure.pi _ _ (Subtype.fintype (·∈S)) _ (Θ A); let R(A:Finset Y):=Measure.pi (Γ A)
 haveI : ∀ i,IsProbabilityMeasure (Θ E' i):= by intro i; rw [show Θ E' i=μ i.val from if_neg (fun v=> disjoint_left.mp d i.property (q v))]; infer_instance
 haveI : ∀ i,IsProbabilityMeasure (Γ E i):=by intro i; rw [show Γ E i=μ i.val from if_neg (fun v=> i.property (p v))]; infer_instance
 have h₁:X U0 = X E:=by
    unfold X; have hp:Θ U0=Θ E:=funext fun i=> by by_cases h:i.val∈E <;> simp [Θ,U0,attend,h,show ¬i.val∈E' from fun v=> disjoint_left.mp d i.property (q v)]
    rw [hp]
 have h₂:R U0=R E':=by unfold R; rw [show Γ U0=Γ E' from funext fun i=> (by simp [Γ,U0,attend,show ¬i.val∈E from fun v=> i.property (p v)])]
 haveI : (A:Finset Y)→ IsFiniteMeasure (X A):= by intro A; unfold X Θ; infer_instance
 haveI : (A:Finset Y)→ IsFiniteMeasure (R A):= by intro A; unfold R Γ; infer_instance
 haveI : IsProbabilityMeasure (X E'):= by unfold X; infer_instance
 haveI : IsProbabilityMeasure (R E):= by unfold R; infer_instance
 have he(A:Finset Y) : MeasurePreserving W.symm ((X A).prod (R A)) (century μ ν A):= (measurePreserving_piEquivPiSubtypeProd (attend μ ν A) (·∈S)).symm W -- tune Fintype
 rw [← (he U0).integral_comp' (fun x=>F x*G x), ← (he E).integral_comp' F, ← (he E').integral_comp' G]; -- tune match
 let ζ := W (Classical.arbitrary _); let f:= fun v=> F (W.symm (v,ζ.2)); let g:= fun v=> G (W.symm (ζ.1,v)); have ht (P):F (W.symm P)=f P.1:= h _ _ (fun i (p:i∈ S)=> by simp [W,p])
 have hv (P):G (W.symm P)=g P.2:= t _ _ (fun i foo=>by simp [W,show i∉ S from fun q=> disjoint_left.mp d q foo])
 rw [h₁,h₂]; simp_rw [ht,hv]; rw [integral_fun_fst f,integral_fun_snd g, integral_prod_mul f g]; simp
end YM.CF.BPress.Contour
