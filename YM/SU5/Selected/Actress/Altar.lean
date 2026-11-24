import YM.SU5.Selected.Actress.Dahl
import YM.SU5.Selected.Actress.Scarves
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open Function Filter Real Set Complex Analysis Boundary Probe OS.Semigroup
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators ComplexOrder
/- pre-local algebra reconstruction for (selected) phase directly. uses time-width labels. -/
def spireSet(T:Hilbert){i:Axis}{κ: Type*}(S:OS.Semigroup T i)(k:κ→ T.Op):Set T.Op:= {x| ∃ i t, x=conduct S t (k i)}
def spireC(T:Hilbert)(S:Set T.Op): StarSubalgebra ℂ T.Op:= (StarAlgebra.adjoin ℂ S).topologicalClosure
lemma SP0(T:Hilbert){i:Axis}{κ:Type*}(S:OS.Semigroup T i)(k:κ→T.Op)(z:κ)(t:ℝ): conduct S t (k z) ∈ spireC T (spireSet T S k) := StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (show _ from ⟨z,t,rfl⟩))
lemma SP_C(T:Hilbert){i:Axis}{κ:Type*}(S:OS.Semigroup T i)(k:κ→T.Op)(z:κ) : k z ∈ spireC T (spireSet T S k):= by rw [←mandate S (k z)]; exact SP0 T S k z 0
lemma willPrior {H:Hilbert}(S:Set H.Op)(f:H.Op ≃⋆ₐ[ℂ] H.Op)(p:Set.MapsTo f S S) : Set.MapsTo f ((StarAlgebra.adjoin ℂ S).topologicalClosure:Set H.Op) ((StarAlgebra.adjoin ℂ S).topologicalClosure:Set H.Op):=by
 let P':=(StarAlgebra.adjoin ℂ S).topologicalClosure
 suffices t:P' ≤ P'.comap f.toStarAlgHom from fun i h=> t h
 exact StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le fun x h => (show f x∈ P' from StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (p h)))) (isClosed_closure.preimage (StarAlgEquiv.isometry f).continuous)
lemma sp_move(T:Hilbert){i:Axis}{κ:Type*}(S:OS.Semigroup T i)(x:κ→T.Op)(t:ℝ): Set.MapsTo (conduct S t) (spireC T (spireSet T S x)) (spireC T (spireSet T S x)) := willPrior _ (conduct S t) (fun i h=>by obtain ⟨F,s,rfl⟩:=h; exact ⟨F,t+s, conducts S t s (x F)⟩)

variable {H:Hilbert}{i:Axis}{κ:Type*}(S:OS.Semigroup H i)(Ω:H)(f:κ → H.Op) {α:Type*}(T:α→unitary H.Op)
-- matrix view of trans story. tookP enforces symmetry of generator under each ticket, or time. verify directly by relation.
abbrev vista:=spireC H (spireSet H S f)
local notation "g₀"=> vista S f
local notation "𝓢"=> sameShore (g₀)
def tickets := Sum.elim (ascends S) T
@[simp] lemma tickets_inl(t:ℝ): tickets S T (Sum.inl t) = ascends S t:=rfl
@[simp] lemma tickets_inr(t:α): tickets S T (Sum.inr t)= T t:=rfl
local notation "B"=> tickets S T
def JMotion : Prop:= ∀ (i:α), (∀ t:ℝ, Commute (T i).val (S.edge t)) ∧ ∀ x:κ,∃ y:κ,(T i).val*f x=f y*(T i).val
local notation "F"=> opState (g₀) Ω
structure Urbana : Prop where -- fields qualified for all ; include B not needed.
   waged: JMotion S f T
   vac: ‖Ω‖=1
   spore (i:ℝ ⊕ α) : (B i).val Ω=Ω
   fit (i:ℝ ⊕ α) : MapsTo (Unitary.conjStarAlgAut ℂ H.Op (B i)) (↑g₀) (↑g₀)
   born : DenseRange (ray (g₀) Ω)
   keeps: 𝓢 B F fit
   principal (X Y: ↑(vista S f)→ₗ[ℂ] ℂ)(t:ℝ): 0<t→ t<1→ 𝓢 B X fit → 𝓢 B Y fit → F = (t:ℂ) • X+((1-t:ℝ):ℂ) • Y → X=F ∧ Y=F  -- t common; use variable names.
   owner : ∀ x:H,(∀ i:ℝ ⊕ α, (B i).val x=x)→∃ c:ℂ,c • Ω=x
#print Urbana.mk
lemma city (p: ‖Ω‖=1)(h:Ω∈ S.ground)(c:DenseRange (fun i:κ=> f i Ω))(w:JMotion S f T) (ca:∀ i:α,(T i).val Ω=Ω)(u:∀ x:H,(∀ i:ℝ ⊕ α,(B i).val x=x)→∃ c:ℂ,c • Ω=x) : Urbana S Ω f T:=by
 have q(i:ℝ ⊕ α) : MapsTo (Unitary.conjStarAlgAut ℂ H.Op (B i)) (↑g₀) (↑g₀) := by
    cases i with
    | inl i=> exact sp_move ..
    | inr i=>
      let A'(x:H.Op):= Unitary.conjStarAlgAut ℂ H.Op (T i) x
      apply willPrior; rintro y ⟨x,t,e⟩
      have ht:= w i; obtain ⟨d,l⟩:=ht.2 x; use d,t; rw [e]; let g:= (T i).val
      rw [tickets_inr,Unitary.conjStarAlgAut_apply]; change g*conduct S t (f x)*star g=_; suffices v:g*conduct S t (f x)= conduct S t (f d)*g by rw [v,mul_assoc,(T i).property.2,mul_one]
      rw [system,system]; calc
       _ = S.edge t * ((g*f x)* S.edge (-t)) := by
         rw [←mul_assoc,←mul_assoc]; rw [ (ht.1 t).eq]; simp only [mul_assoc]; rfl -- inspect l.
       _ = S.edge t * (f d *(S.edge (-t)*g)):= by change g * f x = _ at l; rw [l,mul_assoc,(ht.1 (-t)).eq]; -- simp maybe
       _ = _:= by simp only [mul_assoc]
 have he : DenseRange (ray (g₀) Ω):= c.mono (by rintro _ ⟨i,rfl⟩; exact ⟨⟨f i,SP_C H S f _⟩,rfl⟩)
 have hp(i:ℝ ⊕ α) : (B i).val Ω=Ω:=match i with| Sum.inl i=> mink_invar S Ω i h|Sum.inr i=> ca i
 let v:= principal (g₀) Ω B hp q p he u; exact ⟨w,p,hp,q,he,v.1,v.2,u⟩
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms Urbana
#print axioms city
#print axioms vista
