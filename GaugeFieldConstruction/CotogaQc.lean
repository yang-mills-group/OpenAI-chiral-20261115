import GaugeFieldConstruction.OlanderQc
import GaugeFieldConstruction.GayolaQc
import GaugeFieldConstruction.Meters
/-!
# Slot calculus on the calibration ledger
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing
open scoped Topology BigOperators ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ}
-- PriceAll on very one frame chosen. poly full later M
structure AreaQc (S:City) where
 fee (n:ℕ): (Fin n→l)→ Points n→ℂ
 reg n L:PlaqueQc (fee n L)
 price n L f: S.fee n L f=f.applyTo (fee n L)
 unit n L x(h:x∈generic (n+1)): fee (n+1) (Fathom.add (Empire.one five) L) x=fee n L (riders x) -- name tune
 rearr n (s:Equiv.Perm (Fin n)) x(h:x∈generic n) L: fee n (L ∘ s) (rearrange s x)=fee n L x
variable (S:City)
-- packages.Shape cards.Reads first slot w x.Kernel Test n unrestricted.
structure HintQc where
 n:ℕ
 x:Fin n→UV five
 f: Test (n+1)
structure InkQc extends HintQc where
 b:Bulb
 h:b.Works toHintQc.f 0
-- maps ann dependencies
section
variable {X : Type*}[AddCommGroup X][Module ℂ X]
noncomputable def DriftQc (T:X→ₗ[ℂ]UV five): X→ₗ[ℂ] HintQc→ℂ:= LinearMap.pi (fun i=>LinearMap.applyₗ i.f ∘ₗ S.tagged i.x ∘ₗ T)
lemma DriftCostQc (T:X→ₗ[ℂ]UV five)(A:HintQc)(w): DriftQc S T w A= S.fee _ (Fin.cons (T w) A.x) A.f:=by change S.tagged A.x (T w) A.f=_; rw [tagged_cost]
noncomputable def PenQc (T:X→ₗ[ℂ]UV five): X→ₗ[ℂ] InkQc→ℂ:= LinearMap.pi fun i=> LinearMap.proj i.toHintQc ∘ₗ DriftQc S T
-- detector prism. reduce arbitrary perm to slot. lemma arbitrary ext
end
lemma casedQc (x:Fin (n+1)→l):Fathom.add (x 0) (Fin.tail x)=x:= by simp [Fathom.add]
-- permutes target i to j. y∘ π where π j=i
noncomputable def JuteQc (r:Equiv.Perm (Fin n)):Equiv.Perm (Fin (n+1)):= (finSuccEquiv n).trans ((r.optionCongr).trans (finSuccEquiv n).symm) -- tune
lemma stepWorksQc (s:Equiv.Perm (Fin n))(p:Test n){b i} (x:b.Works p (s i)) : Works b (Fathom.perm s.symm p) i:=by -- annotate b
 let v:= loop s.symm
 have h:tsupport (perm s.symm p)⊆ v ⁻¹' tsupport p:= (ts_pull _ p).le
 have Hw(t:Points n)(i): t i=v t (s i):=by unfold v; change _=t (s.symm (s i)); rw [s.symm_apply_apply]
 refine ⟨fun t q=> ?_,fun t q j w=>?_⟩
 · rw [Hw]; exact x.bulb (v t) (h q)
 rw [Hw]; exact x.direct (v t) (h q) (s j) (s.injective.ne w)
lemma scale_hwQc (r:Equiv.Perm (Fin n))(i:Fin n)(v:Fin n→l)(x:l): update v (r i) x ∘ r= update (v ∘ r) i x:=by
 funext k; by_cases p:k=i
 · subst k; simp
 simp [p,r.injective.ne p]
lemma formHwQc (S: City)(s:Equiv.Perm (Fin n))(k : Fin n)(p:Test n)(L:Fin n→l)(x:l): S.spot L (s k) x p=S.spot (L ∘ s) k x (Fathom.perm s.symm p):=by
 rw [spot_cost,spot_cost,←scale_hwQc,S.rearr]
lemma PenSeenQc (S:City)(H:∀ v:l,(∀ w (p:Foil),S.spot (other w) front v p.p=0)→v=0){X : Type*}[AddCommGroup X][Module ℂ X](T:X→ₗ[ℂ] UV five)(h: Injective T) : Injective (PenQc S T):=by
 apply (detect _).mpr; intro x v; apply h; rw [map_zero]; refine H _ (fun w p=>?_)
 let s:=Equiv.swap (0:Fin 2) front
 have e:s 0=front:=Equiv.swap_apply_left ..
 let L:Fin 2→l:= other w
 let g:= InkQc.mk ⟨1,Fin.tail (L ∘ s), Fathom.perm s.symm p.p⟩ p.a (stepWorksQc s p.p (i:=0) (e.symm ▸ p.u))
 have ht:=v g; change S.spot L front _ _=0; rw [←e, formHwQc,← casedQc (L ∘ s),spot_cost]
 have hL: update (Fathom.add ((L ∘ s) 0) (Fin.tail (L ∘ s))) 0 (T x)=Fathom.add (T x) (Fin.tail (L ∘ s)):=Fin.update_cons_zero ..
 rw [hL]; change DriftQc S T x g.toHintQc=0 at ht; rw [DriftCostQc] at ht; exact ht
lemma DriftSeenQc (S:City)(H:∀ v:l,(∀ w (p:Foil),S.spot (other w) front v p.p=0)→v=0){X:Type*}[AddCommGroup X][Module ℂ X](T:X→ₗ[ℂ] UV five)(h:Injective T): Injective (DriftQc S T):=by
 intro i j e; apply PenSeenQc S H T h; ext1 y; exact congr_fun e y.toHintQc
#check Empire.one
#check Equiv.optionCongr
#check Equiv.optionCongr
#check finSuccEquiv
#check Fin.update_cons_zero
#print axioms DriftSeenQc
end YM.GaugeFieldConstruction.Ember.Hulse
