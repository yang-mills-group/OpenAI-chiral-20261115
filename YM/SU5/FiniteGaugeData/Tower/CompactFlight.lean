import YM.SU5.FiniteGaugeData.Tower.Alliance
/-!
# Real representation of full space and time operators on continuous part

If needed, determine this is the *whole* resolution Hilbert by a separate
comparison. Without that, still have spectrum in one cone bound (p_j ≥0),
canonical maximality; compatible with E on all components via the retention
lemmas, where the latter statements concern **all** mark absorbable tails not
continuum contact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open Function Set Filter Metric ContinuousLinearMap
open scoped Topology InnerProductSpace Classical
variable {I:Type*}{Γ:AddSubgroup ℝ}{H:Hilbert}(S:Alliance I Γ H)(d:Dense (Γ:Set ℝ))
set_option quotPrecheck false
local notation "P" i:max=>S.crew i
local notation "U" i:max x:max=> (P i).play x
local notation "R" i:max x:max=> (P i).route d x
local notation "π" t:max=> S.stackS t
local notation "Id"=> ContinuousLinearMap.id ℂ H.space
variable (t:List I)
noncomputable def aviator : Submodule ℂ H:= ⨅ (i:I)(_ : i∈t),(P i).lives H
lemma assembled(x:H): x∈S.aviator t ↔ ∀i∈t,x∈ (P i).lives H:=by
 unfold aviator; simp
lemma planted(x:H): (π t) x∈S.aviator t:= (S.assembled ..).2 (fun i u => S.flyer_lives t i u x)
lemma grounded{x:H}(h:x∈S.aviator t):(π t) x=x:= by apply S.flyer_end; simp only [mem_iInter,mem_setOf_eq]; exact (assembled S t x).1 h
lemma regular{s:H.Op}(p:∀i∈t,∀c:Γ,(U i c).comp s=s.comp (U i c)){x:H}(hx:x∈S.aviator t):s x∈ S.aviator t:=by
 rw [←S.grounded t hx,←ContinuousLinearMap.comp_apply,S.ground t _ p,ContinuousLinearMap.comp_apply]
 exact S.planted _ _
instance buried:CompleteSpace (S.aviator t):=by
 have hp:(S.aviator t:Set H)= ⋂ i∈{i:I|i∈t},((P i).lives H:Set H):=by ext x; simp [S.assembled]
 have he: IsClosed (S.aviator t:Set H):= by rw [hp]; exact isClosed_iInter fun i=> isClosed_iInter fun _=> (P i).lives_closed
 exact he.completeSpace_coe
noncomputable def Realm : Hilbert where
 space:=S.aviator t
local notation "E₀"=> S.Realm t

-- generic Q-compressed operators
noncomputable def lame (A:H.Op)(h:∀i∈t,∀c:Γ,(U i c).comp A=A.comp (U i c)): (E₀).Op:=
 (show (S.aviator t)→ₗ[ℂ](S.aviator t) from A.toLinearMap.restrict (fun _ hx=> S.regular t h hx)).mkContinuous ‖A‖ (fun x=>by exact A.le_opNorm x.val)
lemma grating (A:H.Op)(p)(x:(S.aviator t)): (lame S t A p x : S.aviator t).val=A x.val:=rfl
lemma commuting(x:I→ℝ)(i:I)(k:Γ): (U i k).comp (S.flight d t x)=(S.flight d t x).comp (U i k):= (S.fluid d t _ (fun j _ c=>S.cCom j i c k) x).symm
noncomputable def aviation(x:I→ℝ): (E₀).Op:=S.lame t (S.flight d t x) (fun i _ k=>S.commuting d t x i k)
lemma avails(x:I→ℝ)(c:S.aviator t): (S.aviation d t x c:S.aviator t).val=S.flight d t x c.val:=rfl
lemma over(x:I→ℝ)(c:H):S.flight d t x ((π t) c) = S.flight d t x c :=by
 have h:(S.flight d t x).comp (π t)=S.flight d t x:=by rw [← S.start d,←S.travel,add_zero]
 rw [←ContinuousLinearMap.comp_apply,h]
lemma below(x:I→ℝ)(c:H): (π t) (S.flight d t x c)=S.flight d t x c:=by rw [←ContinuousLinearMap.comp_apply,←S.start d,←S.travel,zero_add]
lemma aviation_group(x y:I→ℝ):(S.aviation d t x).comp (S.aviation d t y)=S.aviation d t (x+y):=by ext1 f; apply Subtype.ext; change (S.flight d t x) ((S.flight d t y) _)= (S.flight d t (x+y)) _; rw [S.travel]; rfl
lemma aviation_zero: S.aviation d t 0=ContinuousLinearMap.id ℂ _:=by ext1 f; apply Subtype.ext; rw [avails, S.start]; exact S.grounded t f.property
lemma aviation_unit(x:I→ℝ)(c:(E₀)):‖S.aviation d t x c‖=‖c‖:=by
 have he(i:I→ℝ)(x:E₀):‖S.aviation d t i x‖≤ ‖x‖:=by
    change ‖(S.aviation d t i (x:S.aviator t):S.aviator t).val‖≤ ‖(x.val:H)‖
    rw [avails]; apply (S.sailed d t i _).trans; rw [S.grounded t x.property]
 apply le_antisymm (he x c)
 have h:=he (-x) (S.aviation d t x c); rwa [←ContinuousLinearMap.comp_apply,aviation_group,neg_add_cancel,aviation_zero] at h
lemma aviation_cont {D:Type*}[TopologicalSpace D](f:D→ I→ℝ)(h:∀i∈t,Continuous fun x=> f x i)(c:E₀):Continuous (fun i=> S.aviation d t (f i) c):=by
 change Continuous (fun i=> (S.aviation d t (f i) c : S.aviator t))
 apply Continuous.subtype_mk (p:=fun x=>x∈(S.aviator t:Set H)) (show Continuous (fun i=>(S.aviation d t (f i) c:S.aviator t).val) from ?_)
 exact S.moves d t f h (fun _=>c.val) continuous_const
end YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
#print axioms YM.CF.Buffered.Afterglow.Tower.Germ.Alliance.aviation_zero
