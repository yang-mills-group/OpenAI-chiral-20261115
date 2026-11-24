import YM.SU5.FiniteGaugeData.Marked.Variation.Hearth

/-! # Optional: strong norm form with comparison by whole-box operator bound
(still selected-volume & UV, fixed resolution, histories in Course). -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Py Py.Rate LocalLimit Preparation Journey Vale VolumeCape
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x){i k:ℕ→ℕ}
local notation "K"=>tent Y H
variable {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(S:Finset Cover)(s:ℕ)
local notation "Ω"=>sharp Y H s
private lemma accounted {f g:Family (tent Y H)} (h:TestFamily K true f)(t:TestFamily K true g){m n:ℕ}(p:Ferry Y s m n): Ω m n (f+g)=Ω m n f+Ω m n g:=by
 let ν:=momentm Y m s; let t' : Mark ((K).c ν)→ℂ:= Journey.listen Y H m n s
 have he(v w: Mark ((K).c ν)): Journey.send Y H m s (v+w)=send Y H m s v+Journey.send Y H m s w:= selling (terrain Y H (Y.ir m) s) ..
 unfold sharp Journey.listen Journey.compass; rw [Pi.add_apply,he,mark_add _ _ _ (Marks.can_read _ _ _ _ p.fire.priceA),add_div]
 · exact ((Y.voyage m).ownership s).paid.bill
 · exact post (terrain Y H (Y.ir m) s) _ ((h.paid.choose_spec).support _).env
 exact post (terrain Y H (Y.ir m) s) _ ((t.paid.choose_spec).support _).env
where
 selling{m n:Side}(h:m=n)(i j:Mark m): (show Mark n from h ▸ (i+j))= (show Mark n from h ▸ i)+ (show Mark n from h ▸ j):=by subst m; rfl
 post {m n:Side}(h:m=n)(i:Mark m)(p:Envelope i) : Envelope (show Mark n from h ▸ i):=by subst m; exact p
private lemma reason {J:Type*}(v:J→Family (tent Y H))(h:∀ i,TestFamily K true (v i))(P:Finset J): TestFamily K true (∑ x∈P,v x):= Submodule.sum_mem (probes K true) (fun x _=> h x)
include V
private lemma ensemble {J:Type*}(v:J→Family (tent Y H))(h:∀ i,TestFamily K true (v i))(P:Finset J):
 let F:= ∑ i∈P,v i
 (∀ m n,Ferry Y s m n → Ω m n F =∑ i∈P, Ω m n (v i)) ∧ (∀ m,I s F m=∑ i∈P,I s (v i) m) ∧ E s F=∑ i∈P,E s (v i):=by
 classical
 have he(P:Finset J)(m n:ℕ)(a:Ferry Y s m n):Ω m n (∑ i∈P,v i)=∑ i∈P,Ω m n (v i):=by
    induction P using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; have he:= (accounted Y H s (TestFamily.zeroT) (TestFamily.zeroT) a); rw [add_zero] at he; exact add_left_cancel (b:=Ω m n 0) (c:=(0:ℂ)) (by rw [add_zero]; exact he.symm) 
    | insert i P iP ih=>rw [sum_insert iP,sum_insert iP,accounted Y H s (h _) (reason Y H v h P) a, ih]
 intro F
 have H':=V.together s F (reason Y H v h P)
 have v'(m):I s F m= ∑ i∈P,I s (v i) m:=by
    apply tendsto_nhds_unique (H'.inner m)
    refine (tendsto_finsetSum P (fun i _=> (V.together s (v i) (h i)).inner m)).congr' ?_
    exact (V.pick.pass Y H s m).mono fun l p=> (he P m (k l) p).symm
 refine ⟨he P,v',tendsto_nhds_unique H'.periods ((tendsto_finsetSum P (fun i _=>(V.together s (v i) (h i)).periods)).congr' (Filter.Eventually.of_forall fun l=> (v' _).symm))⟩
local notation "Aₛ"=> plaza (Λ:=Λ) S
-- uniform cost for sum receipts

def fees(Λ:Preparation)(l:ℕ)(S:Finset Cover):ℝ:= (Fintype.card (Courses (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S)):ℝ)*(Fintype.card (Evens S))
local notation "d"=> fees Λ l S
omit V
lemma finance : 0 ≤ fees Λ l S:=by unfold fees; positivity
-- charge uniform error relative to all-panel sum by native common op bound
lemma patronage (R:Family (tent Y H))(a:Evens S→Purse S)(t:R=∑ x:Evens S,note K (a x).val (tagWord S x.val)){m:Side}(p:Hosp S ((K).c m))(y:ℝ)(hy:∀ x, ‖R m x‖ ≤ y):
  (∑ i:Evens S, price Λ l S (a i).val) ≤ fees Λ l S*y:=by
 have he:=ruby S K R a t p y hy
 unfold price Touch Common.touch Common.amount
 have hv(i:Evens S): (∑ u:Courses ((VolumeCape.Dream.plot l).C) Aₛ, ∫ x, ‖(a i).val (Common.pairs ((VolumeCape.Dream.plot l).C) (VolumeCape.Dream.plot l).K Aₛ u x)‖∂Common.law ((VolumeCape.Dream.plot l).C) Aₛ) ≤ (Fintype.card (Courses ((VolumeCape.Dream.plot l).C) Aₛ):ℝ)*y:=by
    rw [←nsmul_eq_mul,←card_univ,←sum_const (s:=(univ:Finset (Courses ((VolumeCape.Dream.plot l).C) Aₛ)))]
    exact sum_le_sum fun _ _=> (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x=> norm_nonneg _)) (integrable_const y) (Filter.Eventually.of_forall fun x=>he i _)).trans (by simp)
 exact (Finset.sum_le_sum (fun i _=>hv i)).trans (by rw [sum_const,nsmul_eq_mul,card_univ,fees]; exact le_of_eq (by ring))
include V
lemma boutique :
    (∀ᶠ n:ℕ in atTop, ∀ ε:ℝ, 0<ε→∀ᶠ j:ℕ in atTop,∀ (f:Family (tent Y H)), InTest K true S false f→∀ (m:Side), Hosp S ((K).c m)→∀ (C:ℝ), (∀ x, ‖f m x‖ ≤ C)→ ‖Ω n (k j) f - I s f n‖ ≤ ε*C) ∧
    (∀ ε:ℝ,0<ε→∀ᶠ r:ℕ in atTop,∀ (f:Family K),InTest K true S false f→∀ (m:Side), Hosp S ((K).c m)→∀ (C:ℝ), (∀ x, ‖f m x‖ ≤ C)→
      ‖I s f (i r)- E s f‖ ≤ ε*C ∧ ∀ j:ℕ, legacy Y (i r) (k j)→ ‖Ω (i r) (k j) f - E s f‖ ≤ ε*C):=by
 have p(t:Evens S):= relatives Y H V S s (tagWord S t.val) (bracketV S t)
 let X (a:Evens S→ Purse S)(t:Evens S):Family K:=note K (a t).val (tagWord S t.val)
 have hX(a:Evens S→ Purse S)(t:Evens S):TestFamily K true (X a t):= ⟨⟨S,t.property ▸ note_t K (tagWord S t.val) (a t).property (brand S t.val)⟩, by simp⟩
 have h (ε:ℝ)(he:0<ε):0<ε/(d+1):= by have z:=finance (Λ:=Λ) (l:=l) S; positivity
 have ha (R:Family (tent Y H))(m:Side)(q:Hosp S ((K).c m))(y:ℝ)(t:∀ x, ‖R m x‖≤y)(ε:ℝ)(he:0<ε)(a:Evens S→Purse S)(p:R=∑ x:Evens S,note K (a x).val (tagWord S x.val))(f g:Evens S→ℂ)(w:∀ i,‖f i-g i‖≤ ε/(d+1)*price Λ l S (a i).val): ‖(∑ i,f i)-(∑ i,g i)‖ ≤ ε*y:=by
    rw [← Finset.sum_sub_distrib]; let E:= ε/(d+1)
    have z:= finance (Λ:=Λ) (l:=l) S
    have hz:E*(d+1)=ε:=div_mul_cancel₀ _ (by linarith)
    have hp:0≤y:= (norm_nonneg _).trans (t (1,1))
    refine (norm_sum_le ..|>.trans (sum_le_sum fun x _=>w x)).trans ?_; rw [←mul_sum]; apply (mul_le_mul_of_nonneg_left (patronage Y H S R a p q y t) (h ε he).le).trans; change E*(d*y)≤_; rw [←mul_assoc]; have e:= h ε he; change 0<E at e; gcongr; linarith
 constructor
 · filter_upwards [(eventually_all (ι:=Evens S)).mpr (fun t=>(p t).1)] with n q
   intro ε he
   filter_upwards [(eventually_all (ι:=Evens S)).mpr (fun t=> q t _ (h ε he)),V.pick.pass Y H s n] with j T g
   intro F P m q y z; obtain ⟨a,w⟩:= circulation S K P
   obtain ⟨g₀,gs,_⟩:=ensemble Y H V s (X a) (hX a) Finset.univ -- order
   rw [w,g₀ n (k j) g,gs]; exact ha F m q y z ε he a w _ _ (fun i=>T i _ (a i).property)
 intro ε he; let E':= ε/(d+1)
 obtain ⟨p₀,E0⟩:= eventually_atTop.mp (Journey.ferry_all Y s)
 have t:= ((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp (Y.ir_grows.comp V.pick.grow_i).tendsto_atTop)
 filter_upwards [(eventually_all (ι:=Evens S)).mpr (fun t=> (p t).2 _ (h ε he)),t.eventually_ge_atTop (Y.uv p₀)] with r p₁ pV
 intro F P m q y z; obtain ⟨a,w⟩:= circulation S K P
 obtain ⟨g₀,gs,hg⟩:=ensemble Y H V s (X a) (hX a) Finset.univ
 constructor
 · rw [w,gs,hg]; exact ha F m q y z ε he a w _ _ (fun x=> (p₁ x _ (a x).property).1)
 intro j u'; have hx: Ferry Y s (i r) (k j):= E0 _ (Y.uv_grows.le_iff_le.mp (pV.trans u')) _ (V.pick.ticket r j u')
 rw [w,g₀ _ _ hx,hg]; exact ha F m q y z ε he a w _ _ (fun x=> (p₁ x _ (a x).property).2 j u')
#check eventually_all
#check @ensemble
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.boutique
