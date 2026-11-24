import YM.CF.Skye.Snap
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n:Side}{u d:ℝ}
lemma mealM{I A T:Type*}[Countable I][MeasurableSpace A][MeasurableSpace T]{F:A→I}(p:∀ i, MeasurableSet (F ⁻¹' {i})){G:I→A→T}(h:∀ i,Measurable (G i)):Measurable fun x=>G (F x) x:= by
 intro s e; rw [show (fun x=>G (F x) x) ⁻¹' s=⋃ i,F ⁻¹' {i} ∩ G i ⁻¹' s from ?_]; exact MeasurableSet.iUnion fun i=>(p i).inter (h i e)
 ext; simp
lemma primeV : Measurable (@priorP n):= measurable_pi_lambda _ fun i=> measurable_fst.comp (measurable_pi_apply i)
private lemma locus(S:Finset (Seat n))(e:reach n)(r:ℕ):Measurable (fun x:Orbit n=>(x.2 (greet (soup S r e) (priorP x.2))).2.1):=by
 let J(x:Orbit n):=greet (soup S r e) (priorP x.2); have h:Measurable J:=(mastM _).comp (primeV.comp (measurable_snd (α:=Pane n)))
 exact mealM (F:=J) (fun i=>h (measurableSet_singleton _)) (G:=fun i (x:Orbit n)=> (x.2 i).2.1) (fun i=> measurable_fst.comp (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)))
private lemma actG (P:Pane n→Pane n)(hp:Measurable P)(s:Sweep n)(e:reach n):Measurable fun x:Orbit n=>mend P s x.1 e:= (measurable_pi_apply e).comp (((revM s⁻¹).measurable.comp (hp.comp (revM s).measurable)).comp measurable_fst)
private lemma actSoup (P:Pane n→Pane n)(hp:Measurable P)(e:reach n)(r:ℕ)(S:Finset (Seat n)):Measurable fun x:Orbit n=>if (soup S r e).Nonempty then mend P (x.2 (greet (soup S r e) (priorP x.2))).2.1 x.1 e else x.1 e:=by
 split; next v=> exact mealM (F:=fun x:Orbit n=>(x.2 (greet (soup S r e) (priorP x.2))).2.1) (fun i=> locus S e r (measurableSet_singleton _)) (G:=fun s x=>mend P s x.1 e) (fun i=>actG P hp i _)
 exact (measurable_pi_apply e).comp measurable_fst
private lemma flagsO (V:Finset (Seat n))(u:ℝ):MeasurableSet ((fun x:Orbit n=> RG.flags u x.1) ⁻¹' {V}):= measurable_fst (RG.flags_measurable_eq ..)
private lemma lightsM (P:Pane n→Pane n)(u:ℝ)(r:ℕ)(hp:Measurable P): Measurable (lightly P u r):= measurable_pi_lambda _ fun e=>mealM (F:=fun x:Orbit n=>RG.flags u x.1) (fun i=> flagsO i _) (G:=fun S x=>if (soup S r e).Nonempty then mend P (x.2 (greet (soup S r e) (priorP x.2))).2.1 x.1 e else x.1 e) (fun S=>actSoup P hp e _ _)
private lemma gaugesM : Measurable fun x:(Seat n→E)×Pane n=> gauge x.1 x.2:=by apply Continuous.measurable; apply continuous_pi; intro i; simp only [Lattice.gauge]; fun_prop
lemma sunM (P:Pane n→Pane n)(u:ℝ)(r:ℕ)(hp:Measurable P): Measurable (sun P u r):=by
 let f(x:Orbit n):=frameP x.2; have ht:Measurable f:= measurable_pi_lambda _ fun i=> measurable_snd.comp (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))
 let b(x:Orbit n):=(Lattice.gauge (f x) x.1,x.2); have he: Measurable b:= ((gaugesM (n:=n)).comp (ht.prodMk measurable_fst)).prodMk measurable_snd
 have hk: Measurable (fun (x:Orbit n) (i:Seat n)=> ((f x) i)⁻¹) := measurable_pi_lambda _ fun i=> ((measurable_pi_apply i).comp ht).inv
 let t(x:Orbit n):=((frameP x.2)⁻¹,lightly P u r (b x)); have hT:Measurable t:= hk.prodMk ((lightsM P u r hp).comp he)
 rw [show sun P u r=(fun x:(Seat n→E)×Pane n=>Lattice.gauge x.1 x.2) ∘ t from rfl]; exact (gaugesM (n:=n)).comp hT
-- knows when region admitted
structure Week(X:Support (More n))(S M: Support (More n))(k:ℕ) :Prop where
 all(i:reach n)(v:ends i⊆ S):win k i⊆ X
 mask(i:reach n)(v:ends i⊆ S): ∀ a∈soup M k i,halo (2*k+20) {a}⊆ X
lemma keepsL (S M X:Support (More n))(k:ℕ)(h:halo (2*k+20) (M∩X) ⊆ X)(r:halo k S ⊆ X): Week X S M k:=by
 have he(i:reach n)(v:ends i⊆ S):win k i⊆ X:=by intro j hj; obtain ⟨y,t,p⟩:=halo_spec.mp hj; exact r (halo_spec.mpr ⟨y,v t,p⟩)
 refine ⟨he,fun i t a v p g=>?_⟩; obtain ⟨q,x,b⟩:= (mem_filter.mp v).2
 have hx:a∈X:=by
    have hp':∀ a,Relation.ReflTransGen (legs M k) q a→a∈X:=by
      intro a b; induction b with
      | refl=>exact he _ t (mem_inter.mp (cake_p M k i ▸ x)).2
      | tail _ v ih=> exact h (halo_spec.mpr ⟨_,mem_inter.mpr ⟨v.1,ih⟩,v.2.2⟩)
    exact hp' a b
 exact h (halo_spec.mpr ⟨a,mem_inter.mpr ⟨(mem_filter.mp v).1,hx⟩,by simpa [halo_spec] using g⟩)
lemma noon (t:Ids n)(V:Pane n):gauge (frameP t)⁻¹ (gauge (frameP t) V)=V:=by rw [gauge_sq,inv_mul_cancel]; funext; simp [Lattice.gauge]
lemma sunW {r:ℕ}(P: Pane n→Pane n)(h:Basic n P u d r)(V W:Pane n)(t z:Ids n)(X S:Support (More n))(p:X ∩ RG.flags u V=X ∩ RG.flags u W)(f: Week X S (RG.flags u V) r)(g:Week X S (RG.flags u W) r)(k:Agrees X V W)(m:Set.EqOn t z X): Agrees S (sun P u r (V,t)) (sun P u r (W,z)):=by
 intro i vi wi; let A:= gauge (frameP t) V; let B:= gauge (frameP z) W; let D:= RG.flags u V; let J:= RG.flags u W; have hx: Agrees X A B:=tied _ _ _ _ _ k (fun i v=> by simp only [frameP,m v]); have ht:ends i⊆ S:= insert_subset_iff.mpr ⟨vi,singleton_subset_iff.mpr wi⟩; have hp:ends i⊆ X:=Subset.trans (halo_subset r _) (f.all i ht) -- ambiguity
 have hl:soup D r i=soup J r i:=suppC _ _ _ _ _ (by unfold D J; rw [inter_comm,inter_comm J]; exact p) (f.all _ ht) (f.mask _ ht) (g.mask _ ht) -- J after unfold
 have hy: lightly P u r (A,t) i=lightly P u r (B,z) i:=by
    have he: RG.flags u A = D:= RG.gauge_flags ..; have hv:RG.flags u B=J:=RG.gauge_flags ..; unfold lightly; dsimp only; rw [he,hv,hl]; by_cases q:(soup J r i).Nonempty; swap; · rw [if_neg q,if_neg q]; exact hx i (hp (by simp)) (hp (by simp))
    have ht'(x)(e:x∈soup J r i):x∈X:= g.mask i ht _ e (halo_subset _ _ (mem_singleton_self x)); rw [if_pos q,if_pos q,mastL _ _ (priorP z) (fun x v=> congrArg Prod.fst (m (ht' x v))),m (ht' _ (mastP _ q _).1), (mine h _).shore A B i (agrees_mono hx (f.all _ ht))]
 unfold sun Lattice.gauge; simp only [show ∀ i, (frameP t)⁻¹ i=(t i).2.2⁻¹ from fun _=>rfl,show ∀ i, (frameP z)⁻¹ i=(z i).2.2⁻¹ from fun _=>rfl]
 rw [m (show (i.1)∈↑X from hp (by simp)),m (show i.1+step i.2∈↑X from hp (by simp))]; exact congrArg (fun v=>_*v*_) hy -- tune
lemma sun_here(P: Pane n→Pane n)(u:ℝ)(r:ℕ)(V: Pane n)(t:Ids n)(i:reach n)(h:Disjoint (RG.flags u V) (win r i)): sun P u r (V,t) i= V i:=by
 have hv:lightly P u r (gauge (frameP t) V,t) i = gauge (frameP t) V i :=by unfold lightly; dsimp only; rw [if_neg]; rw [RG.gauge_flags]; exact fun v=> (pieV ..|>.mp v) h
 exact calc
   _ = gauge (frameP t)⁻¹ (gauge (frameP t) V) i:=congrArg (fun v=>(frameP t)⁻¹ _*v*_) hv -- tune
   _ = _:= by rw [noon]
structure Roof(n:Side)(u d:ℝ)(r:ℕ) (P: Orbit n→Pane n):Prop where
 paid(x): Guard (P x) d
 bill:Measurable P
 rev(V:Pane n)(X:Ids n)(g:Seat n→E):P (gauge g V,threadG g X)=gauge g (P (V,X))
 move(V:Pane n)(X:Ids n)(s:Sweep n)(v:Injective (priorP X)): P (flashA s V,bun s X)=flashA s (P (V,X))
 lamp(V:Pane n)(t: Ids n)(i:reach n):Disjoint (RG.flags u V) (win r i)→P (V,t) i=V i
 transmission (V W:Pane n)(t z:Ids n)(X S:Support (More n))(p:X ∩ RG.flags u V=X ∩ RG.flags u W)(f: Week X S (RG.flags u V) r)(g:Week X S (RG.flags u W) r)(k:Agrees X V W)(m:Set.EqOn t z X): Agrees S (P (V,t)) (P (W,z))
theorem roofs (d:ℝ)(t:0<d) :∃ N:ℕ,∀ B:Side,N≤B.val → ∃ k u,0<u∧∀ m:Side,2≤m.val→ ∃ P,Roof (CSide m B) u d k P:=by
 obtain ⟨b,c,H⟩:=taxon t; obtain ⟨N,J⟩:= trench c; refine ⟨N,fun B v=>?_⟩
 obtain ⟨u,p,K⟩:= J _ v; refine ⟨2*B.val,u,p,fun m r=>?_⟩; obtain ⟨F,g⟩:= K m r; have ht:= repairB F g
 refine ⟨sun F _ _,⟨fun x=>H _ _ ?_,sunM _ _ _ ht.meas,fun V X s=>sun_g _ _ _ _ _ _,fun V X i h=> sun_v _ _ _ _ _ h _,fun V X i=>sun_here _ _ _ _ _ _,sunW F ht⟩ ⟩
 rw [sun,RG.gauge_flags]; exact lightLegal ht _
end YM.CF.Skye
