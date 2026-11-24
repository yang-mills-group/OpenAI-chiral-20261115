import GaugeFieldConstruction.Booms
/-! tariffs via positive sums -/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FlightFlux
open Function Filter Metric Lattice Laurent Bloch Finset RG Next.Free
open scoped Topology BigOperators Classical
section wage
variable {ι κ α:Type*}{E:Type*}{f g:ι→ℝ}{a v t:ℝ}
lemma SBgoed (p:SumBudget f a) :0≤a:=(tsum_nonneg p.1).trans p.2.2
lemma SBleast (p:SumBudget f a)(g: Finset ι): ∑ i∈g,f i ≤ a:=(p.2.1.sum_le_tsum _ (fun i _=>p.1 _)).trans p.2.2
lemma SBone (p:SumBudget f a) (x:ι):f x≤a:=by simpa using SBleast p {x}
lemma SBwork (h:∀ i,0 ≤ f i) (H:∀ s:Finset ι,∑ i∈s,f i ≤ a): SumBudget f a:=by
 have hx: Summable f:= summable_of_sum_le h H; exact ⟨h,hx,le_of_tendsto' hx.hasSum H⟩
lemma SBscale (p:SumBudget f a)(h:0≤t): SumBudget (fun i=> t*f i) (t*a):= SBwork (fun i=> mul_nonneg h (p.1 _)) (fun s=> by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (SBleast p s) h)
lemma SBplus(p:SumBudget f a)(h:SumBudget g v): SumBudget (fun i=> f i+g i) (a+v):= SBwork (fun x=>add_nonneg (p.1 _) (h.1 _)) (fun s=>by rw [sum_add_distrib]; exact add_le_add (SBleast p _) (SBleast h _))
lemma SBfin {f:κ→ι→ℝ}(g:Finset κ)(a:κ→ℝ)(h:∀ i∈g,SumBudget (f i) (a i)): SumBudget (fun i=>∑ x∈g, f x i) (∑ x∈g,a x):=SBwork (fun i=> sum_nonneg fun a b=> (h a b).1 _) (fun s=> by rw [sum_comm]; exact sum_le_sum fun i u=> SBleast (h i u) _)
lemma SBhook (p: SumBudget f a)(x:κ≃ι):SumBudget (f ∘ x) a:=SBwork (fun i=> p.1 _) (fun s=> by simpa only [comp_apply, Finset.sum_image (show Set.InjOn x s from x.injective.injOn)] using SBleast p (s.image x)) -- tune
lemma SBqual (u : SumBudget g v)(p: ∀ i,0≤f i)(w:∀ i,f i≤g i): SumBudget f v := SBwork p (fun s=> (sum_le_sum fun i _=>w i).trans (SBleast u _)) -- shadow v
lemma SBqual' (u : SumBudget g v)(p: ∀ i,0≤f i)(w:v≤ a)(h:∀ i,f i≤g i): SumBudget f a:=SBwork p (fun s=> (SBleast (SBqual u p h) s).trans w)
lemma SBmono (u: SumBudget f a)(w:a≤ v):SumBudget f v:= ⟨u.1,u.2.1,u.2.2.trans w⟩
lemma SBprod (F:ι→κ→ ℝ)(h:∀ i,SumBudget (F i) (f i))(p:SumBudget f a): SumBudget (uncurry F) a:=by
 have ht:0 ≤ uncurry F:= fun ⟨i,x⟩=> (h i).1 _; have he : Summable fun i=> ∑' x,F i x:= Summable.of_nonneg_of_le (fun i=> tsum_nonneg (h i).1) (fun i=>(h i).2.2) p.2.1; let t:=uncurry F
 have hx: Summable t:= (summable_prod_of_nonneg ht).mpr ⟨fun i=>(h i).2.1,he⟩ -- ht defeq warning
 refine ⟨ht,hx,?_⟩; change ∑' z,t z ≤_; rw [hx.tsum_prod]; exact (he.tsum_le_tsum (fun i=> (h i).2.2) p.2.1).trans p.2.2
lemma SBflip {F:ι×κ→ℝ}(v:SumBudget F a): SumBudget (fun z: κ×ι=> F z.swap) a:= SBhook v (Equiv.prodComm κ ι)
lemma SBfold {F:ι→κ→ℝ}(w:SumBudget (uncurry F) a): SumBudget (fun i=> ∑' j, F i j) a:= by
 rcases w with ⟨P,hv,h⟩; refine ⟨fun i=>tsum_nonneg (fun j=>P (i,j)),(summable_prod_of_nonneg (show 0≤ uncurry F from P)|>.mp hv).2,(?_ : _ ≤ _)⟩; rw [hv.tsum_prod] at h; exact h
lemma SBmin (t:κ → ι)(x:Injective t)(p:SumBudget f a):SumBudget (fun i:κ=> f (t i)) a:=SBwork (fun i=>p.1 _) (fun s=> by rw [← sum_image x.injOn]; exact SBleast p _)
abbrev chime (t:ι→ℝ) [Norm E](f:ι→ E)(x:ℝ):=SumBudget (fun i=> t i*‖f i‖) x
end wage
end YM.FlightFlux
end
