import YM.CF.BPress.Spark.Estate
/-! eq:B-Oexpect. Canonical $H$ after row budget. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Palmer Fock Pastry Pine Pine.EdgeD Pf Vesper Spin Spin.Pledge Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement Pine.Story -- check
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {I D Y :Type}[LinearOrder I][Fintype I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D](P : Stage Y I D Empty) {X Y':D→Finset I}{A T:Raw D I}{C C':D→ℝ→Op I}{h d ε r:ℝ}
-- Groove labels deterministic orientation. build EdgeD as all Throne labels. unify $Spin$ Order costs P.
abbrev Emet (P: Stage Y I D Empty) (i j:TripC I)(s:Seal Y):Prop:= Grove P.F s ∧ P.home (throat i)∈s ∧ P.home (throat j)∈s
abbrev Shimmer := {x:TripC I × TripC I × Seal Y // x.1<x.2.1∧ Emet P x.1 x.2.1 x.2.2}
def crownP : EdgeD (TripC I) (Shimmer P) Y P.F:=⟨P.home ∘ throat, fun i=>i.val.1, fun i=> i.val.2.1,fun i=>i.property.1, fun i=> i.val.2.2,fun i=> i.property.2.1,fun i=>i.property.2.2.1, fun i=> i.property.2.2.2⟩
variable {P}
abbrev χPay(P:Pledge):ℝ:= (Fintype.card SpinIndex:ℝ)*P.price
variable {F:SpinIndex→SpinIndex→ Raw D I}(B:Pledge)
structure Offered (U:D→Shimmer P→ℂ)(w: Shimmer P→ℝ):Prop where
 weight: Enorm (crownP P) B.rate (χPay B) w
 help:∀ p, Expo P ((crownP P).look p) (throat p.val.1) (throat p.val.2.1) (w p) (fun i=> U i p)
 price : ∀ x (i j:TripC I), i<j→ (crownP P).bkg (U x) i j=F (flavor i) (flavor j) x (throat i) (throat j) -- F parameter infer
lemma crown_factor (f:TripC I→TripC I→ Seal Y→ℂ)(u:Shimmer P→ℂ)(p:∀ i,u i=f i.val.1 i.val.2.1 i.val.2.2)(x y:TripC I)(h:x<y): (crownP P).bkg u x y=∑ s:Seal Y with Emet P x y s,f x y s:=by
 unfold bkg; rw [Matrix.sum_apply]; simp_rw [manifest_lt (crownP P) _ _ x y h]; erw [←sum_filter (p:=fun i:Shimmer P=> x=(crownP P).src i ∧ y=(crownP P).dst i) (f:=u) (s:=univ)]; symm; apply sum_bij (fun s (v : s∈univ.filter _) => (⟨(x,y,s),h,(mem_filter.mp v).2⟩ : Shimmer P)); · intro i p; exact mem_filter.mpr ⟨mem_univ _,rfl,rfl⟩
 · intro i v j t e; exact congrArg (fun i:Shimmer P=> i.val.2.2) e
 · rintro ⟨⟨j,k,l⟩,t,g⟩ v; obtain ⟨r,w⟩:=mem_filter.mp v|>.2; change x=j at r; change y=k at w; subst j; subst k; exact ⟨_,mem_filter.mpr ⟨mem_univ _,g⟩,rfl⟩ -- Src proof.F tune
 intro s v; exact (p ⟨(x,y,s),h,(mem_filter.mp v).2⟩).symm
lemma crown_earn (v:∀ a x,B.Costs P (F a x)): ∃ U w, Offered B (P:=P) (F:=F) U w:=by
 choose K L p q h using v; let D0:=crownP P; let d(x y:TripC I)(S:Seal Y):=L (flavor x) (flavor y) S (throat x) (throat y); let U(z:D)(x y:TripC I)(s:Seal Y):= K (flavor x) (flavor y) s z (throat x) (throat y)
 let W(t: Shimmer P):= d t.val.1 t.val.2.1 t.val.2.2; refine ⟨fun z t=> U z t.val.1 t.val.2.1 t.val.2.2,W,⟨?_,fun i=> (p ..).expo ..,?_⟩⟩; swap
 · intro t x y e; rw [crown_factor (U t) _ (fun t=>rfl) x y e, h _ _ t,Matrix.sum_apply]; apply sum_subset (filter_subset ..); intro i u v; apply norm_eq_zero.mp; have ht: d x y i=0:=by_contra (fun f=>v (mem_filter.mpr ⟨u,((p ..).expo ..).triggered f⟩)); exact le_antisymm (ht ▸ ((p ..).expo ..).bounded t) (norm_nonneg _)
 refine ⟨by unfold χPay; have ht:=B.bought; positivity,fun i=> (p ..).nonn ..,?_⟩; intro x
 let π(i:Shimmer P): SpinIndex × I × Seal Y:= (flavor i.val.2.1, throat i.val.2.1,i.val.2.2); let G(i:SpinIndex × I × Seal Y):= rent B.rate i.2.2* L (flavor x) i.1 i.2.2 (throat x) i.2.1; let X:=D0.holds x; have he(i:Shimmer P)(t:i∈X) : i.val.1=x:= ((mem_filter.mp t).2).symm; have hp : Set.InjOn π X:=by
    intro i u j v e; apply Subtype.ext; refine Prod.ext ((he i u).trans (he j v).symm) (Prod.ext ?_ (congrArg (fun i:SpinIndex × I × Seal Y=> i.2.2) e)); exact (parked _).symm.trans ((congrArg₂ park (show (π i).1=(π j).1 from congrArg Prod.fst e) (show (π i).2.1=(π j).2.1 from congrArg (Prod.fst ∘ Prod.snd) e)).trans (parked _)) -- tune underscore implicit
 rw [show (∑ i∈X,rent B.rate (D0.look i)*W i)=∑ i∈X.image π,G i from ?_]; swap; · rw [sum_image hp]; apply sum_congr rfl; intro i t; change rent B.rate _ *d i.val.1 _ _ = rent B.rate _* L _ _ _ _ _; rw [he i t]; rfl -- tune token
 apply (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> mul_nonneg (rent_pos ..|>.le) ( (p ..).nonn ..))).trans; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; exact (sum_le_sum (g:=fun _:SpinIndex=>B.price) (fun j _=>(q ..).rows _)).trans (by simp [χPay])
end YM.CF.BPress.Spark
