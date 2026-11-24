import YM.CF.Fixed.Voltage.Review
import YM.CF.Fixed.Voltage.MineV
/-! Small readdressing savings. Same Auth powers and locality requirements. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.Fixed.Voltage
open Function NormedSpace Filter Metric Finset Lattice Wilson SU Scree Skye Fock Lat Cube MeasureTheory Vow RG Rue Spire Scroll
open Vow Ione Beau
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{x a b h u v:ℝ}(P:BudgetPoint)(D:Support (More n)){R Q:ForceBudget n}{E E':RegBudget n}
variable {K:ℕ}(τ:Sweep n→Prop)
local notation "N"=> More n
local notation "A"=> deck_F P D
lemma upgradeI(g:IncX τ E P h a)(u:a≤x): IncX τ E P h x:= by obtain ⟨⟨f,g,k⟩,t⟩:=g; exact ⟨⟨f,g,fun i=>(k i).trans u⟩,t⟩
lemma upgradeD(g:Dark τ R P h a)(u:a≤x): Dark τ R P h x:= by obtain ⟨⟨f,g,k⟩,t⟩:=g; exact ⟨⟨f,g,fun i=>(k i).trans u⟩,t⟩
lemma crestV(g:IncX τ E P h a)(x:ℝ): IncX τ (x • E) P h (|x| * a):=
  ⟨(Ione.thin_P P E x ⟨g.weight,fun _ k=>k.elim⟩).weight,fun s S V v i U=> by
    simp only [Pi.smul_apply, map_smul]; exact congrArg _ (g.face s S V v i U)⟩ -- tune abi
-- FROM d8 `Roots`: economic addition. Changing absolute polynomial bookings OK
private lemma bundle_F (T:Force n)(F G:Copy n)(p:ForceB P T F h v)(w:ForceB P T G h u):ForceB P T (F+G) h (v+u):=by
 obtain ⟨c,h,x,y⟩:=p.costP; obtain ⟨k,v,α,g⟩:=w.costP
 refine ⟨fun V W t e g z=> congrArg₂ (·+·) (p.values _ _ _ _ g z) (w.values _ _ _ _ g z),fun i=>(p.fitted i).add (w.fitted i),fun t=> by rw [p.flagsV t,w.flagsV t,add_zero],p.measureV.add w.measureV,fun i t=> ?_, fun i z y=>(congrArg₂ (·+·) (p.gaugeV i z y) (w.gaugeV i z y)).trans (map_add ..).symm,c+k,fun j=>add_nonneg (h j) (v j),fun i z j=>Prism.tack (x i z j) (α i z j),by simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add y g⟩
 by_cases w':F i=0; · refine w.protect _ ?_; intro z; rw [Pi.add_apply,w',z,add_zero] at t; contradiction
 exact p.protect _ w'
lemma cloudy(u: Dark τ R P h a)(v: Dark τ Q P h b):Dark τ (R+Q) P h (a+b):=by
 obtain ⟨f,g,t⟩:=u.weight; obtain ⟨c,p,x⟩:=v.weight; refine ⟨⟨f+c,fun i=> bundle_F P i _ _ (g i) (p i),fun i=>?_⟩,fun s S V B X W T p=> (congrArg₂ (·+·) (u.face s S V B X W T p) (v.face s S V B X W T p)).trans (map_add ..).symm⟩
 let κ(z:Force n→ℝ):=fun j:Force n=>if i∈j.val.1.val.2 then P.mass j.val.1.val.2 (z j) else 0; have heB(j):κ (f+c) j=κ f j+κ c j:=by
   unfold κ; split; · unfold BudgetPoint.mass; rw [Pi.add_apply,mul_add]
   exact (zero_add ..).symm
 change (∑ j,κ (f+c) j) ≤ a+b; simp_rw [heB,sum_add_distrib]; exact add_le_add (t _) (x i)
structure Lord(E:RegBudget n)(b h:ℝ)(K:ℕ): Prop where
 tax:IncX Utrue E P h b
 theme:Ionic P K E
namespace Lord
variable {P}(T:Lord P E b h K)(p:0≤h)
private lemma pace (T:Lord P E b h K) : IncX (fun _=>False) E P h b:=⟨T.tax.weight,fun _ f=>f.elim⟩
include T p
lemma scale(x:ℝ): Lord P (x • E) (|x| * b) h K:= ⟨crestV _ _ T.tax _, night_k T.theme p (T.pace) _⟩
lemma merge(S:Lord P E' a h K): Lord P (E+E') (b+a) h K:=⟨ Ione.addT P T.tax S.tax, Beau.wage_add T.theme S.theme T.pace S.pace p⟩
omit T p in
lemma empty:Lord P (0:RegBudget n) 0 h K:=⟨ (Vale.lye (Utrue) P h).1, fun _ _ _=> Beau.none_q _⟩
omit p in
lemma uprate(hc:b≤x):Lord P E x h K:=⟨upgradeI P _ T.tax hc,T.theme⟩
omit T in
lemma pileL {I:Type*}(X:Finset I)(G:I→ RegBudget n)(d:I→ℝ)(g:∀ i∈X,Lord P (G i) (d i) h K):Lord P (∑ i∈X,G i) (∑ i∈X, d i) h K:=by induction X using Finset.induction_on with|empty=>rw [sum_empty,sum_empty]; exact empty|insert i X q ih=> rw [sum_insert q,sum_insert q]; exact (g i (mem_insert_self ..)).merge p (ih fun i' w=> g i' (mem_insert_of_mem w))
end Lord
end YM.CF.Fixed.Voltage
