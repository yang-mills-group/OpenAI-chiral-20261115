import Anomaly.Rack.Receive
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
variable (f:I→ Bag n) (p q': I→ Aura n→ℝ) (T:∀ (i:I)(X:Aura n),Flight P q X h (f i X) (p i X) (q' i X))
include T

lemma digit_extract (X:Aura n)(Y:Aura n)(D:Support (More n))(F:Copy n)(j:I)(v : Orbit n) :
    tipI (fun z:Key I=> zealPitch f p q' T z X D Y F v) [j]=jetSlice f p q' T j X D Y F v := by
  have e:River (fun z:Key I=> zealPitch f p q' T z X D Y F v) := by
    simp_rw [zeal_scales, Finset.sum_apply, Pi.smul_apply]; apply Solvent.riv (i:=1); refine Solvent.sum _ _ ?_; intro i _
    exact Solvent.pair (j:=0) (LinearMap.lsmul ℂ _) (Solvent.bill i) (Solvent.still _)
  let K:=fun z:Key I=> zealPitch f p q' T z X D Y F v
  change cutI K j 0=_
  have hX(x:ℂ): K (Function.update 0 j x)=x • jetSlice f p q' T j X D Y F v:=by unfold K; rw [zeal_scales, Finset.sum_apply, sum_eq_single j,update_self]; rfl; intro i _ p'; rw [update_of_ne p',Pi.smul_apply]; exact zero_smul ..; simp
  rw [← (mitt (show River K from e) roots j).deriv]; simp_rw [hX]
  simpa using ((hasDerivAt_id' (0:ℂ)).smul_const (jetSlice f p q' T j X D Y F v)).deriv

open Bake
variable (t : Ids n)(x:Seat n)
local notation "τ" a:max X:max=> (jetSlice f p q' T a X ∅ X 1)

-- Proof-param reason. root A.
def singleReceipt (T:∀ (i:I)(X:Aura n),Flight P q X h (f i X) (p i X) (q' i X))(t: Ids n)(i:I)(x:Seat n)(U: Scree.Hub n) : InkD n:= if U.val.1=x then fun V=> (jetSlice f p q' T i (lagE U) ∅ (lagE U) 1) (V,t) else 0
variable (i:I)
local notation "F🌅"=> singleReceipt f p q' T t i x
lemma SpanTip_at (v:∀ Y:Aura n,x∉Y.val → f i Y=0) : SpanTip P (singleReceipt f p q' T t i x) x (zealPitch f p q' T) t i := by
  refine ⟨fun A V _=>?_, fun Y U H u=>?_⟩
  · rw [singleReceipt,digit_extract]; split_ifs <;> rfl
  rw [digit_extract,jetSlice, Bias.payX]; split; swap; · rfl
  apply Subtype.ext; change Sault.rind (coll_T P Y ∅ _ _*_)=0; rw [v _ u]; simp [coll_T,Sault.rind]

lemma dedicate (g:3≤P.B)(p_:0≤h) (U:Aura n): Fray P h (cipherK q) U ∅ (jetSlice f p q' T i U ∅ U 1) (q' i U):=by
  unfold jetSlice Bias.payX; rw [dif_pos (show Bias.αt U U ∅ (cipherK q) from ⟨Subset.refl _,empty_subset _,by simp [Lattice.halo]⟩)]; exact Fringe.burn _ ((T i U).birth U (Subset.refl _))

-- cost at p*, using same $Ω$. Already Grove rooted all footprints.
lemma dedicate_fixed (U:Aura n)(r s:Ids n)(V:Pane n) :
    (τ i U) (V,r)=(τ i U) (V,s):=by
  let Z(X):= (T i X).tube.title
  let K:= Title.powerQ (f i) (p i) Z
  exact opva (p i) (V,s) K (fun X Y v x h j=>(T i X).tube.clean _ v x h j) r U U _ _ rfl

lemma dedicate_medal (X:Scree.Hub n)(u:X.val.1=x) (g:3≤P.B)(hx:0≤h) : Medal P X.val.2 ∅ (oV ((F🌅) X)) h (q' i (lagE X)) := by
  have hv:= (dedicate f p q' T i g hx (lagE X)).merit
  rw [show oV ((F🌅) X) = τ i (lagE X) from ?_]
  · exact hv
  funext V; unfold oV singleReceipt; rw [if_pos u]; exact dedicate_fixed f p q' T i (lagE X) t V.2 V.1

abbrev meritChart (Y: Aura n → ℝ)(p:BudgetPoint)(X:Scree.Hub n):ℝ := fareX p.B p X.val.2 * Y (Bake.lagE X)
abbrev formalCost (σ:Seat n)(Y:Aura n→ℝ)(p:BudgetPoint)(X:Scree.Hub n):ℝ:= if X.val.1=σ then meritChart Y p X else 0
lemma heated (g:3≤P.B)(hp:0≤h)(X:Scree.Hub n) : PressB P X ((F🌅) X) h (formalCost x (q' i) P X):=by
  unfold formalCost; split; next v=> exact ((dedicate_medal f p q' T t x i X v g hp).preservesE t hp P.B)
  next v=> rw [singleReceipt,if_neg v]; exact Vale.rinse ..

omit T
lemma birth_tally {k:ℝ}(v:Aura n→ℝ)(p:BudgetPoint)(e a:ℝ)(he:0<e)(u:0 ≤ v)(hx:voyageB v p.B (p.supportExponent+k+e) ≤ a):
    (∑ X:Scree.Hub n,massPlus p k X.val.2 (formalCost x v p X)) ≤ Nor.reserveT p.power p.order p.B e*a:=by
  apply le_trans ?_ (mul_le_mul_of_nonneg_left hx (by unfold Nor.reserveT Nor.coin_n Nor.stilK; positivity))
  unfold formalCost; have hy(X:Scree.Hub n):massPlus p k X.val.2 0=0:=mul_zero _
  simp_rw [massPlus, mul_ite, mul_zero]
  rw [←sum_filter]; unfold voyageB; rw [mul_sum]; let Q:=univ.filter (fun V:Scree.Hub n=> V.val.1=x)
  rw [←Finset.sum_fiberwise_of_maps_to (s:=Q) (t:= (univ:Finset (Aura n))) (g:=lagE) (fun i _=>mem_univ _)]
  apply sum_le_sum; intro X _
  by_cases h:x∈X.val
  · let K : Scree.Hub n := ⟨(x,X.val),h⟩; have hv: lagE K=X:=Subtype.ext rfl
    rw [sum_eq_single_of_mem (s:=Q.filter (fun i=>lagE i=X)) K (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,hv⟩)]; swap
    · intro j t v; exact False.elim (v (Subtype.ext (Prod.ext (mem_filter.mp (mem_filter.mp t).1).2 (congrArg Subtype.val (mem_filter.mp t).2))))
    unfold meritChart; rw [hv]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nor.coinPay _ _ _ he) (u X)) (Real.exp_pos _).le); apply le_of_eq; unfold Sour.tact Sour.widthK; rw [add_mul (p.supportExponent+k) e, Real.exp_add ((p.supportExponent+k)*_)]; unfold K; dsimp only; ring
  have hc:Nor.reserveT p.power p.order p.B e≥0:=by unfold Nor.reserveT Nor.coin_n Nor.stilK; positivity
  apply le_trans ?_ (mul_nonneg hc (mul_nonneg (u X) (Real.exp_pos _).le)); apply le_of_eq; exact sum_eq_zero (fun i u=>False.elim (h ((congrArg Subtype.val (mem_filter.mp u).2) ▸ ((mem_filter.mp (mem_filter.mp u).1).2 ▸ (show i.val.1∈(lagE i).val from i.property))))) -- tune casts

/-- The `p*` receipt in the power-counting aperture is also bought on
these first tips (core `grooveB 24` for current at this stage;
optimizing or merging afterwards is separate). In fact get it for every
such capsule. -/
def pStar (p:BudgetPoint):BudgetPoint:={p with power := 3, power_ge:=by norm_num}

include T

lemma birth_Star (hP:3 ≤ P.B)(hp:0 ≤ h)(X:Scree.Hub n) :
    PressB (pStar P) X ((F🌅) X) h (formalCost x (q' i) (pStar P) X):=by
  unfold formalCost
  split
  next u =>
    obtain ⟨H,A_,a,b,c⟩:= dedicate_medal f p q' T t x i X u hP hp
    have p:Medal (pStar P) X.val.2 ∅ (oV ((F🌅) X)) h (q' i (lagE X)):= ⟨H,A_,a,b,c⟩
    exact p.preservesE t hp _
  next u=> rw [singleReceipt,if_neg u]; exact Vale.rinse ..

lemma offRoot (H:Support (More n))(u:∀ Y:Aura n,¬H ⊆ Y.val → f i Y=0)(X:Scree.Hub n)(v:¬ H⊆X.val.2):
    (F🌅) X=0:=by
  unfold singleReceipt
  split; swap; · rfl
  funext k; apply Subtype.ext; unfold jetSlice Bias.payX; split; swap; · rfl
  change Sault.rind (coll_T P (lagE X) ∅ _ _*_)=0
  rw [u _ v]; simp [coll_T,Sault.rind]

lemma station (X:Scree.Hub n)(v:X.val.1 ≠ x): (F🌅) X=0:=by unfold singleReceipt; exact if_neg v
omit T

open Py -- for primeU
variable {N B:Side}

lemma composeInc {P:BudgetPoint}(σ:I→Seat n) (K : I→RegBudget n) (t:ℕ) (a:ℝ) (hx:0≤a) -- use t times uniform
    (g:Force_M P.B σ t) (p:∀ i:I,IncX primeU (K i) P h a)(hp:0≤h)(w:∀ X:Scree.Hub n,∀ i:I,X.val.1≠σ i→K i X=0) (z:Key I)(c:ℝ)(he:0≤c)(L:∀ i,‖z i‖≤c):
    IncX primeU (core_C K z) P h (t*(c*a)) := by
  choose F Hv H using fun i:I=> (p i).weight
  let U(X:Scree.Hub n):= univ.filter fun i:I=>X.val.1=σ i
  let X(i:Scree.Hub n):=∑ j∈U i,‖z j‖* F j i
  refine ⟨⟨X,fun i=>?_,fun o=>?_⟩,fun j c=> False.elim c⟩
  · let T:=Larch.prop_sum (U i) (fun j=> z j • K j i) _ _ _ i (fun j _=> (súe _ _ (Hv j i) _)); -- name.sue tune
    unfold core_C; rw [Finset.sum_apply,← Finset.sum_subset (show U i⊆_ from subset_univ _)]; exact T
    intro j _ b; have hx:=w i j (fun t=>b (mem_filter.mpr ⟨mem_univ _,t⟩)); rw [Pi.smul_apply,hx,smul_zero]
  rw [←sum_filter]; let S:= univ.filter fun i:Scree.Hub n=>o=i.val.1; let V:= univ.filter fun i:I=>σ i=o
  let f(i):= fun j:Scree.Hub n=> if o=j.val.1 then P.mass j.val.2 (F i j) else (0:ℝ)
  have T (i:Scree.Hub n)(p:i∈S) : P.mass i.val.2 (X i)= ∑ j∈V, ‖z j‖*f j i:=by
    have t:o=i.val.1:= (mem_filter.mp p).2; unfold BudgetPoint.mass X; rw [show U i=V from (by ext; simp [U,V,t,eq_comm]),mul_sum]; refine sum_congr rfl ?_; intro j _; unfold f; rw [if_pos t]; unfold BudgetPoint.mass; ring
  rw [Finset.sum_congr rfl (s₁:=S) T,sum_comm]
  simp_rw [←Finset.mul_sum]
  refine le_trans (sum_le_sum (g:=fun _=>c*a) fun j _=> ?_) ?_
  · have hv:(∑ i∈S,f j i)=∑ i:Scree.Hub n,f j i:= by apply Finset.sum_subset (subset_univ _); intro i _ v; exact if_neg fun p=> v (mem_filter.mpr ⟨mem_univ _,p⟩)
    rw [hv]; exact (mul_le_mul_of_nonneg_left (H j o) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (L j) hx)
  rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (pinsFromLamp g.2 o)) (mul_nonneg he hx)
end YM.CF.Vow.TreasuryFog
