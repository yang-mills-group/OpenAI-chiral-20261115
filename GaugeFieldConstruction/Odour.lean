import GaugeFieldConstruction.Boards

/-!
# Single-leg relation for (89)
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Complex Cauchy Row Wick Phys Function Filter Set
open YM.Maxwell (grad)
open scoped ContDiff Topology BigOperators
variable {α β γ : Type*}

-- derivatives at either end. general tools
lemma propR {f : SmoothGap} {z y:E4} (H : z≠y):ContDiffAt ℝ ∞ (fun y=>eye (y-z) f) y := (Gap.healthy f (sub_ne_zero.mpr H.symm)).comp y (f:=fun y=>y-z) (contDiffAt_id.sub contDiffAt_const)
lemma propR' (f : SmoothGap) (i : Axis) {x y} (p : x≠y) :
    grad i (fun y=> eye (y-x) f) y = eye (y-x) (Gap.step i f) :=
    (Photo.add_shift (Gap.healthy f (sub_ne_zero.mpr p.symm))).trans (Eq.symm (Gap.flash i f (sub_ne_zero.mpr p.symm)))
lemma propL (f : SmoothGap) {x y:E4} (p : x≠y) : ContDiffAt ℝ ∞ (fun x=>eye (y-x) f) x := (Gap.healthy f (sub_ne_zero.mpr p.symm)).comp _ (f:=fun x=>y-x) (contDiffAt_const.sub contDiffAt_id)
lemma propL' (f : SmoothGap) (i : Axis) {x y} (p : x≠y) : grad i (fun x=> eye (y-x) f) x=eye (y-x) (-Gap.step i f) := by
  have hv : HasFDerivAt (fun x:E4=> y-x) (-ContinuousLinearMap.id ℝ E4) x := by
    have he:= ((hasFDerivAt_const y x).sub (hasFDerivAt_id (𝕜:=ℝ) x)); rw [zero_sub] at he; exact he
  have he := Gap.healthy f (sub_ne_zero.mpr p.symm)
  change (fderiv ℝ (f.val ∘ fun x=>y-x) x) _ = _
  rw [fderiv_comp _ (he.differentiableAt (by simp)) hv.differentiableAt,hv.fderiv,map_neg,ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,map_neg, ContinuousLinearMap.id_apply]; rw [show eye (y-x) (Gap.step i f)=_ from Gap.flash i f (sub_ne_zero.mpr p.symm)]; rfl

/-- paid in (z,x,y) order. tag probes on first L→xor may be fermion or pulse. -/
abbrev Coupon (α β : Type*) := J α →ₗ[ℂ] J β →ₗ[ℂ] ℂ
structure Lamp (α β : Type*) where
  pay : Wick.Bil α β
  P : Axis → Module.End ℂ (J α)
  fast (i : Axis) (a b) : pay (P i a) b = - Gap.step i (pay a b)
  -- single-leg contraction out of a stress insertion in (z,x,y) order, including Wick signs
  charge : E4 → E4 → E4 → Axis→Axis→ Coupon α β
  cont {y t z : E4} (r : t≠y) (p : z≠y) (q : z≠t) (i j : Axis) (a b) :
    ContinuousAt (fun w : E4 × E4=>charge w.2 w.1 y i j a b) (t,z)
  climb (x : E4) (v : Axis) (s : ℝ) (y z : E4) (l : road x v s ≠ y) (p : z≠y) (q:z≠ road x v s) (i j : Axis) (a b) :
    HasDerivAt (fun t : ℝ=>charge z (road x v t) y i j a b) (charge z (road x v s) y i j (P v a) b) s
abbrev Lattice := Axis → Axis → ℝ
def Toll (K : Dollars) (A : Lattice) := ∀ i j x,grad i (K j) x=A j i
namespace Lamp
variable (L : Lamp α β) {χ : E4→ℝ} {K : Dollars} {A : Lattice}

def cost (x y : E4): Coupon α β := L.pay.compr₂ (eye (y-x))

def toll (x y : E4) (a : J α) (b : J β) : Forms := fun i j z=> L.charge z x y i j a b
def glow (χ : E4→ℝ) (K : Dollars) (x y : E4) (a : J α) (b : J β):= Shell χ K (L.toll x y a b)

lemma legend {x y : E4} (p : x≠y) (a b) : ContDiffAt ℝ ∞ (fun x=> L.cost x y a b) x := propL (L.pay a b) p
lemma limit {x y : E4} (p : x≠y) (a b k) : grad k (fun x=>L.cost x y a b) x=L.cost x y (L.P k a) b := by
  change grad k (fun x=>eye (y-x) (L.pay a b)) x= eye (y-x) _; rw [propL' _ _ p,L.fast]
lemma beam (B : Course K) (x y p q) (i : Axis) (a : E4×E4) (h:a.1=x) (g:a.2≠y) (z:a.2≠x) (v : x≠y) :
    ContinuousAt (fun w:E4×E4=> currentZ K (L.toll w.1 y p q) i w.2) a := by
  change ContinuousAt (fun w:E4×E4=> ∑ j : Axis,K j w.2 • L.charge w.2 w.1 y i j p q) a
  refine tendsto_finsetSum _ (fun j _=>?_)
  subst x; exact ((B.health j).continuous.comp continuous_snd).continuousAt.smul (L.cont v g z i j p q)
lemma steady (B : Course K) {x y : E4} (c : Chassis x y χ) (a b) (i : Axis) (z : E4) (p : z ∈ Shore χ) :
    ContinuousAt (currentZ K (L.toll x y a b) i) z := (L.beam B x y a b i (x,z) rfl (c.gate p).2.symm (c.gate p).1.symm c.distinct).comp (f:=fun z=>(x,z)) (continuousAt_const.prodMk continuousAt_id)
lemma flight (B : Course K) {x y : E4} (c : Chassis x y χ) (v : Axis) (a b) :
    HasDerivAt (fun t : ℝ=> L.glow χ K (road x v t) y a b) (L.glow χ K x y (L.P v a) b) 0 := by
  apply spends c (fun x=>currentZ K (L.toll x y a b)) (fun x=> currentZ K (L.toll x y (L.P v a) b)) v (fun z v' p q i=> L.beam B _ _ a b i z rfl p q v') (fun z v' p q i=>L.beam B _ _ (L.P v a) b i z rfl p q v')
  intro z p t v' q i; change HasDerivAt (fun t=>∑ j:Axis,K j z • L.charge z (road x v t) y i j a b) (∑ j:Axis,K j z • L.charge z (road x v t) y i j (L.P v a) b) _
  apply HasDerivAt.fun_sum; intro j _; exact (L.climb _ _ t y z v' p q _ _ a b).const_smul (K j z)
lemma total (B : Course K) {x y : E4} (c : Chassis x y χ) (a b v) : L.glow χ K x y (a+b) v=L.glow χ K x y a v+ L.glow χ K x y b v := by
  have H : currentZ K (L.toll x y (a+b) v)= currentZ K (L.toll x y a v)+currentZ K (L.toll x y b v) := by
    ext1 i; ext1 z; simp only [Pi.add_apply,currentZ,toll,map_add,LinearMap.add_apply, smul_add, Finset.sum_add_distrib]
  unfold glow Shell; rw [H,pulse c (L.steady B c a v) (L.steady B c b v)]
lemma tip (z : ℂ) (a : J α) (b : J β) (x y : E4) :L.glow χ K x y (z • a) b=z*L.glow χ K x y a b := by
  unfold glow Shell; rw [← atlas]; congr 1; ext1 i; ext1 w
  simp only [currentZ,toll,map_smul, LinearMap.smul_apply,Pi.smul_apply,Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _=> smul_comm ..

/-- single target label remembers α_i coefficients; write intrinsic rotation p to stay at all derivative domains.
  c is bought also for rotations; input charge = c * (translation+intrinsic).
-/
def Touch (K : Dollars) (c : ℂ) (a p : J α) := ∀ x y χ, Chassis x y χ → ∀ d,
    L.glow χ K x y a d = c*(L.cost x y p d+∑ i:Axis,K i x • L.cost x y (L.P i a) d)

lemma plus (B : Course K) {c a b p q} (g : L.Touch K c a p) (h : L.Touch K c b q) : L.Touch K c (a+b) (p+q) := by
  intro x y χ t d; rw [L.total B t,g x y χ t d,h x y χ t]; simp only [map_add,LinearMap.add_apply,smul_add,Finset.sum_add_distrib,mul_add]; abel
lemma wish {c a p} (g : L.Touch K c a p) (r : ℂ): L.Touch K c (r • a) (r • p) := by
  intro x y χ t d; rw [tip L r _ _,g x y χ t]; simp only [map_smul,LinearMap.smul_apply]; simp_rw [show ∀ i : Axis,K i x • r • (L.cost x y (L.P i a) d)= r • K i x • (L.cost x y (L.P i a) d) from fun i=>smul_comm ..,← Finset.smul_sum,smul_eq_mul]; ring
lemma expand (B : Course K) (P : Toll K A) {a p : J α} {r : ℂ} (h : L.Touch K r a p) (v : Axis) :
    L.Touch K r (L.P v a) (L.P v p+∑ i : Axis, (↑(A i v):ℂ) • L.P i a) := by
  intro x y χ c d
  let q (z : E4) := L.cost z y p d+∑ i : Axis,K i z • L.cost z y (L.P i a) d
  have ht (a) := L.legend (b:=d) c.distinct a
  have pd := c.distinct
  have H i :ContDiffAt ℝ ∞ (fun z=>K i z • L.cost z y (L.P i a) d) x:= (B.health i).contDiffAt.smul (ht _)
  have he : HasDerivAt (fun t:ℝ=> r*q (road x v t)) (r*grad v q x) 0:= HasDerivAt.const_mul _ (One.fast (F:=q) ((ht p).add (ContDiffAt.sum fun i _=>H i))) -- tune
  have ep : L.glow χ K x y (L.P v a) d = r*grad v q x := (L.flight B c v a d).unique (he.congr_of_eventuallyEq (by
    have ht :Tendsto (road x v) (𝓝 0) (𝓝 x):=by simpa only [p0] using (ridge x v).continuousAt (x:= (0:ℝ)) |>.tendsto
    filter_upwards [ht c.route] with z hz; exact h _ _ _ hz d))
  rw [ep]; unfold q
  have hx (i): L.cost x y (L.P v (L.P i a)) d=L.cost x y (L.P i (L.P v a)) d := by
    change eye (y-x) _=eye (y-x) _; repeat rw [L.fast]
    simp only [map_neg,neg_neg]; congr 1; exact LinearMap.congr_fun (Gap.collide v i) (L.pay a d) -- adjust
  have hi (i): grad v (fun z=>K i z • L.cost z y (L.P i a) d) x = A i v • L.cost x y (L.P i a) d + K i x • L.cost x y (L.P i (L.P v a)) d := by
    rw [here_dollar (B.health i).contDiffAt (ht _) v,limit L pd,hx,P v i]
  have hu : grad v (fun z=> L.cost z y p d+∑ i : Axis,K i z • L.cost z y (L.P i a) d) x=
      grad v (fun z=> L.cost z y p d) x+grad v (fun z=> ∑ i:Axis,K i z • L.cost z y (L.P i a) d) x := by
    unfold YM.Maxwell.grad YM.Analysis.D; rw [fderiv_fun_add ((ht p).differentiableAt (by simp)) ((show ContDiffAt ℝ ∞ (fun z=> ∑ i:Axis,K i z • L.cost z y (L.P i a) d) x from ContDiffAt.sum (fun i _=> H i)).differentiableAt (by simp))]; rfl
  rw [hu,L.limit pd p d v,here_sum (v:=Finset.univ) (fun i _=> H i)]
  simp_rw [hi, Finset.sum_add_distrib,map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply,map_smul,LinearMap.smul_apply]; congr 1
  rw [← add_assoc]; simp only [real_smul]; rfl
end Lamp
end YM.GaugeFieldConstruction.Flux.One
