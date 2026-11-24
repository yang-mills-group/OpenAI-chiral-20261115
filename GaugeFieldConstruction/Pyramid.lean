import GaugeFieldConstruction.Lux

/-!
# Wick cycles for z x y.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One.Lamp
open Gap Cauchy Row Wick Phys Function Set Filter Complex
open scoped Topology ContDiff BigOperators
variable {α β γ η : Type*} (L : Lamp α β) (N : Lamp γ η)
def lugs (f : Coupon α β) (g : Coupon γ η) : Coupon (α×γ) (β×η) := jet fun a=> productRead (f (ket a.1)) (g (ket a.2))
lemma sunny (f : Coupon α β) (g : Coupon γ η) (a b c d): lugs f g (times' a b) (times' c d)=f a c*g b d := by
  let R:=f.flip c; let S:=g.flip d
  have h: (lugs f g).flip (times' c d)=productRead R S := ket_ext fun i=>by
    change lugs _ _ _ _=_; rw [lugs,on_ket, read_times,productRead,on_ket]; rfl
  change (lugs f g).flip _ _=_; rw [h,read_times]; rfl

/-- Ordered legs: one allocation. -/
def area (z x y i j) := lugs (L.charge z x y i j) (N.cost x y) + lugs (L.cost x y) (N.charge z x y i j)
lemma stretch (z x y) (i j) (a b c d): L.area N z x y i j (times' a b) (times' c d) =
    L.charge z x y i j a c*N.cost x y b d+ L.cost x y a c*N.charge z x y i j b d := by
  simp only [area, LinearMap.add_apply,sunny]
lemma carry (z : E4) {x y:E4} (p:x≠y) (a b) :ContinuousAt (fun w:E4×E4=>L.cost w.1 y a b) (x,z):= by
  exact ContinuousAt.comp (x:=(x,z)) (f:=Prod.fst) (g:=fun x=>L.cost x y a b) (L.legend p a b).continuousAt continuousAt_fst
lemma gammaE {s v z x y} (r:x≠y) (p:z≠y) (h:z≠x) (a b) :
    ContinuousAt (fun w:E4×E4=>area L N w.2 w.1 y s v a b) (x,z) := by
  have ht i (b : J (β×η)): ContinuousAt (fun w:E4×E4=>area L N w.2 w.1 y s v (ket i) b) (x,z) := by
    induction b using Finsupp.induction_linear with
    | zero=> simp only [map_zero]; exact continuousAt_const
    | add a b f g=> simp only [map_add]; exact f.add g
    | single j t=>
      rw [show Finsupp.single j t=t • ket j from by simp [ket]]; simp only [map_smul]
      rw [← takes i.1 i.2,← takes j.1 j.2]; simp_rw [stretch]
      simp only [smul_eq_mul]; apply ContinuousAt.mul continuousAt_const
      have e:ContinuousAt (fun w : E4 × E4=> L.cost w.1 y (ket i.1) (ket j.1)) (x,z):= carry L z r _ _
      have hq:ContinuousAt (fun w : E4 × E4=> N.cost w.1 y (ket i.2) (ket j.2)) (x,z):= carry N z r _ _
      exact ((L.cont r p h s v (ket i.1) (ket j.1)).mul hq).add (e.mul (N.cont r p h s v (ket i.2) (ket j.2)))
  induction a using Finsupp.induction_linear with
  | zero=> simp only [map_zero, LinearMap.zero_apply]; exact continuousAt_const
  | add a b f g=>simp only [map_add,LinearMap.add_apply]; exact f.add g
  | single i v=>
    rw [show Finsupp.single i v= v • ket i from by simp [ket]]; simp only [map_smul,LinearMap.smul_apply]
    exact (continuousAt_const (x:= (x,z)) (y:=v)).smul (ht i b)
lemma gammaD (x i t y z) (v : road x i t≠y) (h : z≠ y) (p : z≠ road x i t) (s k a b) :
    HasDerivAt (fun t=>area L N z (road x i t) y s k a b) (area L N z (road x i t) y s k (splitD (L.P i) (N.P i) a) b) t := by
  have hv (a b c d) : HasDerivAt (fun t=>area L N z (road x i t) y s k (times' a b) (times' c d)) (area L N z (road x i t) y s k (splitD (L.P i) (N.P i) (times' a b)) (times' c d)) t := by
    simp_rw [split_legs, map_add,LinearMap.add_apply, stretch]
    have e : HasDerivAt (fun t=> N.cost (road x i t) y b d) (N.cost (road x i t) y (N.P i b) d) t := (speedy (N.legend v b d)).congr_deriv (N.limit v ..)
    have f : HasDerivAt (fun t=> L.cost (road x i t) y a c) (L.cost (road x i t) y (L.P i a) c) t:= (speedy (L.legend v a c)).congr_deriv (L.limit v ..)
    exact ((((L.climb x i t y z v h p s k a c).mul e).add (f.mul (N.climb x i t y z v h p s k b d))).congr_deriv (by abel))
  have H a (b : J (β×η)) :HasDerivAt (fun t=>area L N z (road x i t) y s k (ket a) b) (area L N z (road x i t) y s k (splitD (L.P i) (N.P i) (ket a)) b) t := by
    induction b using Finsupp.induction_linear with
    | zero=> simpa only [map_zero] using! hasDerivAt_const t (0:ℂ)
    | add a b f g=> simp only [map_add]; exact f.add g
    | single j t=> rw [show Finsupp.single j t=t • ket j from by simp [ket]]; simp only [map_smul]; rw [← takes a.1 a.2,← takes j.1 j.2]; exact (hv (ket a.1) (ket a.2) (ket j.1) (ket j.2)).const_smul (𝕜:=ℝ) t -- args fix
  induction a using Finsupp.induction_linear with
  | zero=> simpa only [map_zero, LinearMap.zero_apply] using! hasDerivAt_const t (0:ℂ)
  | add a b f g=>simp only [map_add,LinearMap.add_apply]; exact f.add g
  | single i t=>
    rw [show Finsupp.single i t= t • ket i from by simp [ket]]; simp only [map_smul,LinearMap.smul_apply]
    exact (H i b).const_smul (𝕜:=ℝ) t

def elect : Lamp (α×γ) (β×η) where
  charge:=area L N
  P i:=splitD (L.P i) (N.P i)
  pay:=weave' L.pay N.pay
  fast i:=fades _ _ _ _ _ (L.fast i) (N.fast i)
  cont:=fun r p h _ _ a b=> gammaE L N r p h a b -- tune
  climb:=gammaD L N
lemma wheel (a b c d) (x y): (L.elect N).cost x y (times' a b) (times' c d)=L.cost x y a c*N.cost x y b d := by
  change eye (y-x) (weave' _ _ _ _)=_; rw [arrive,tick]; rfl
lemma glow2 {K χ x y} (p : Course K) (h : Chassis x y χ) (a b c d) :
    (L.elect N).glow χ K x y (times' a b) (times' c d) = L.glow χ K x y a c*N.cost x y b d+ L.cost x y a c*N.glow χ K x y b d := by
  let F:= currentZ K (L.toll x y a c); let G:=currentZ K (N.toll x y b d)
  let U:=N.cost x y b d; let V:=L.cost x y a c
  have ht : currentZ K ((L.elect N).toll x y (times' a b) (times' c d))= U • F + V • G := by
    ext1 i; ext1 z; change ∑ j:Axis,K j z • area L N z x y i j (times' a b) (times' c d)= _
    rw [show (U • F+V • G) i z= U • (∑ j:Axis,K j z • L.charge z x y i j a c)+V • (∑ j:Axis,K j z • N.charge z x y i j b d) from rfl]
    simp_rw [stretch, Finset.smul_sum,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
    unfold U V; simp only [real_smul,smul_eq_mul]; ring
  have hf i z (u : z∈ Shore χ):ContinuousAt ((U • F) i) z:=(continuousAt_const (y:=U)).smul (L.steady p h a c i z u)
  have hg i z (u : z∈ Shore χ):ContinuousAt ((V • G) i) z:=(continuousAt_const (y:=V)).smul (N.steady p h b d i z u)
  rw [glow, Shell,ht,pulse (J:= U • F) (J':= V • G) h hf hg, atlas, atlas]; rw [mul_comm U]; rfl
lemma income_s {K χ x y} (p : Course K) (h : Chassis x y χ) (a c d) : L.glow χ K x y a (c+d)=L.glow χ K x y a c+ L.glow χ K x y a d := by
  have ht :currentZ K (L.toll x y a (c+d))=currentZ K (L.toll x y a c)+currentZ K (L.toll x y a d):= by ext1 i; ext1 z; simp only [Pi.add_apply,currentZ,toll,map_add,smul_add,Finset.sum_add_distrib]
  unfold glow Shell; rw [ht,pulse h (L.steady p h a c) (L.steady p h a d)]
lemma warm_s {K χ x y} (r : ℂ) (a c) : L.glow χ K x y a (r • c) = r*L.glow χ K x y a c:=by
  unfold glow Shell; rw [← atlas]; congr 1; ext1 i; ext1 z
  simp only [currentZ,toll, map_smul,Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=>smul_comm ..)

/-- Local balance. From `Touch` even if not all charged. -/
def Latch (χ : E4→ℝ) (K : Dollars) (x y : E4) (a v : J α):=∀ d,L.glow χ K x y a d=L.cost x y v d
lemma receives {χ K x y a b c} (t : L.Touch K c a b) (v : Chassis x y χ) : L.Latch χ K x y a (c • (b + ∑ i:Axis,(K i x:ℂ) • L.P i a)) := by
  intro d; rw [t x y χ v]; simp only [map_smul,map_add,map_sum,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply]; congr 1
lemma sum_pay {K : Dollars} {χ x y a b U V} (p : Course K) (q : Chassis x y χ) (u : L.Latch χ K x y a U) (v : N.Latch χ K x y b V): (L.elect N).Latch χ K x y (times' a b) (times' U b+ times' a V):=by
  intro w; induction w using Finsupp.induction_linear with
  | zero => simp [glow,Shell,Flux, currentZ, toll,YM.Maxwell.Free.exportFlux]
  | add c d f g=> rw [income_s (L.elect N) p q, f,g]; rw [map_add ((elect L N).cost x y _)]
  | single i t=> rw [show Finsupp.single i t=t • ket i from by simp [ket],← takes i.1 i.2,warm_s,glow2 L N p q,u,v]
                 rw [map_smul,map_add,LinearMap.add_apply,wheel,wheel]; rfl
lemma merger {K a b r s c} (p : Course K) (h : L.Touch K c a r) (g : N.Touch K c b s): (L.elect N).Touch K c (times' a b) (times' r b+times' a s) := by
  intro x y χ t d; rw [sum_pay L N p t (L.receives h t) (N.receives g t) d]
  have e (i) : (L.elect N).P i (times' a b)= times' (L.P i a) b + times' a (N.P i b) := split_legs ..
  simp only [map_add,map_sum, LinearMap.add_apply, LinearMap.sum_apply,map_smul,LinearMap.smul_apply,e,map_add, LinearMap.add_apply, real_smul,smul_eq_mul]; simp [Finset.sum_add_distrib,mul_add,Finset.mul_sum]; abel
end YM.GaugeFieldConstruction.Flux.One.Lamp
