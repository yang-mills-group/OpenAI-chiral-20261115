import GaugeFieldConstruction.Hearths

/-!
# Specialization to singular & outer legs. Derivative on outside near z.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Cauchy Row Wick Phys Function Filter Set Complex
open YM.Maxwell (grad)
open scoped Topology BigOperators ContDiff
open Matter (Slot)
variable {x y z : E4}

abbrev intact (y : E4) := ({y}:Set E4)ᶜ

/-- Outgoing germ at point distinct from y. -/
def outF (b : Bool) (y : E4) (x z) (i : FW) := eye (y-z) (yarn b x i)
def outG (y : E4) (x z) (i : PW) := eye (y-z) (ge x i)
lemma paidF (d : Bool) {z:E4} (h : z∈ intact y) (p q k) :
    grad k (fun x=> outF d y p x q) z=outF d y (stride d k p) z q := (Glove 0 d).limit h p q k -- Q unresolved
lemma paidG {z:E4} (h:z∈intact y) (p q k) : grad k (fun x=>outG y p x q) z=outG y (lace k p) z q := (Flash 0).limit h p q k

def fullF (b : Bool) (y : E4) (s : Slot) (q : FW) : Tissue.Rtil := fun a x=>outF b y (sessionF s a) x q
def fullG (y : E4) (s :Pig) (q : PW) : Forms := fun a b x=> outG y (sectionG s a b) x q
lemma u_f (b i a): ∑ k:Axis,∑ c:Spin,Tissue.M b k c a • stride b k (sessionF i c)=0 := by
  suffices E : ∑ k:Axis,∑ c:Spin,Tissue.M b k c a • Cder b k (C c 0)=0 by
    unfold stride sessionF; simp_rw [← Phys.here,← map_smul (atop i),← map_sum (atop i)]; rw [E,map_zero]
  apply Row.skin b; intro w; rw [LinearMap.mem_ker]
  change (w.val.fermi b).read _=_; let Q:= w.val.fermi b
  change Q.read _=_
  rw [map_sum]; simp_rw [map_sum,map_smul]
  have he k c: Q.read (Cder b k (C c 0))=Q.p k*Q.u c := by
    rw [← LinearMap.comp_apply,Q.frequency,LinearMap.smul_apply]; simp [power]
  simp_rw [he,smul_eq_mul, mul_comm (Tissue.M _ _ _ _ : ℂ)]; exact Q.chiral a
lemma out_law (b y k v): Tissue.Law b (fullF b y k v) (intact y) := by
  constructor
  · intro i z h; exact (Glove 0 b).legend h (sessionF k i) v
  intro i z h; have e := congr_arg (fun x => (Glove 0 b).cost z y x v) (u_f b k i)
  simp only [map_sum, LinearMap.sum_apply,map_smul, LinearMap.smul_apply,map_zero,LinearMap.zero_apply] at e
  unfold Tissue.sig fullF; simp_rw [paidF _ h]; exact e

lemma u_g (s : Pig):
    (∀ a b c, lace a (sectionG s b c)+lace b (sectionG s c a)+lace c (sectionG s a b)=0) ∧
    (∀ j, ∑ i:Axis,lace i (sectionG s i j)=0) := by
  have ht (p : Maxwell) i j: p.read (F i j)=p.skin i j := by rw [Maxwell.read_F]; simp [power,Maxwell.skin] -- skin defined?
  have he (p : Maxwell) k i j: p.read (Gder k (F i j))=p.p k * p.skin i j:= by rw [← LinearMap.comp_apply,p.frequency,LinearMap.smul_apply,ht]; rfl
  unfold lace sectionG; simp_rw [← Phys.here]; constructor
  · intro i j k; have hv : Gder i (F j k)+Gder j (F k i)+Gder k (F i j)=0 := by
      apply loyalty; intro a; rw [LinearMap.mem_ker]; let p:= a.1.val.face a.2; change p.read _=_; rw [map_add,map_add,he,he,he]; exact p.rigor.closed ..
    rw [← map_add,← map_add,hv,map_zero]
  intro j; have hv: ∑ i:Axis,Gder i (F i j) = 0 := by
    apply loyalty; intro a; rw [LinearMap.mem_ker]; let p:=a.1.val.face a.2; change p.read _=_; simp_rw [map_sum,he]; exact p.rigor.div j
  rw [← map_sum,hv,map_zero]
lemma out_wave (y s v): YM.Maxwell.WaveOn (intact y) (fullG y s v) := by
  constructor
  · intro i j x h; exact (Flash 0).legend h (sectionG s i j) v
  · intro i j x _; unfold fullG outG
    conv_lhs=> rw [sectionG,U1.Gauge97.turnover i j]
    simp only [map_neg, sectionG,LinearMap.neg_apply]
  · intro i j k x h
    unfold fullG; rw [paidG h,paidG h,paidG h]
    have e:=congr_arg (fun p=> (Flash 0).cost x y p v) ((u_g s).1 i j k); simp only [map_add,map_zero, LinearMap.add_apply,LinearMap.zero_apply] at e; exact e
  intro j x h; unfold fullG; simp_rw [paidG h]
  have e:=congr_arg (fun p=> (Flash 0).cost x y p v) ((u_g s).2 j); simp only [map_sum,map_zero,LinearMap.sum_apply,LinearMap.zero_apply] at e; exact e

-- even in the Slot positions are sharp
lemma stampG (s u k l a b) (p : z≠x) : outG x (sectionG u a b) z (sectionG s k l)=
    if u=s then Photo.placed 0 x k l a b z else 0 := by
  unfold outG sectionG; rw [ge, matchU]; split_ifs
  · rw [unroll,ends,ends]; simp only [Module.End.one_apply]
    have h: eye (x-z) (curl a b k l)= ((YM.Maxwell.bareCurl a b k l (x-z):ℝ):ℂ) := lap _ (fun x q=>YM.Maxwell.Bare.curl_diff q a b k l) (sub_ne_zero.mpr p.symm)
    rw [h,show x-z= -(z-x) by abel,YM.Maxwell.Bare.even (sub_ne_zero.mpr p)]; unfold Photo.placed; rw [YM.Maxwell.Free.cure_0]
  rw [map_zero]
lemma stampF (d : Bool) (s u k a) (p : z≠x) : outF (!d) x (sessionF u a) z (sessionF s k)=if u=s then Tissue.jewel d x k 0 a z else 0 := by
  unfold outF sessionF; rw [yarn, matchU]; split_ifs
  · rw [psD,ends,ends]; simp only [Module.End.one_apply]
    rw [present,map_sum,Tissue.jewel, YM.Maxwell.Free.soften_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    have hm : coeffCR (!d) i k a=Tissue.M d i k a:=Tissue.even_M .. -- indices?
    have he:eye (x-z) (Gap.step i stone) = -↑(grad i YM.Maxwell.Green (z-x):ℝ) := by rw [flashStone i (sub_ne_zero.mpr p.symm), YM.Maxwell.first_Green (sub_ne_zero.mpr p.symm), YM.Maxwell.first_Green (sub_ne_zero.mpr p), show x-z= -(z-x) by abel]; simp; rw [norm_sub_rev x z]; ring
    rw [map_smul, hm,he,smul_eq_mul]; ring
  rw [map_zero]
lemma derivativeF (d k u z) (hz:z∈intact x) (X V): outF d x (stride d k (sessionF u V)) z X=grad k (fun z=>outF d x (sessionF u V) z X) z := (paidF d hz _ _ _).symm
end YM.GaugeFieldConstruction.Flux.One
