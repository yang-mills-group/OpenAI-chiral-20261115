import GaugeFieldConstruction.Durian
/-!
# Fubini for comparison contours
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Calibration Raw Cauchy Gap Wick Phys Function MeasureTheory Filter TopologicalSpace Set YM.Analysis Lamp
open scoped Topology BigOperators ContDiff
variable {U X Y B K : Type*} [TopologicalSpace U] {x y z:U→E4} {u:U}
lemma contFins (p: U→J X→ₗ[ℂ] ℂ) (v:J X) (h:∀ i, ContinuousAt (fun z=>p z (ket i)) u): ContinuousAt (fun z=>p z v) u:= by
  induction v using Finsupp.induction_linear with
  | zero=> simp only [map_zero]; exact continuousAt_const
  | add a b q w=> simp only [map_add]; exact q.add w
  | single i r=> rw [show Finsupp.single i r=r • ket i from by simp [ket]]; simp only [map_smul,smul_eq_mul]; exact continuousAt_const.mul (h i)

variable (U1 : ContinuousAt x u) (U2 : ContinuousAt y u) (U3 : ContinuousAt z u)
    (xy : x u≠ y u) (xz : x u≠z u) (yz : y u≠z u)
include U1 U2 U3 xz yz
lemma contOrient (p: Wick.Bil X Y) (q:Wick.Bil B K) (a b c) : ContinuousAt (fun v=>orient p q (z v) (x v) (y v) a b c) u:=by
  apply contFins (fun v=> ((orient p q (z v) (x v) (y v)).flip b).flip c); intro i
  change ContinuousAt (fun v=>orient p q _ _ _ (ket i) b c) _; rw [← takes i.1 i.2]; simp_rw [pair_up]
  exact ((healthy _ (sub_ne_zero.mpr xz)).continuousAt.comp (x:=u) (U1.sub U3)).mul ((healthy _ (sub_ne_zero.mpr yz)).continuousAt.comp (x:=u) (U2.sub U3))
lemma contFG (v a b): ContinuousAt (fun t=> FG (z t) (x t) (y t) v a b) u := by
  simp only [FG,LinearMap.comp_apply,LinearMap.add_apply]
  exact (contOrient U1 U2 U3 xz yz ..).add (contOrient U1 U2 U3 xz yz ..)
lemma contFF (d v a b): ContinuousAt (fun t=> FF d (z t) (x t) (y t) v a b) u:= by
  cases d
  · exact contOrient U1 U2 U3 xz yz _ _ _ _ _
  exact (contOrient U1 U2 U3 xz yz _ _ _ _ _).neg
omit U1 U2 U3 xz yz in
lemma cont_lugs {g : U→Coupon X Y} {h : U→ Coupon B K} (p : ∀ a b, ContinuousAt (fun t=> g t a b) u) (q : ∀ a b,ContinuousAt (fun t=>h t a b) u) (a b): ContinuousAt (fun t=> lugs (g t) (h t) a b) u:=by
  apply contFins (fun v=> (lugs (g v) (h v)).flip b); intro i
  apply contFins (fun v=>lugs (g v) (h v) (ket i)); intro j
  rw [← takes i.1 i.2,← takes j.1 j.2]; simp_rw [sunny]
  exact (p _ _).mul (q _ _)
omit U3 xz yz in
lemma solo_cont (p : Wick.Bil X Y) (xy : x u≠y u) (a b): ContinuousAt (fun t=>solos p (x t) (y t) a b) u := (healthy _ (sub_ne_zero.mpr xy.symm)).continuousAt.comp (x:=u) (U2.sub U1)
include xy
lemma go_cont (w a b):ContinuousAt (fun t=>Lamp.go (z t) (x t) (y t) w a b) u:= by
  let k:=b+Phys.swap _ b
  change ContinuousAt (fun t=> lugs (FG (z t) (x t) (y t) w) (solos ge (x t) (y t)) a k+ lugs (solos ge (x t) (y t)) (FG (z t) (x t) (y t) w) a k) u
  have e:= contFG U1 U2 U3 xz yz w; exact (cont_lugs e (solo_cont U1 U2 _ xy) ..).add (cont_lugs (solo_cont U1 U2 _ xy) e ..)
lemma fo_cont (w a b):ContinuousAt (fun t=>Lamp.fo (z t) (x t) (y t) w a b) u:= by
  let k:= Phys.swap _ b
  change ContinuousAt (fun t=> lugs (FF false (z t) (x t) (y t) w) (solos _ (x t) (y t)) a k+ lugs (solos _ (x t) (y t)) (FF true (z t) (x t) (y t) w) a k) u
  exact (cont_lugs (contFF U1 U2 U3 xz yz false w) (solo_cont U1 U2 _ xy) ..).add (cont_lugs (solo_cont U1 U2 _ xy) (contFF U1 U2 U3 xz yz true w) ..)
lemma contTri (a b c): ContinuousAt (fun t=> tri (z t) (x t) (y t) a b c) u:= by
  have ht w:ContinuousAt (fun t=>eye (x t-z t) w) u:=(healthy w (sub_ne_zero.mpr xz)).continuousAt.comp (x:=u) (U1.sub U3)
  have hs w:ContinuousAt (fun t=>eye (y t-z t) w) u:=(healthy w (sub_ne_zero.mpr yz)).continuousAt.comp (x:=u) (U2.sub U3)
  unfold tri; simp only [LinearMap.add_apply]
  apply ContinuousAt.add
  · apply ContinuousAt.add
    · apply ContinuousAt.add
      · exact ((((continuousAt_const.mul ((healthy _ (sub_ne_zero.mpr xy.symm)).continuousAt.comp (x:=u) (U2.sub U1))).add (continuousAt_const.mul ((ht _).add (ht _)))).add (continuousAt_const.mul ((hs _).add (hs _))))) -- counts plus
      exact go_cont U1 U2 U3 xy xz yz ..
    exact fo_cont U1 U2 U3 xy xz yz ..
  exact (cont_lugs (fo_cont U1 U2 U3 xy xz yz a.2.2.1) (solo_cont U1 U2 ge xy) ..).add (cont_lugs (solo_cont U1 U2 fGap xy) (contFG U1 U2 U3 xz yz a.2.1) ..)
end YM.GaugeFieldConstruction.Flux.One
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Empire Fathom Payroll Function Filter Set TopologicalSpace YM.Analysis MeasureTheory Points Bulb Palace Module Flux -- issue
open Floor Wick Invoice Gap Sailing
open scoped Topology BigOperators ContDiff
open Phys Flux.One

attribute [local instance] iG iF iX iU iT2 iW2 iV iS

-- kernel evaluated at (z,x,y), not (z,y,x)

def coupe (p:UV four) (a b:UV five) (x:Points 3): ℂ:=Flux.One.Tri (x 0) (x 1) (x 2) p a b
def capo (p:UV four) (a b:UV five) (x:Points 3): ℂ:=coupe p a b (arrangeL flip_last x)
lemma capo_earn (p a b) (q : Points 3) : capo p a b q=Flux.One.Tri (q 0) (riders q front) (riders q 0) p a b := by unfold capo coupe; simp_rw [arranged, rearrange_at]; congr 1 <;> rfl
lemma smoothT (p a b): ContinuousOn (coupe p a b) (conf 3):= fun x u=> (contTri (x:=fun x : Points 3=> x 1) (y:=fun x:Points 3=> x 2) (z:=fun x:Points 3=> x 0) (loc _).continuous.continuousAt (loc _).continuous.continuousAt (loc _).continuous.continuousAt ((show Injective (⇑x) from u).ne (by decide)) (u.ne (by decide)) (u.ne (by decide)) _ _ _).continuousWithinAt -- u.ne defeq?
lemma stillT (p a b): ContinuousOn (capo p a b) (conf 3):= ContinuousOn.comp (smoothT p a b) (arrangeL flip_last).continuous.continuousOn (fun _ h=> rearrange_in flip_last h)
lemma shiftTag (p a b f): Test.applyTo (Fathom.perm flip_last f) (coupe p a b)= f.applyTo (capo p a b):= (cost_mirror flip_last f (coupe p a b)) -- using sym? sym rfl

-- now pull operations with integral and bump x at slot k

def freight (f : Foil) (K : Payroll 2) (p : SymT) (a b: UV five): ℂ := ∑ i: Axis, ∑ j:Axis, (testcut K f.p f.a f.u.cared i j).applyTo (capo (pens p i j) a b)
private def interpret (α : Type*) {n :ℕ} (K: Points (n+1)→α) : E4× Points n→α:= K ∘ fuse.symm
lemma measured {n:ℕ} : MeasurePreserving (fuse (n:=n)) volume volume:= (WithLp.volume_preserving_ofLp _ _).comp Points.peel.measurePreserving

lemma tally (p v x y z q): tri z x y (dress (shells _ p)) (dress (shells _ v)) (dress (shells _ q))=Flux.One.Tri z x y p v q :=rfl

lemma delivered (K : Payroll 2) (f : Foil) (p : SymT) (a b : UV five) : freight f K p a b=
    ∫ x:Points 2, f.p x* Flux.Shell f.a.f (fun j z=> K.K j (cons z x))
      (fun i j z=> Flux.One.Tri z (x front) (x 0) (pens p i j) a b) := by
  let U i j:=testcut K f.p f.a f.u.cared i j; let V i j:=capo (pens p i j) a b
  let w i j (x:Points 3):= U i j x * V i j x
  let u i (x:E4×Points 2):= ∑ j:Axis,w i j (fuse.symm x)
  let tag i (x : Points 2) z := ∑ j :Axis, (D (basis i) f.a.f z * K.K j (cons z x)) • Flux.One.Tri z (x front) (x 0) (pens p i j) a b
  have ht (z) (x:Points 2):riders (cons z x)=x := by
    have H:=ContinuousLinearEquiv.apply_symm_apply fuse ((z,x):E4×Points 2); exact congr_arg Prod.snd H
  have h (i) (x) (z):u i (z,x)= f.p x * tag i x z := by
    unfold tag; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    unfold w U V; rw [capo_earn,testcut_v]; change _ = _; rw [fuse_m,ht,Complex.real_smul,Complex.real_smul]; change ((_:ℂ) * _)*_= _; rw [mul_assoc,mul_left_comm]; congr 1
  have hp i j :Integrable (w i j) := Test.smearing _ (stillT (pens p i j) a b)
  have hu i: Integrable (u i) volume := integrable_finsetSum _ (fun j _=> (show MeasurePreserving (fuse (n:=2)).symm volume volume from measured.symm (e:=fuse.toHomeomorph.toMeasurableEquiv)).integrable_comp_of_integrable (hp i j)) -- check
  have he i: ∑ j:Axis, ∫ x:Points 3,w i j x = ∫ x:Points 2, ∫ z:E4,u i (z,x) := by
    rw [← integral_finsetSum _ (fun j _=> hp i j)]; exact ((show MeasurePreserving fuse.symm volume volume from measured.symm (e:=fuse.toHomeomorph.toMeasurableEquiv)).integral_comp (fuse.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding) (fun x=>∑ j:Axis,w i j x)).symm.trans (integral_prod_symm (u i) (hu i)) -- check
  change (∑ i:Axis,∑ j:Axis, ∫ x:Points 3,w i j x)= _
  simp_rw [he]; rw [← integral_finsetSum _ (fun i _=> (hu i).integral_prod_right)] -- inner E4
  apply integral_congr_ae; refine Eventually.of_forall (fun x=>?_)
  simp_rw [h,integral_const_mul,← Finset.mul_sum]; congr 1; exact (Flux.pay_shell ..).symm
end YM.GaugeFieldConstruction.Ember
