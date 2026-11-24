import YM.SU5.WakeInvestment.Viewport
import YM.SU5.WakeInvestment.Dip
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Wake
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis Regis.Head clocks
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)(D:LocalRatio J)
open Regis.Wake (Paint drip mute_mix muting mute_shrink mute_ceiling mute_same mute_smooth lipClay assay)
open Regis.Head.Etch ProbabilityTheory
variable {S0:Support n}{s:ℕ}
abbrev keelSlot (a:PlaqAxes) : RG.Slot:= ⟨[],a⟩
lemma keelFace (a:PlaqAxes)(x:Site n): slotFace (keelSlot a) x=(x,a):=by simp [slotFace,keelSlot,Slot.offset,stop]
lemma keelEval (a:PlaqAxes)(y:Site n)(U:Config G n) : (keelSlot a).atSite U y=G.curvature (faceValue U (y,a)):=by rw [atSite_path,keelFace]; simp [keelSlot,travel]
abbrev Eye (G:Gauge)(n:Side) := Cell n × G.ColorIndex
structure Vessel (G:Gauge)(n:Side)(I : Type*) where
 view:I→Eye G n
variable {I : Type*} [Fintype I] (W:Vessel G n I)
namespace Vessel
abbrev ua(i:I):= (W.view i).1
abbrev lens(i:I) := (W.view i).2
abbrev keel(i:I):= keelSlot (W.ua i).2
abbrev origin(i:I):= (W.ua i).1
abbrev crew(i:I)(t:Signed) := skewSlot G (W.keel i) t
abbrev cBase(i:I)(t:Signed)(b:Site n):= affine t b (W.origin i)
abbrev viewFace(i:I)(t:Signed)(b:Site n):=slotFace (W.crew i t) (W.cBase i t b)
structure Ship(S:Support n)(d:ℕ) : Prop where
 lives(i:I): touched (W.ua i)⊆ S
 keeps(i:I)(t:Signed)(b:Site n):(W.viewFace i t b).1∈ S.image (affine t b)
 pay(i:I)(t:Signed): (W.crew i t).length≤ d
omit [Fintype I] in
lemma Ship.raise(U:Support n)(h:S0⊆ U)(p:W.Ship S0 m)(qv:m ≤ s) : W.Ship U s:= ⟨fun i=>(p.lives i).trans h,fun i t b=>image_subset_image h (p.keeps i t b),fun i t=>(p.pay i t).trans qv⟩
variable (ρ:ℝ)(t:Signed)(b:Site n)
-- vessel coords after here H basis. matched at stamen. scale λ used at root/world with field-curl convention; wake argument expects `ω=λ*coupling β`
def material(U:Config G n)(i:I):ℝ:= ρ*(G.curvature (faceValue U (W.ua i)) (W.lens i))
abbrev siphon (q:Clip) (i:I) : StrongDual ℝ (Altar G n):= (ρ*(skewSig G (W.keel i) t)) • ((EuclideanSpace.proj (W.lens i)).comp ((river q (W.viewFace i t b)).toContinuousLinearMap))
-- explicit call Order V=stamen or Altar protagonist.
local notation "■" => starFeed
lemma siphon_now (q:Clip)(i:I)(x:Altar G n): W.siphon ρ t b q i x=((ρ • (skewSig G (W.keel i) t) • river q (W.viewFace i t b) x) (W.lens i)) :=by rw [←mul_smul]; rfl
lemma on_orient(i:I)(V:fieldDir G n 1): W.siphon ρ t b q i (tiler B P V)= ρ*(faceCurl (W.ua i) (bank t b V) (W.lens i)):=by
 rw [siphon_now,river_now q B P]; rw [show W.ua i=slotFace (W.keel i) (W.origin i) from (keelFace ..).symm]; rw [reflex]; rfl
lemma vane {Y:Support n}(hx:W.Ship S0 m)(i:I) (p:∀ z∈ S0.image (affine t b),withinCore r A Y (hallBill m) z) : withinMark r A Y m (W.viewFace i t b) :=
  (p _ (hx.keeps i t b)).shift (by simp [Sequest,hallBill])
lemma port_cost(hx:W.Ship S0 m)(R:Rules G){D L:fieldDir G n 1}{Y0:Support n}(hp:∀ z∈ S0.image (affine t b),withinCore r A Y0 (hallBill m) z)(u:TrustLogs (D+L) U r A v)(hs:0≤v)(he:v ≤ R.c)(g:0<β)(i:I) :
    |W.material ρ (pull t b U) i-W.siphon (ρ*coupling β) t b q i (starFeed B P r A Y0 m L β D)| ≤ |ρ| * slotError R m v:=by
 let F:=W.keel i; let D':=W.crew i t; let x:=W.origin i; let y:=W.cBase i t b; let z:=skewSig G F t
 have hx' := reflects F t x b U;
 have ht: G.curvature (faceValue (pull t b U) (W.ua i)) = z • (D'.atSite U y):=(keelEval (W.ua i).2 ..).symm.trans hx'
 let V:=starFeed B P r A Y0 m L β D; let X:= D'.atSite U y; let Y:= faceCurl (W.viewFace i t b) (D+L); let C:= X-Y
 have hh: W.siphon (ρ*coupling β) t b q i V=((ρ • z • Y) (W.lens i)):=by
      rw [siphon_now]; unfold V starFeed; rw [map_smul,river_still B P _ (W.vane t b hx i hp)]; rw [mul_smul, smul_comm (coupling β), smul_inv_smul₀ (coupling_pos g).ne'] -- arg order
 have hv := hp y (mem_image_of_mem (affine t b) ((hx.lives i) (Work.E01.base_touched _))); have h: ‖C‖≤ slotError R m v:= grantSlot u hs he D' (hv.1.shift (y:=y) (by simp [hallBill,Sequest])) (hx.pay i t)
 have hw:0 ≤ |ρ|:=abs_nonneg _
 rw [hh]; unfold material; rw [ht]; change |(ρ*(z* X (W.lens i)))-(ρ * (z * Y (W.lens i)))|≤_
 rw [←mul_sub,←mul_sub,abs_mul, abs_mul, skewSq, one_mul]; exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (p:=2) C (W.lens i)).trans h) hw
abbrev cap(q:Clip)(x:ℝ):ℝ:= |x| *(Real.sqrt q.direct)⁻¹
lemma siphon_price(q:Clip)(i:I)(x:Altar G n) : ‖W.siphon ρ t b q i x‖ ≤ cap q ρ*‖x‖ :=by
 rw [siphon_now]; let T:= W.crew i t; let z:= skewSig G (W.keel i) t; let w:= W.cBase i t b; let f:= slotFace T w
 change ‖(ρ • z • river q f x) (W.lens i)‖ ≤_; apply le_trans (PiLp.norm_apply_le (p:=2) (ρ • z • river q f x) _); rw [norm_smul,norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, skewSq,one_mul]
 have hv:‖cup f x‖≤ ‖x‖:=by
    simpa [f] using (cup_sum (fun i:Unit=>w) (Function.injective_of_subsingleton _) T x)
 unfold river cap; rw [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),mul_assoc |ρ|]; gcongr
lemma siphons_clamp (q:Clip)(i:I)(V:Submodule ℝ (Altar G n)) : ‖(W.siphon ρ t b q i).comp V.subtypeL‖ ≤ cap q ρ:= by
 apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) (by positivity)); exact fun i'=> W.siphon_price _ _ _ _ _ _
lemma sight (q:Clip)(i:I)(hx:W.Ship S0 s)(x:Altar G n) :
 W.siphon ρ t b q i (vase G n (S0.image (affine t b)) x)= W.siphon ρ t b q i x :=by
 unfold siphon; simp [river,cup,vase]; intro h; exact False.elim (h _ (mem_image.mp (hx.keeps i t b)).choose_spec.1 (mem_image.mp (hx.keeps i t b)).choose_spec.2)
include L_
lemma echo_read (H':Bid.Sworn H n G) (Φ Ψ:Altar G n→ℂ)(g:Continuous Φ)(h:∀ V:fieldDir G n 1, Φ (tiler B P (bank t b V))=Ψ (tiler B P V)): (∫ x:stamen B P n, Φ x.val∂stdGaussian (stamen B P n)) = (∫ x:stamen B P n, Ψ x.val∂stdGaussian (stamen B P n)):=by -- `L_` include
 let T:=stamen B P n; obtain ⟨W,hx⟩:= banked t b B P L_ H'; have he(a:T): Φ (W a).val= Ψ a.val:=by obtain ⟨V,rfl⟩:= (tiler B P).surjective_rangeRestrict a; rw [hx]; exact h _
 conv_rhs => arg 2; intro i; rw [←he]
 have hw:= integral_map (μ:=stdGaussian T) W.continuous.aemeasurable (f:=fun p:T=> Φ p.val) (g.comp continuous_subtype_val|>.aestronglyMeasurable); rw [stdGaussian_map W] at hw; exact hw
-- invariant sanity, turn does not use point localization costs for polynomial realm
omit L_
abbrev basin (ρ:ℝ)(F:(I→ℝ)→ℂ)(q:Clip)(x:Altar G n):= F (drip (W.siphon ρ 1 0 q) x)
lemma belly (G':(I→ℝ)→ℂ)(V:fieldDir G n 1) : W.basin ρ G' q (tiler B P V)=G' fun i=> ρ*faceCurl (W.ua i) V (W.lens i):=by
 let M:=bank (G:=G) 1 (0:Site n);
 apply congrArg G'; funext i; rw [drip, W.on_orient B P]; let J:=W.keel i; let t:= W.origin i
 have ht:= slot_deriv J t (M V); unfold M at ht; simp_rw [bank_at, pull_id] at ht; have hs:faceCurl (W.ua i) (M V)=faceCurl (W.ua i) V:=by rw [show W.ua i= slotFace J t from (keelFace ..).symm]; exact ht.unique (slot_deriv J t V)
 rw [hs]
section
include L_
lemma turn_basin (H':Bid.Sworn H n G) (G':(I→ℝ)→ℂ) (g:Continuous G') : ∫ x:stamen B P n, W.basin ρ G' q x.val∂stdGaussian (stamen B P n)=∫ x:stamen B P n, G' (drip (W.siphon ρ t b q) x.val)∂stdGaussian (stamen B P n):=by
 apply echo_read B P L_ t b H' (W.basin ρ G' q) (fun x=> G' (drip (W.siphon ρ t b q) x)) (g.comp (continuous_pi (fun i:I=> (W.siphon ρ 1 0 q i).continuous))) (fun x=>?_); rw [W.belly B P]; unfold drip; simp_rw [W.on_orient B P]
end
end Vessel
end YM.Gleam.Wake
