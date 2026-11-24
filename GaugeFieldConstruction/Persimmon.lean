import GaugeFieldConstruction.Delve
/-!
# 81 triple status. Consequences for (98/99), normalization included.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6500
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Empire Fathom Payroll Function Filter Set TopologicalSpace YM.Analysis MeasureTheory Points Bulb Palace Module RawBank Stage
open Floor Wick Invoice Gap Sailing
open scoped Topology BigOperators ContDiff
open Phys Flux.One
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {X : Type*} {ℱ : Filter X} {S : City} {q:X→Carat}
local notation "l4" => Calibration.lift Floor.four
local notation "l5" => Calibration.lift Floor.five
abbrev lens (Q:Carat) (d:Floor): UV d ≃ₗ[ℂ] UV d:= (Q.G d).c

lemma wages (p : Points 3) (x y : UV five): ∃ L : UV four →ₗ[ℂ]ℂ, ∀ i,coupe i x y p=L i:= ⟨(((YM.GaugeFieldConstruction.Flux.One.prism (p 0) (p 1) (p 2)).flip (dress (shells _ x))).flip (dress (shells _ y))) ∘ₗ dress ∘ₗ shells _,fun _=>rfl⟩
def audition (x y : UV five) (f:Test 3): UV four→ₗ[ℂ]ℂ where
  toFun z:= f.applyTo (coupe z x y)
  map_add' z v:=by
    unfold Test.applyTo; rw [← integral_add (Test.smearing f (smoothT z x y)) (Test.smearing f (smoothT v x y))]; apply integral_congr_ae; apply Eventually.of_forall; intro p
    obtain ⟨H,h⟩:=wages p x y; simp only; simp only [h,map_add,mul_add]
  map_smul' a v:=by
    change f.applyTo _=a* f.applyTo (coupe v x y); unfold Test.applyTo; rw [← integral_const_mul]; apply integral_congr_ae; apply Eventually.of_forall; intro p
    obtain ⟨H,h⟩:=wages p x y; simp only; simp only [h,map_smul]; exact mul_left_comm ..

structure Blush (S : City) (ℱ : Filter X) (q : X→Carat) extends Views S ℱ q : Prop where
  -- first z, then x, then y. Ordinary comparison. No derivatives assumed.
  trio x y z (p : Test 3) (v:tsupport p ⊆ axisRange 3) : Tendsto (fun k=> S.tagged (tie (lens (q k) five x) (lens (q k) five y)) (l4 (lens (q k) four z)) ((q k).u.roll p)) ℱ (𝓝 (p.applyTo (coupe z x y)))

variable (H : Blush S ℱ q) {P:Axis→Across} {L : Sheds S P} (C:Supplies L)
local notation "Ls"=> Tot S P L
include H in
lemma tripleFlux (f : Foil) (K:Payroll 2) (x y) (t:X→SymT) (R) (p:Dips ℂ ℱ t R) : Tendsto (fun k=> delta K f.p f.a f.u.cared (fun i j=> (S.armed (prints ((q k).t (t k))) (tie (lens (q k) five y) (lens (q k) five x)) i j) ∘ₗ (q k).u.roll)) ℱ (𝓝 (freight f K R x y)) := by
  unfold delta freight; refine tendsto_finsetSum _ (fun i _=>tendsto_finsetSum _ fun j _=>?_)
  let u:= testcut K f.p f.a f.u.cared i j; let e:= Fathom.perm flip_last u; let v:=audition x y e
  let T k : UV four →ₗ[ℂ] ℂ:= LinearMap.applyₗ (q k |>.u.roll e) ∘ₗ S.tagged (tie (lens (q k) five x) (lens (q k) five y)) ∘ₗ l4 ∘ₗ (lens (q k) four).toLinearMap
  have h z:Dips ℂ ℱ (fun k=> T k z) (v z):= seen.mpr (H.trio x y z e (into_patch ..)) -- type
  let B:= LinearMap.proj (ordered i j) ∘ₗ SymT.subtype
  have hx:=seen.mp (trav h (fun k=>B (t k)) (B R) (maps p B)); rw [show v (B R)= u.applyTo (capo (pens R i j) x y) from shiftTag ..] at hx
  refine hx.congr (fun k=>?_)
  let Q:=q k; change _ = S.tagged (tie _ _) (prints _ i j) (Q.u.roll u); rw [counter S,roll_perm]; unfold prints pens; rw [Carat.t_pay]; rfl

-- Free contours
variable [ℱ.NeBot]
include H
lemma around_pivot (k : Payroll 2) (f : Foil) (i : Floor) (x : UV i) (y) (a : Bundle) (o : Floor) (v : UV o)
    (p : ∀ q :Points 2,q∈tsupport f.p → Earn a.1 a.2 f.a.f (fun j z=> k.K j (cons z q)) (q front) (q 0) (dress (shells _ x)) (dress (shells _ v))) :
    freight f k (totalIx a).val (Calibration.lift i x) y=silky y (Calibration.lift o v) f.p:= by
  rw [delivered,mirror_is H.toViews y]
  apply integral_congr_ae; apply Eventually.of_forall; intro z
  by_cases h:z∈tsupport f.p
  · have T:=p z h (dress (shells _ y))
    refine congr_arg (fun u:ℂ=> f.p z*u) T
  have U : f.p z=0:=image_eq_zero_of_notMem_tsupport h
  change f.p z*_= f.p z*_; simp [U]
omit H [ℱ.NeBot] in
lemma chassis (f:Foil) (x) (p:x∈tsupport f.p) : Chassis (x front) (x 0) f.a.f := ⟨⟨f.a.d,f.a.c⟩,f.u.bulb _ p,f.u.direct _ p 0 (by decide)⟩
lemma penned (a : Bundle) (f : Foil) (b:UV five) x (i) : freight f (ticket i) (totalIx a).val (l4 x) b= silky b (packΘ a.1 a.2 (basis i) x) f.p := by
  exact around_pivot H (ticket i) f four x b a five (packΘ a.1 a.2 (basis i) x) (fun z p=> amble a.1 a.2 x (chassis f z p) (basis i))
lemma earnedₛ (a : Bundle) (f : Foil) (b:UV five) (o:Floor) (x : UV o) Ω: freight f (desk front Ω) (totalIx a).val (Calibration.lift o x) b=silky b (Calibration.lift _ (SY a.1 a.2 o Ω x)) f.p := by
  apply around_pivot H (desk front Ω) f o x b a o _; intro z p; have h (i w) :(desk front Ω).K i (cons w z)=soar Ω (z front) i w:= by rw [angle]; rfl -- cons
  rw [funext fun i=>funext (@h i)]; exact stroke _ _ _ _ (chassis f z p) Ω
omit H [ℱ.NeBot] in
lemma delta_scale {n : ℕ} (x : Variation n) (c : ℂ) (K:Payroll n) (p : Test n) (J : Bulb) (f:∀ i, Quiet p (J.LED i)): delta K p J f (c • x)=c • delta K p J f x := by simp only [delta,Pi.smul_apply,LinearMap.smul_apply,Finset.smul_sum]
-- multipliers. roll conservation frames back

def hip (Q:Carat) (t : Ls) (a:Axis) : Across := levelP (C.theta (Q.κ⁻¹^4 • t)) Q a -- using same scalar tower

def horn (Q:Carat) (d : Floor) (t : Ls) (Ω:Rotors) : Module.End ℂ (UV d) := (lens Q d).symm.toLinearMap ∘ₗ (C.Y d (Q.κ⁻¹^4 • t) Ω ∘ₗ (lens Q d).toLinearMap)
omit H [ℱ.NeBot] in
lemma scaled_armed (t:Ls) (q:ℂ) {n:ℕ} (x : Fin n→UV five) (i j): S.armed (prints (q • t).val) x i j=q • S.armed (prints t.val) x i j:= by
  unfold armed prints pens; change S.tagged x (l4 (q • t.val.val _))= _; rw [map_smul,map_smul]
-- single witness price on phi
omit H [ℱ.NeBot] in
lemma hop_fee (f : Foil) (b:UV five) (x:UV four) (Q : Carat) (t : Ls) (i):
    alpha S Q (hip C Q t i x) (f,b)= delta (ticket i) f.p f.a f.u.cared (fun j l=> (S.armed (prints t.val) (tie (lens Q five b) (lens Q five (l4 x))) j l) ∘ₗ Q.u.roll):=by
  let g := (lens Q four) x; let u:= other (lens Q five b); let k:=Q.κ; let V:=S.armed (prints t.val) (update u front (l4 g)); let w:=fun i j=> V i j ∘ₗ Q.u.roll
  have he : tie (lens Q five b) (lens Q five (l4 x))=update u front (l4 g):= congr_arg _ (Q.include_ four x) -- mismatch
  rw [he]
  change lunar _ _ _ _ _=delta _ _ _ _ w
  rw [lucid]; unfold hip; rw [vert,map_smul,LinearMap.smul_apply]
  change k • S.spot u front _ (Q.u.roll _) = _
  rw [C.law _ _ _ _ _ _ _ _ (Q.u.Works' f.u),postage,Q.u.do_move i f.p f.a front f.u]; simp_rw [scaled_armed]; change k • (k^3 • delta (ticket i) _ _ _ (k⁻¹^4 • w))=_; rw [delta_scale,smul_smul,smul_smul,show (k*k^3*k⁻¹^4)=1 by field_simp [show k≠0 from Q.nζ],one_smul] -- nesting

omit H [ℱ.NeBot] in
lemma horn_fee (f : Foil) (b: UV five) (d : Floor) (x:UV d) (Q:Carat) (t:Ls) (Ω):
    alpha S Q (Calibration.lift d (horn C Q d t Ω x)) (f,b)= delta (desk front Ω) f.p f.a f.u.cared (fun j l=> (S.armed (prints t.val) (tie (lens Q five b) (lens Q five (Calibration.lift d x))) j l) ∘ₗ Q.u.roll):= by
  let g:=(lens Q d) x; let u:= other (lens Q five b); let k:=Q.κ; let V:=S.armed (prints t.val) (update u front (Calibration.lift d g)); let w:=fun i j=> V i j ∘ₗ Q.u.roll
  rw [show tie (lens Q five b) (lens Q five (Calibration.lift d x))=update u front (Calibration.lift d g) from congr_arg _ (Q.include_ d x)]
  change lunar _ _ _ _ _=delta _ _ _ _ w; rw [lucid,Q.include_]; unfold horn; change S.spot u front (Calibration.lift _ (lens Q d ((lens Q d).symm _))) _=_
  rw [LinearEquiv.apply_symm_apply]; change S.spot u front (Calibration.lift d (C.Y d (Q.κ⁻¹^4 • t) Ω g)) (Q.u.roll f.p)=_; rw [C.decree _ _ _ _ _ _ _ _ _ (Q.u.Works' f.u),rpm,Q.u.do_turn Ω f.p f.a front f.u]; simp_rw [scaled_armed]; change k^4 • delta (desk front Ω) _ _ _ (k⁻¹^4 • w)=_; rw [delta_scale, smul_smul,← mul_pow,mul_inv_cancel₀ (show k≠0 from Q.nζ),one_pow,one_smul]

variable (t:X→Tot S P L) (a:Bundle) (p:Dips ℂ ℱ (fun k=> (q k).t.symm (t k).val) (totalIx a).val)
include p
private lemma stablePay (x y : UV five) (K:Payroll 2) (f:Foil): Tendsto (fun k=> delta K f.p f.a f.u.cared (fun i j=>S.armed (prints (t k).val) (tie (lens (q k) five y) (lens (q k) five x)) i j ∘ₗ (q k).u.roll)) ℱ (𝓝 (freight f K (totalIx a).val x y)) := by
  have h := tripleFlux H f K x y _ _ p; simp_rw [LinearEquiv.apply_symm_apply] at h; exact h
lemma pledge (i : Axis) (x: UV four): Dips ℂ ℱ (fun k=>hip C (q k) (t k) i x) (packΘ a.1 a.2 (basis i) x) := by
  apply (insight etaF₀ (send H.toViews)).2; rintro ⟨v,b⟩; simp_rw [hop_fee C]; change Tendsto _ _ (𝓝 (silky b _ v.p)); rw [← penned H a v b x i]; exact stablePay H t a p (l4 x) b (ticket i) v
lemma rimmed (d Ω) (x : UV d): Dips ℂ ℱ (fun k=>horn C (q k) d (t k) Ω x) (SY a.1 a.2 d Ω x) := by
  let X:= fun k=> horn C (q k) d (t k) Ω x; let v:= SY a.1 a.2 d Ω x
  apply truth (etaF ∘ₗ Calibration.lift d) (etaF₀.comp (inject d))
  have h : Dips ℂ ℱ (fun k=> Calibration.lift d (X k)) (Calibration.lift d v):= by
    refine (insight etaF₀ (send H.toViews)).2 _ _ ?_; rintro ⟨j,b⟩
    change Tendsto (fun k=>alpha S (q k) _ _) _ (𝓝 (silky b (Calibration.lift d v) j.p)) -- annotate
    unfold X; simp_rw [horn_fee]; unfold v; rw [← earnedₛ H a j b d x Ω]; exact stablePay H t a p (Calibration.lift d x) b (desk front Ω) j
  exact fun i=> h (feel etaF i)
#print axioms pledge
#print axioms rimmed
end YM.GaugeFieldConstruction.Ember
