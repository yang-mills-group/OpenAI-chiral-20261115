import GaugeFieldConstruction.Three

/-!
# Assemblies, grade trajectories. Inductive Lie closure kept explicit.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6300
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Loft
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Row
open Floor Carat Dawn Sailing Angles
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate
attribute [local instance] iG iF iX iU iT2 iW2 iV iS towerA towerR floatA floatY
local notation "W"=>port Al
local instance (priority:=30000) topx:IsScalarTower ℝ Al Al:= towerA
local instance (priority:=30000) topg:SMulCommClass ℝ Al Al:= towerR
lemma port_at (i j:Al) (d x): (port Al).l i j d x=i d (j d x) - j d (i d x):=rfl

def tax : Signed→* Al where
  toFun s d:=spinFrame d s
  map_one':=funext fun d=> (spinFrame d).map_one
  map_mul' i j:=funext fun d=>(spinFrame d).map_mul i j
abbrev meter := acn tax
-- normalization B. Lie hull.

def pipe (s: Signed): Endr Apit.G where
  toFun := Stage.conjS s.ortho
  map_add' x y := Subtype.ext (by simp [Stage.conjS,mul_add,add_mul])
  map_smul' a x:=Subtype.ext (by simp [Stage.conjS])
def timbre: Helm Signed where
  A:={ toFun:=pipe
       map_one':=by apply LinearMap.ext; intro i; change conjS (Signed.ortho 1) i=i; rw [show Signed.ortho 1=1 from Signed.inclusionO.map_one]; apply Subtype.ext; simp [conjS]
       map_mul' x y:=by apply LinearMap.ext; intro i; change conjS (Signed.ortho (x*y)) i=conjS x.ortho (conjS y.ortho i); rw [show Signed.ortho (x*y)= x.ortho*y.ortho from Signed.inclusionO.map_mul x y]; apply Subtype.ext; simp [conjS,mul_assoc] }
  joins x a b:= by
    change pipe x (tick a b)=tick (pipe x a) (pipe x b)
    let k:=x.ortho; have h:= k.property.1
    change _=_;
    change conjS k (tick a b)=tick (conjS k a) (conjS k b)
    apply Subtype.ext; simp only [conjS,tick,mul_sub,sub_mul,mul_assoc]; rw [← mul_assoc (star k.val) k.val,← mul_assoc (star k.val) k.val,h,one_mul,one_mul]

lemma mapT (s a b): meter s ((port Al).l a b)= (port Al).l (meter s a) (meter s b):= by
  change meter s (a*b-b*a)= meter s a*meter s b- meter s b*meter s a; rw [map_sub,acn_mul,acn_mul]
lemma metered s (v:Al) d x: meter s v d x=spinFrame d s (v d (spinFrame d s⁻¹ x)):=rfl
lemma both (s g) (x:UV g): spinFrame g s (spinFrame g s⁻¹ x)=x:=by rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
lemma both' (s g) (x:UV g): spinFrame g s⁻¹ (spinFrame g s x)=x :=by simpa using both s⁻¹ _ x
lemma packet (u:C1 Al) : u∈ Apit.fixed (gr₁ timbre meter) ↔
      ∀ s i d x, u (pipe s i) d (spinFrame d s x)=spinFrame d s (u i d x):=by
  rw [fix₁]; constructor
  · intro p s i d x
    have h:=LinearMap.congr_fun (congr_fun (p s i) d) (spinFrame d s x)
    rw [metered,both'] at h; exact h.symm
  intro v s i; ext1 d; apply LinearMap.ext; intro x; rw [metered, ← v s i d (spinFrame d s⁻¹ x),both]; rfl

lemma real_pay (a:ℝ) (d) (x:UV d): a • x=(a:ℂ) • x:=RCLike.real_smul_eq_coe_smul (K:=ℂ) a x
lemma spin_lift d s x: Calibration.lift d (spinFrame d s x)=spinFrame five s (Calibration.lift d x) := by
  let q:= spinFrame d s x; let k:=lift d x
  apply Prod.ext; rfl
  apply Prod.ext; apply Subtype.ext
  · apply LabelAction.Carries.same (gauge d).toCarries (gauge five).toCarries s; rfl
  apply Prod.ext
  · ext1 i; apply Subtype.ext; apply LabelAction.Carries.same (matter d).toCarries (matter five).toCarries s; rfl
  ext1 i; apply Subtype.ext; apply LabelAction.Carries.same (mixed d).toCarries (mixed five).toCarries s; rfl
-- QT constraints (need only d4&5 for product, keep full). Explicit rather than equiv assumption on nearby maps. unit part not centered!
structure Canny (G:Al): Prop where
  unit d:G d (one d)=0
  soul d x:G d (shade d x)=shade d (G d x)
  up d x: G five (Calibration.lift d x)=Calibration.lift d (G d x)
  moon s d x:G d (flavors d s x)= flavors d s (G d x)
namespace Canny
lemma nil: Canny 0:=⟨fun _=> rfl, fun d _=> (shade d).map_zero.symm,fun d _=> (Calibration.lift d).map_zero.symm,fun s d _=>(flavors d s).map_zero.symm⟩
lemma add {a b:Al} (h:Canny a) (k:Canny b): Canny (a+b):=by
  constructor
  · intro i; simp only [Pi.add_apply,LinearMap.add_apply,h.unit,k.unit,add_zero]
  · intro i x; simp only [Pi.add_apply,LinearMap.add_apply,h.soul,k.soul,map_add]
  · intro i x; simp only [Pi.add_apply,LinearMap.add_apply,h.up,k.up,map_add]
  intro s i x; simp only [Pi.add_apply,LinearMap.add_apply,h.moon,k.moon,map_add]
lemma scale {a} (h:Canny a) (s:ℝ):Canny (s • a):=by
  rw [realT]
  constructor
  · intro d; change (s:ℂ) • a d (one d)=0; rw [h.unit,smul_zero]
  · intro d x; change (s:ℂ) • a d _ =shade d ((s:ℂ) • _); rw [h.soul,map_smulₛₗ]; rw [show Conj.bar (s:ℂ)=s from Complex.conj_ofReal s]
  · intro d x; change (s:ℂ) • a five _ = Calibration.lift d ((s:ℂ) • _); rw [h.up,map_smul]
  intro t d x; change (s:ℂ) • a d _ = flavors d t ((s:ℂ) • _); rw [h.moon,map_smul]
lemma large {a b} (h:Canny a) (k:Canny b):Canny (a*b):=by
  constructor
  · intro i; change a i (b i (one i))=0; rw [k.unit,map_zero]
  · intro i x; change a i (b i _)=_; rw [k.soul,h.soul]; rfl
  · intro i x; change a five (b five _)=_; rw [k.up,h.up]; rfl
  intro t i x; change a i (b i _)=_; rw [k.moon,h.moon]; rfl
lemma thermal {G} (s:Signed) (h:Canny G): Canny (meter s G):=by
  constructor
  · intro i; rw [metered,Empire.sends_1,h.unit,map_zero]
  · intro d x; rw [metered,metered,← Calibration.comp_s,h.soul,Calibration.comp_s]
  · intro d x; rw [metered,metered,← spin_lift,h.up,spin_lift] -- adjust
  intro f d x; rw [metered,metered, show spinFrame d s⁻¹ (flavors d f x)=flavors d f (spinFrame d s⁻¹ x) from LinearMap.congr_fun (Calibration.commute s⁻¹ d f) x, h.moon]; exact LinearMap.congr_fun (Calibration.commute s d f) _
end Canny

def allowed : Wardrobe timbre Al where
  paint:=meter
  muls:= acn_mul tax
  P:={ carrier:={x|Canny x}
       zero_mem':=Canny.nil
       add_mem':=Canny.add
       smul_mem' a _ p:=Canny.scale p a }
  proper g _ p:= Canny.thermal g p
  lands _ _:=Canny.large

-- Y supplementary Q2 hypothesis. (81) does not alone imply.
variable {S : City} {P:Axis→Across} {L:Sheds S P} (C : Supplies L) (E : Tot S P L)
def angleT : C1 Al := LinearMap.pi fun d=> (C.Y d E)
structure Typical (E:Tot S P L): Prop where
  canny x:Canny (angleT C E x)
  twists : angleT C E∈ Apit.fixed (gr₁ timbre meter)

lemma holy (D : District) (i): Canny (gest D i) where
  unit d:= Empire.alone (d:=d) i D
  soul d x:=Stage.realG D i x
  up d x:= RawBank.SY_up (RawBank.activates D.g) (fun k=>RawBank.activates (D.f k)) d i x
  moon s d x:=Stage.due D i s x
lemma whorl (D : District): gest D ∈ Apit.fixed (gr₁ timbre meter):= (packet _).2 (fun s i d x=> Stage.sooner ..)
end YM.GaugeFieldConstruction.Ember.Loft
