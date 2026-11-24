import GaugeFieldConstruction.Born
import GaugeFieldConstruction.Terra
import GaugeFieldConstruction.Xenial
/-!
# active comparison invariant metric for the carrier `∀ i : Floor, End ℂ`
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6400
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Loft
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module
open Floor Carat Dawn Sailing Angles
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local instance : DecidableEq Floor:= Classical.decEq _
instance : Fintype Floor:= ⟨[three,four,five].toFinset,fun i=>by cases i <;> simp⟩ -- DecidableEq missing
abbrev Piece (d:Floor):= Module.End ℂ (UV d)
abbrev Al := ∀ i:Floor, Piece i

-- Check Instances
private instance aral: Module.Finite ℂ Al:= by infer_instance
-- later
local instance floatA : Module.Finite ℝ Al:= Module.Finite.trans ℂ Al -- check
local instance floatY (d:Floor) : Module.Finite ℝ (UV d):= Module.Finite.trans ℂ _

-- geometric cost

def pulse (D:District): Stage.SO→* Al where
  toFun x d:= ledger D d x
  map_one':= funext fun d=> (ledger D d).map_one
  map_mul' i j:= funext fun d=> (ledger D d).map_mul i j

lemma realT (a:ℝ) (v:Al) : a • v=(a:ℂ) • v:= funext fun d=>LinearMap.ext fun t=> RCLike.real_smul_eq_coe_smul (K:=ℂ) a (v d t)
local instance towerA:IsScalarTower ℝ Al Al:= ⟨fun a x y=> by change (a • x)*y=a • (x*y); rw [realT,realT]; ext1 i; apply LinearMap.ext; intro x; rfl⟩
local instance towerR:SMulCommClass ℝ Al Al:=⟨fun a x y=> by change a • (x*y)=x*(a • y); rw [realT, realT]; ext1 i; apply LinearMap.ext; intro v; exact Eq.symm (map_smul (x i) (a:ℂ) _)⟩

def gest (D:District) : C1 Al where
  toFun i d:=enlarged D d i
  map_add' x y:= funext fun i=> LinearMap.ext (gunsum D (d:=i) x y)
  map_smul' r v:= by ext1 i; apply LinearMap.ext; intro x; rw [show enlarged D i (r • v) x=(r:ℂ) • _ from gs ..]; exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) r _).symm
lemma accent (D): Hom (port Al) (gest D):= fun i j=> funext fun x=> LinearMap.ext (fun s=> (fists D i j s).symm)

section Roller
variable {X Y : Type*} [Group X] [Monoid Y]
-- conjug End action general
variable (P:X→* Al)
def acn : X→* Endr Al where
  toFun x:=((LinearMap.mul ℝ Al).flip (P x⁻¹)) ∘ₗ LinearMap.mul ℝ Al (P x)
  map_one':=by apply LinearMap.ext; intro v; change P 1*v*P _=v; rw [inv_one,map_one,one_mul,mul_one]
  map_mul' x y:=by apply LinearMap.ext; intro v; change P (x*y)*v*P _=P x*(P y*v*P y⁻¹)* P x⁻¹; rw [map_mul,mul_inv_rev,map_mul]; simp only [mul_assoc]
lemma acn_rem (p:X) (i:Al): acn P p i=P p*i*P p⁻¹:=rfl
lemma acn_mul i (x y:Al): acn P i (x*y)=acn P i x*acn P i y := by simp_rw [acn_rem]; simp only [mul_assoc]; rw [← mul_assoc (P i⁻¹),← map_mul,inv_mul_cancel,map_one,one_mul]
end Roller
section RealSpeed
variable {X K : Type*} [AddCommGroup X] [Module ℝ X] [Module ℂ X] [IsScalarTower ℝ ℂ X] [Module.Finite ℝ X] [Module.Finite ℂ X] -- omit atTop
-- read real coords via arbitrary ℂ linear funcs (basis not necessarily descending). Real probe includes both.
abbrev Yf (b:X→ₗ[ℂ]ℂ) :X→ₗ[ℝ] ℂ:=b.restrictScalars ℝ
def Hx (X : Type*) [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]: X→ₗ[ℝ] ((X→ₗ[ℂ]ℂ) × Bool)→ℝ:= LinearMap.pi fun i=> (if i.2 then Complex.reCLM else Complex.imCLM).toLinearMap ∘ₗ Yf i.1
lemma Hx_in : Injective (Hx X):=by
  intro x y h; let q:=finBasis ℂ X; apply q.equivFun.injective
  ext1 i; exact Complex.ext (congr_fun h (q.coord i,true)) (congr_fun h (q.coord i,false))
lemma dimmed (f:K→X) (q:Filter K) (z:X): Dips ℂ q f z → Dips ℝ q f z:=fun p=> truth (Hx X) Hx_in fun i=> ((if i.2 then Complex.reCLM else Complex.imCLM).continuous.continuousAt.tendsto.comp (p i.1))
lemma realSends (f :ℝ→X) (v t) (h:Sends f t v): Apit.Price f t v:= Price.collect (Hx X) Hx_in fun i=> (if i.2 then Complex.reCLM else Complex.imCLM).hasFDerivAt.comp_hasDerivAt t (h i.1) -- `Price` namespace clutter
end RealSpeed

def bolt : Al→ₗ[ℝ] ((d:Floor)×(UV d × (UV d→ₗ[ℝ]ℝ)))→ ℝ:= LinearMap.pi fun i => i.2.2 ∘ₗ ((LinearMap.applyₗ i.2.1: (UV i.1→ₗ[ℂ]UV i.1)→ₗ[ℂ]UV i.1).restrictScalars ℝ) ∘ₗ LinearMap.proj i.1
lemma bolt_in : Injective bolt := by
  intro x y h; ext1 d; apply LinearMap.ext; intro a
  let f:=Module.finBasis ℝ (UV d); apply f.equivFun.injective; ext1 i; exact congr_fun h ⟨d,(a,f.coord i)⟩
variable (D : District)
lemma real_p (z) : Apit.Price (fun t=> pulse D (Angles.rise z t)) 0 (gest D z) := by
  apply Price.collect bolt bolt_in; rintro ⟨d,a,v⟩
  have h := cost D (d:=d) z a 0; rw [crest,map_one,Module.End.one_apply] at h
  exact realSends _ _ _ h v
lemma real_cont (p:Stage.SO):Dips ℝ (𝓝 p) (pulse D) (pulse D p):=by
  apply truth bolt bolt_in; rintro ⟨d,a,v⟩
  have H:=dimmed (fun p:Stage.SO=> ledger D d p a) (𝓝 p) (ledger D _ p a) (fun f=> (continu D _ f).continuousAt)
  exact H v
lemma whip {K:Type*} {p:Filter K} {f g:K→Al} {x y} (u:Dips ℝ p f x) (v:Dips ℝ p g y): Dips ℝ p (fun i=> f i*g i) (x*y):=by
  refine trav (H:=fun k=>(LinearMap.mul ℝ Al) (f k)) (h:=LinearMap.mul ℝ Al x) ?_ g y v
  exact fun i=> maps u ((LinearMap.mul ℝ Al).flip i)
lemma real_arc (i : Al→ₗ[ℝ]ℝ) v: Continuous (fun p=> i (acn (pulse D) p v)) := by
  apply continuous_iff_continuousAt.mpr; intro p
  let P:=pulse D; have hp:= subs (real_cont D p⁻¹) (fun p:Stage.SO=>p⁻¹) (continuous_inv.continuousAt (x:=p)).tendsto
  exact whip (whip (real_cont D p) (Sailing.fixed v)) hp i
lemma orbit_phy (z v): Apit.Price (fun t=> acn (pulse D) (Angles.rise z t) v) 0 (boy (gest D) z v):= by
  let P:=pulse D; let F:=gest D z
  have h: Apit.Price (fun t : ℝ=> P (rise z t) * v) 0 (F*v) := Price.map (real_p D z) ((LinearMap.mul ℝ Al).flip v)
  have e: Apit.Price (fun t : ℝ=> P (rise z t)⁻¹) 0 (-F):= by
    rw [show (fun t : ℝ=> P (rise z t)⁻¹)=(fun t=>P (rise z (-t))) from funext fun t=>congr_arg P (Subtype.ext (param_inv z t))]; exact Price.perigee (real_p D z)
  have ht:= Price.product h e (LinearMap.mul ℝ Al); rw [crest,inv_one,map_one,one_mul] at ht; change Price _ 0 (F*v*1+v*(-F)) at ht; rw [mul_one,show v * -F = -(v*F) from mul_neg v F,← sub_eq_add_neg] at ht; exact ht

-- nonlinear real metric
def musical : Dome (boy (gest D)):= Apit.moon _ (acn (pulse D)) (real_arc D) (orbit_phy D)
end YM.GaugeFieldConstruction.Ember.Loft
