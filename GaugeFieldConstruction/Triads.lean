import GaugeFieldConstruction.Pyramid

/-!
# Three-slot prices in U2 domain (comparison only)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Cauchy Row Wick Phys Calibration U1 Function Set Filter Complex
open scoped Topology ContDiff BigOperators
variable {α β γ : Type*}
namespace Lamp

def ticket (L : Lamp α β) (f : J γ →ₗ[ℂ] J β) : Lamp α γ where
  P:= L.P
  pay:= L.pay.compl₁₂ LinearMap.id f
  fast i p q:= L.fast i p (f q)
  charge z x y i j:= (L.charge z x y i j).compl₁₂ LinearMap.id f
  cont p q r i j a b:= L.cont p q r i j a (f b)
  climb x i t y z u v w a b p q:= L.climb x i t y z u v w a b p (f q)
lemma to_touch {L : Lamp α β} {p q c K} (h : L.Touch K c p q) (f : J γ →ₗ[ℂ] J β): (L.ticket f).Touch K c p q :=fun x y χ i d=>h x y χ i (f d)
lemma to_latch {L : Lamp α β} {p q K χ x y} (h : L.Latch χ K x y p q) (f : J γ →ₗ[ℂ] J β): (L.ticket f).Latch χ K x y p q :=fun d=>h (f d)

abbrev gloG (T : Axis→Axis→J GaugePair) : Lamp GaugePair GaugePair := ((Flash T).elect (Flash T)).ticket (LinearMap.id+Phys.swap _)
abbrev gloF (T : Axis→Axis→J Spair) : Lamp Spair Spair := ((Glove T false).elect (Glove T true)).ticket (Phys.swap _)
abbrev gloX (T : Axis→Axis→J Spair) (F : Axis→Axis→J GaugePair) := (gloF T).elect (Flash F)
lemma gamma_g (T) : (gloG T).pay= gaugeGap := by
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
  change weave' ge ge x (y+_) = weave' ge ge _ _+ weave' ge ge _ _; rw [map_add]; rfl
lemma gamma_f (T) : (gloF T).pay=fGap := rfl
lemma gamma_x (T G) : (gloX T G).pay=xGap := rfl
-- maps in z input as well
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
def liftU {α β γ η : Type*} (L : Y →ₗ[ℂ] Coupon α β) (Z : Coupon γ η): Y →ₗ[ℂ] Coupon (α×γ) (β×η) where
  toFun z:= lugs (L z) Z
  map_add' a b:= equalsB (fun i j=>by
    change lugs _ _ _ _=lugs _ _ _ _ + lugs _ _ _ _; simp only [lugs,productRead,on_ket,map_add,LinearMap.add_apply,add_mul])
  map_smul' a b:= equalsB (fun i j=>by
    change lugs _ _ _ _= a • lugs _ _ _ _; simp only [lugs,productRead,on_ket,map_smul,LinearMap.smul_apply,smul_eq_mul,mul_assoc])
def liftD {α β γ η : Type*} (L : Coupon α β) (Z : Y →ₗ[ℂ] Coupon γ η) : Y→ₗ[ℂ] Coupon (α×γ) (β×η) where
  toFun z:= lugs L (Z z)
  map_add' a b:= equalsB (fun i j=>by
    change lugs _ _ _ _=lugs _ _ _ _ + lugs _ _ _ _; simp only [lugs,productRead,on_ket,map_add,LinearMap.add_apply,mul_add])
  map_smul' a b:= equalsB (fun i j=>by
    change lugs _ _ _ _= a • lugs _ _ _ _; simp only [lugs,productRead,on_ket,map_smul,LinearMap.smul_apply,smul_eq_mul,mul_left_comm])

def immerse (f : Y →ₗ[ℂ] Coupon α β) (g : J γ→ₗ[ℂ] J β) : Y→ₗ[ℂ]Coupon α γ where
  toFun x:= (f x).compl₁₂ LinearMap.id g
  map_add' a b:= by rw [map_add]; rfl
  map_smul' r a:= by rw [map_smul]; rfl -- syntax

def solos (p : Wick.Bil α β) (x y:E4) : Coupon α β := p.compr₂ (eye (y-x))
def go (z x y) := immerse (liftU (FG z x y) (solos ge x y)+liftD (solos ge x y) (FG z x y)) (LinearMap.id + Phys.swap Pen)
def fo (z x y) := immerse (liftU (FF false z x y) (solos (yarn true) x y)+liftD (solos (yarn false) x y) (FF true z x y)) (Phys.swap Mode)
def xu (z x y : E4): J Spair →ₗ[ℂ] Coupon Trip Trip := liftU (fo z x y) (solos ge x y)
def xd (z x y : E4): J GaugePair →ₗ[ℂ] Coupon Trip Trip := liftD (solos fGap x y) (FG z x y)

lemma connect_g (T z x y a b) : go z x y (T a b)=(gloG T).charge z x y a b := rfl
lemma connect_f (T z x y a b) : fo z x y (T a b)=(gloF T).charge z x y a b := rfl
lemma connect_x (T G z x y a b): xu z x y (T a b)+xd z x y (G a b)=(gloX T G).charge z x y a b:= rfl
lemma shineG {T} (x y i j) : (gloG T).cost x y i j= eye (y-x) (gaugeGap i j) := by
  change eye (y-x) ((gloG T).pay i j)=_; rw [gamma_g]
lemma shineF (T) (x y i j) : (gloF T).cost x y i j=eye (y-x) (fGap i j) := rfl
lemma shineX (T G) (x y i j) : (gloX T G).cost x y i j = eye (y-x) (xGap i j) := rfl
end Lamp
open Lamp

/-- Triangle. First slot only with degree-four budget; price convention is
 z (J4 or lower) then x and y. In particular, mixed never at z. No new
 diagonal definition is intended by arbitrary equal-position values.
-/
def tri (z x y : E4) (p a b : Book): ℂ :=
    p.1* eye (y-x) (Wick.pair a b) +
-- unit at x or y: z centered part interacts only with uncentered !
    b.1*(eye (x-z) (gaugeGap p.2.1 a.2.1)+eye (x-z) (fGap p.2.2.1 a.2.2.1)) +
    a.1*(eye (y-z) (gaugeGap p.2.1 b.2.1)+eye (y-z) (fGap p.2.2.1 b.2.2.1)) +
    go z x y p.2.1 a.2.1 b.2.1 + fo z x y p.2.2.1 a.2.2.1 b.2.2.1 +
    (xu z x y p.2.2.1 + xd z x y p.2.1) a.2.2.2 b.2.2.2

-- in later use restrict to UV four with no Book.x. -- define linear
private lemma tri_x {z x y : E4} (p a r b): tri z x y p (a+r) b=tri z x y p a b+tri z x y p r b := by
  unfold tri; simp only [Prod.fst_add,Prod.snd_add, map_add,LinearMap.add_apply]; ring
private lemma tri_s (z x y) (p a r b): tri z x y p ((r:ℂ) • a) b = r*tri z x y p a b := by
  unfold tri; simp only [show ∀ v : Book,(r • v).1 = r • v.1 from fun _=>rfl, show (r • a).2=r • a.2 from rfl]
  simp only [Prod.fst_smul,Prod.snd_smul,map_smul,LinearMap.smul_apply]; simp [smul_eq_mul]; ring
private lemma tri_r {z x y p a} (b t):tri z x y p a (b+t)=tri z x y p a b+tri z x y p a t := by
  unfold tri; simp only [Prod.fst_add,Prod.snd_add,map_add]; ring
private lemma tri_t {x y z p a} (r:ℂ) (b): tri z x y p a (r • b)=r*tri z x y p a b := by
  unfold tri; simp only [show ∀ v:Book,(r • v).1=r•v.1 from fun _=>rfl,show (r • b).2=r • b.2 from rfl, Prod.fst_smul,Prod.snd_smul,map_smul]; simp [smul_eq_mul]; ring

def prism (z x y : E4) : Book →ₗ[ℂ] Book→ₗ[ℂ] Book→ₗ[ℂ] ℂ where
  toFun p:= LinearMap.mk₂ ℂ (tri z x y p) (fun u v w=>tri_x ..) (fun a b c=>tri_s z x y p b a c) (fun u t v=>tri_r ..) (fun b i j=>tri_t b j)
  map_add' p q:= by
    apply LinearMap.ext; intro u; apply LinearMap.ext; intro v; change tri z x y (p+q) u v=tri z x y p u v+tri z x y q u v
    unfold tri; simp only [Prod.fst_add,Prod.snd_add,map_add,LinearMap.add_apply]; ring
  map_smul' r p := by
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro b; change tri z x y (r • p) a b=r*tri z x y p a b
    unfold tri; simp only [show (r • p).1=r • p.1 from rfl,show (r • p).2=r • p.2 from rfl, Prod.fst_smul,Prod.snd_smul,map_smul,LinearMap.add_apply,LinearMap.smul_apply]; simp; ring

def Tri (z x y : E4) (p : UV Calibration.Floor.four) (a b : UV Calibration.Floor.five) : ℂ := prism z x y (dress (shells _ p)) (dress (shells _ a)) (dress (shells _ b))
end YM.GaugeFieldConstruction.Flux.One
