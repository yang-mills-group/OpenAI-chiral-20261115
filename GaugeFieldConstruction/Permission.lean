import GaugeFieldConstruction.YieldSh

/-!
# U2 & U5. Algebraic part of change of calibration frame

Throughout this costs a point identification at common origin and label spaces already
sized to U2. Need the estimates on the existence constructions to apply it. The general
intertwiner need not send mean to mean; it sends the unit symbol to itself.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5500
noncomputable section
namespace YM.GaugeFieldConstruction.Empire
open Calibration RawBank Floor Cauchy Row Record Phys Function Filter Stage
open scoped BigOperators

variable {I : Type*} (L : Labels I) {d : Floor}
abbrev one (d : Floor) : UV d := (1,0) -- rest zero
abbrev readOne (d : Floor) : UV d →ₗ[ℂ] ℂ:=LinearMap.fst ..
lemma sends_1 (d s) : spinFrame d s (one d)=one d := by
  simp only [one,spinFrame,MonoidHom.coe_mk,OneHom.coe_mk,LinearMap.prodMap_apply,Module.End.one_apply]
  simp
lemma sends_2 (d x s) : readOne d (spinFrame d s x)=readOne d x := rfl
lemma charges_1 (d s): flavors d s (one d)=one d:= by simp only [one,flavors,MonoidHom.coe_mk,OneHom.coe_mk,LinearMap.prodMap_apply,Module.End.one_apply]; simp
lemma charges_2 (d x s): readOne d (flavors d s x)=readOne d x:=rfl

local instance iG (d : Floor) : AddCommGroup (UG d):= @Submodule.addCommGroup ℂ (J g) _ _ _ _
local instance iF (d : Floor) : AddCommGroup (UF d):= @Submodule.addCommGroup ℂ (J f) _ _ _ _
local instance iX (d : Floor) : AddCommGroup (UX d):= @Submodule.addCommGroup ℂ (J x) _ _ _ _
local instance iU (d : Floor) : AddCommGroup (UV d):= inferInstanceAs (AddCommGroup (Prod _ _))
def centre (d : Floor) : Module.End ℂ (UV d):= LinearMap.id - LinearMap.smulRight (readOne d) (one d)
lemma centre_at (x : UV d) : centre d x=x-x.1 • one d:= rfl
lemma mean_one (u : UV d) : centered (centre d u) := by change readOne d (centre d u) = 0; rw [centre_at,map_sub,map_smul]; change u.1-u.1*1=0; simp
lemma mark (u : UV d) (v : centered u): centre d u=u := by rw [centre_at,v,zero_smul,sub_zero]
lemma centre_spin (i) (x : UV d): centre d (spinFrame d i x)=spinFrame d i (centre d x):= by rw [centre_at,centre_at,map_sub,map_smul,sends_1]; rfl
lemma centre_f (i) (x : UV d) : centre d (flavors d i x)=flavors d i (centre d x):= by rw [centre_at,centre_at,map_sub,map_smul,charges_1]; rfl
lemma alone (Ω) (D : District): enlarged D d Ω (one d)=0 := awake ..
section
variable {α A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℂ A] [Module ℂ B]
def go (α : Type*) (L : A→ₗ[ℂ]B) : (α→A) →ₗ[ℂ] (α→B) := LinearMap.pi fun i=> L ∘ₗ LinearMap.proj i
lemma go_at (L:A→ₗ[ℂ]B) (p : α→A) i : go α L p i=L (p i):=rfl
end
structure FreeName (d : Floor) where
  c : UV d ≃ₗ[ℂ] UV d
  h (i : Signed) (b) : c (spinFrame d i b)= spinFrame d i (c b)
  f (i : Flavor) (b): c (flavors d i b)=flavors d i (c b)
  unit : c (one d)=one d
  charge (u) : c (shade d u)=shade d (c u)
namespace FreeName
variable (c : FreeName d)
def swapped : FreeName d where
  c:=c.c.symm
  h i b := c.c.injective (by rw [c.c.apply_symm_apply,c.h,c.c.apply_symm_apply])
  f i b:= c.c.injective (by rw [c.c.apply_symm_apply,c.f,c.c.apply_symm_apply])
  unit := c.c.symm_apply_eq.mpr c.unit.symm
  charge u:= c.c.injective (by rw [c.c.apply_symm_apply,c.charge,c.c.apply_symm_apply])
lemma swap_twice : c.swapped.swapped=c := by cases c; rfl

def price := centre d ∘ₗ c.c.toLinearMap
lemma illumination (p) (h : white (d:=d) p): white (c.price p) := by
  intro g; unfold price; simp only [LinearMap.comp_apply]; rw [← centre_f]; change centre d (flavors d g (c.c p))= _; rw [← c.f,h]; rfl
lemma take (p s) : c.price (spinFrame d s p) = spinFrame d s (c.price p) := by change centre d (c.c _)=spinFrame _ _ (centre _ _); rw [c.h,centre_spin]; rfl
lemma quote (x : invariant L d) : go I c.price x.val∈invariant L d := ⟨fun i=>⟨mean_one (c.c (x.val i)), c.illumination _ (x.property.1 i).2⟩,fun i s=>by
  change spinFrame d s (c.price (x.val i)) = pay _ (c.price _)
  rw [← c.take,x.property.2]; cases L.cost s i <;> simp⟩ -- adjust

def bought (c:FreeName d) : invariant L d→ₗ[ℂ] invariant L d := (go I c.price ∘ₗ (invariant L d).subtype).codRestrict _ (quote L c)
lemma covered (v:UV d) (p : centered v) : c.swapped.price (c.price v)=v := by
  change centre d (c.swapped.c (centre d (c.c v)))=v; rw [centre_at (c.c v),map_sub,map_smul,c.swapped.unit]
  change centre _ (c.c.symm _ - _)=_; rw [c.c.symm_apply_apply,map_sub,map_smul,mark v p,centre_at (one d),show (one d).1=1 from rfl,one_smul,sub_self,smul_zero,sub_zero]
lemma alive (v : invariant L d) : bought L c.swapped (bought L c v)=v:= Subtype.ext (funext fun i=>c.covered _ (v.property.1 i).1)

def total (c : FreeName d) : invariant L d≃ₗ[ℂ] invariant L d where
  __:=bought L c
  invFun:= bought L c.swapped
  left_inv v:=alive L c v
  right_inv v:= by have h:=alive L c.swapped v; rw [c.swap_twice] at h; exact h
lemma total_value (x : invariant L d) (i): (total L c x).val i=c.price (x.val i):=rfl
lemma inv (x : invariant L d) : (total L c).symm x=(total L c.swapped) x:=rfl
-- For odd polar covariant maps, centering doesn't change the images
lemma toll (u : invariant L d) (i) (p : L.move Count.allf i=i) (h : L.cost Count.allf i=true): centered (c.c (u.val i)) := by
  have hv : spinFrame d Count.allf (c.c (u.val i))= - c.c (u.val i):= by rw [←c.h, u.property.2, p,h, pay_true,map_neg]
  have ht:= congr_arg (readOne d) hv; rw [sends_2,map_neg] at ht; exact Count.negate ht
lemma Vcost (x:OneW) (i) (c:FreeName five) : (total Raw.v c x).val i=c.c (x.val i) := mark _ (toll Raw.v c x i rfl rfl)
-- VS remove using central orientation invariant arrays, so Fif. show allf on ordered.
lemma Xcost (x:BothV) (i) (c:FreeName five) : (total Raw.vsAct c x).val i=c.c (x.val i) := by
  have e : Raw.vsAct.move Count.allf i=i := Prod.ext rfl (show Raw.symAct.move Count.allf i.2=i.2 from ordered_same i.2)
  exact mark _ (toll Raw.vsAct c x i e rfl)

lemma rot_back (d) (p q : FreeName d) (h : p.c=q.c) : p=q := by cases p; cases q; congr
end FreeName
end YM.GaugeFieldConstruction.Empire
