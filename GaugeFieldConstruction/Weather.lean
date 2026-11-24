import GaugeFieldConstruction.Proton
import GaugeFieldConstruction.Door

/-!
# Defect of an H-equivariant section. Algebra and projected equations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Function Module Set Stage Filter
open scoped BigOperators Topology
variable {D W : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup W] [Module ℝ W] {H : Type*} [Group H] {p: Helm H}

structure Mount (W : Type*) [AddCommGroup W] [Module ℝ W] where
  l : W→ₗ[ℝ] Endr W
  swap (x y:W): l x y= -l y x
  jac (x y z:W): l x (l y z)+l y (l z x)+l z (l x y)=0
structure Vap (p : Helm H) (w : Mount W) (D : Type*) [AddCommGroup D] [Module ℝ D] where
  z : H→*Endr D
  u : H→*Endr W
  cov i a b:u i (w.l a b)= w.l (u i a) (u i b)
variable {w : Mount W} {r: Vap p w D}
def Hom (w: Mount W) (t:C1 W): Prop := ∀ i j,w.l (t i) (t j)=t (bracket i j)
def tariff (w : Mount W) (g:C1 W) : C2 W:=⟨w.l.compl₁₂ g g - bracket.compr₂ g,fun i j=>by
  change w.l _ _-g (bracket i j)+(w.l _ _-g (bracket j i))=0; rw [w.swap (g i) (g j),flips,map_neg]; abel⟩
lemma tariff_v (w : Mount W) (g:C1 W) (x y:G): (tariff w g).val x y=w.l (g x) (g y)-g (bracket x y):= rfl
lemma tariff_zero (g) : tariff w g=0 ↔ Hom w g:= by
  constructor
  · intro e i j; apply sub_eq_zero.mp; exact LinearMap.congr_fun (LinearMap.congr_fun (congr_arg Subtype.val e) i) j
  intro a; apply Subtype.ext; apply LinearMap.ext; intro i; apply LinearMap.ext; intro j; exact sub_eq_zero.mpr (a i j)
lemma cabin (g): Cycle (w.l ∘ₗ g) (tariff w g) := by
  intro x y z
  let a:= w; simp only [tariff_v, LinearMap.comp_apply, map_sub]
  have hp:g (bracket (bracket y z) x)+g (bracket (bracket z x) y)+g (bracket (bracket x y) z)=0:= by rw [← map_add,← map_add,flips (bracket y z), flips (bracket z x),flips (bracket x y), ← neg_add,← neg_add,jac x y z,neg_zero,map_zero]
  have hu:=w.jac (g x) (g y) (g z)
  rw [w.swap (g (bracket x y)) _,w.swap (g (bracket y z)) _,w.swap (g (bracket z x)) _,eq_neg_of_add_eq_zero_right hp,eq_neg_of_add_eq_zero_right hu]; abel
lemma stature (w : Mount W) (g) (u:Hom w g): Stood (w.l ∘ₗ g) where
  acts i j:=by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.mul_apply]; rw [← u]
    have h:=w.jac (g i) (g j) x; rw [w.swap x (g i), map_neg, w.swap x _] at h; rw [← neg_neg (w.l (w.l _ _) _),eq_neg_of_add_eq_zero_right h]; abel

abbrev Wave (r : Vap p w D) := fixed (gr₁ p r.z)
abbrev Patch (r : Vap p w D) := fixed (gr₂ p r.z)

structure Weather (r:Vap p w D) where
  k:D→ₗ[ℝ] W
  faithful : Injective k
  L: W→ₗ[ℝ]D
  retract x : L (k x)=x
  h (i:H) x: r.u i (k x)= k (r.z i x) -- change
  j:C1 W
  kisses : j∈ fixed (gr₁ p r.u)
  cross x y:w.l (k x) (k y) ∈ LinearMap.range k
  fold i x:w.l (j i) (k x) ∈ LinearMap.range k
  match_ i j': (tariff w j).val i j'∈ LinearMap.range k
namespace Weather
variable (T:Weather r)
lemma reached (x: W) (v:x∈LinearMap.range T.k): T.k (T.L x)=x:= by obtain ⟨y,rfl⟩:=v; rw [T.retract]
def offer (c: Wave r): C1 W:= T.j+T.k ∘ₗ c.val
lemma achieve (c : Wave r) : offer T c∈ fixed (gr₁ p r.u):= (fix₁ ..).mpr (fun g x=> by
  rw [offer, LinearMap.add_apply,map_add,(fix₁ T.j).mp T.kisses]; change _+r.u g (T.k _)=_+T.k _; rw [T.h,(fix₁ _).mp c.property]) -- tactic arg
lemma safeO (c: Wave r) (x i) : w.l (T.offer c i) (T.k x) ∈ LinearMap.range T.k := by
  rw [offer,LinearMap.add_apply,map_add]; exact Submodule.add_mem _ (T.fold ..) (T.cross ..)
def active (c : Wave r): Tour D:= (w.l.compl₁₂ (offer T c) T.k).compr₂ T.L
lemma activa (c i x) : T.k (active T c i x)=w.l (offer T c i) (T.k x):=reached T _ (safeO ..)
def pupil (c: Wave r) : Item p (active T c) where
  Z:= r.z
  marks i x g:=T.faithful (by rw [activa, ← T.h g x,← T.h g (((T.active c) i) x),activa,r.cov,(fix₁ _).mp (achieve T c)])
lemma offer0 (x): offer T 0 x=T.j x:=by rw [offer]; simp
lemma came (u: Hom w T.j): Stood (active T 0) := by
  have H:= stature w _ u
  refine ⟨fun i j=>LinearMap.ext fun x=>?_⟩; apply T.faithful
  simp only [activa,offer0, LinearMap.sub_apply, map_sub,Module.End.mul_apply]; exact LinearMap.congr_fun (H.acts i j) _

-- base R, beta inside k, C²

def milled : C2 D:=⟨(tariff w T.j).val.compr₂ T.L,fun i j=>by change T.L _+T.L _=_; rw [← map_add,show _+_= _ from (tariff w T.j).property i j,map_zero]⟩
lemma mill (x y:G): T.k (T.milled.val x y)= (tariff w T.j).val x y:=T.reached _ (T.match_ ..)
def rho : Patch r:= ⟨T.milled,(fix₂ T.milled).mpr (fun i x y=>by apply T.faithful; rw [← T.h,mill,mill,tariff_v,tariff_v,map_sub,r.cov]; rw [← p.joins]; simp_rw [(fix₁ _).mp T.kisses])⟩
lemma pure (h:Hom w T.j):rho T=0:=Subtype.ext (Subtype.ext (LinearMap.ext fun x=> LinearMap.ext fun y=> T.faithful (show T.k _=T.k 0 from (T.mill x y).trans (by rw [(tariff_zero _).2 h]; exact (T.k.map_zero).symm)))) -- incompatible
-- cross bilinear

def Z (f g: Wave r) : Bile W:= w.l.compl₁₂ (T.k ∘ₗ f.val) (T.k ∘ₗ g.val)
def highQ (f g: Wave r) : C2 D := ⟨ (1/2:ℝ) • ((Z T f g).compr₂ T.L+(Z T g f).compr₂ T.L),fun x y=> by
  change (1/2:ℝ) • (T.L (w.l (T.k (f.val x)) _)+ T.L (w.l (T.k (g.val x)) _))+(1/2:ℝ) • (T.L (w.l (T.k (f.val y)) _)+T.L (w.l (T.k (g.val y)) _))= _
  rw [w.swap (T.k (f.val x)), w.swap (T.k (g.val x)),map_neg,map_neg, smul_add,smul_add,smul_neg,smul_neg]; simp only [LinearMap.comp_apply]; abel⟩
lemma tide (f g:Wave r) (x y : G): T.k ((highQ T f g).val x y)= (1/2:ℝ) • (w.l (T.k (f.val x)) (T.k (g.val y))+w.l (T.k (g.val x)) (T.k (f.val y))):= by
  change T.k ((1/2:ℝ) • (T.L (w.l (T.k (f.val x)) (T.k (g.val y)))+T.L (w.l (T.k (g.val x)) (T.k (f.val y)))))=_; rw [map_smul,map_add, T.reached _ (T.cross ..), T.reached _ (T.cross ..)]
lemma tide_h (f g:Wave r): highQ T f g∈fixed (gr₂ p r.z) := (fix₂ _).mpr (fun i x y=>by
  apply T.faithful; rw [← T.h,T.tide,T.tide,map_smul,map_add, r.cov, r.cov]
  simp_rw [T.h,(fix₁ _).mp f.property,(fix₁ _).mp g.property])

def highF (f g : Wave r): Patch r:=⟨highQ T f g,tide_h T f g⟩
lemma tower (f g: Wave r) (i j): T.k ((highF T f g).val.val i j)=(1/2:ℝ) • (Z T f g i j+Z T g f i j):= tide ..
lemma halved (u v : Wave r): highF T u v=highF T v u:= Subtype.ext (Subtype.ext (LinearMap.ext (fun i=> LinearMap.ext fun j=> T.faithful (by rw [tower,tower]; exact congr_arg _ (add_comm ..)))))
private lemma add_Q (u v t: Wave r): highF T (u+v) t=highF T u t+highF T v t:= by
  apply Subtype.ext; apply Subtype.ext; ext1 i; ext1 j; apply T.faithful; rw [tower]
  change _= T.k ((highF T u t).val.val _ _+(highF T v t).val.val _ _); rw [map_add,tower,tower]
  have ht : (u+v).val=u.val+v.val:=rfl
  unfold Z; simp [ht, LinearMap.comp_apply,LinearMap.compl₁₂_apply]; module -- abel
private lemma scale_Q (u v : Wave r) (a : ℝ): highF T (a • u) v=a • highF T u v:=by
  apply Subtype.ext; apply Subtype.ext; ext1 i; ext1 j; apply T.faithful; rw [tower]; change _=T.k (a • (highF T u v).val.val _ _); rw [map_smul,tower]; simp [Z]; module

def ear : Wave r →ₗ[ℝ] Wave r →ₗ[ℝ] Patch r:= LinearMap.mk₂ ℝ (highF T)
  (fun u v w=> T.add_Q u v w) (fun a u v=> T.scale_Q u v a) (fun x y z=> by rw [T.halved, T.add_Q,←T.halved x y, ←T.halved x z])
  (fun a x y=> by rw [T.halved,T.scale_Q,T.halved])

def del : Wave r→ₗ[ℝ] Patch r:= delta (T.pupil 0)
def residual (f:Wave r) : Patch r:=T.rho + T.del f+T.ear f f
lemma score (f: Wave r) (i j): T.k ((T.residual f).val.val i j)= (tariff w (T.offer f)).val i j := by
  change T.k (T.milled.val _ _+(lone _ _).val _ _+(T.highQ _ _).val _ _)=_
  rw [map_add,map_add,T.mill,T.tide,turn,map_sub,map_sub]; try simp_rw [T.activa,T.offer0]
  change _ = _; simp only [tariff_v,offer,LinearMap.add_apply,map_add]; simp only [LinearMap.comp_apply,Submodule.subtype_apply]; rw [w.swap (T.k (f.val i)) (T.j j)]; module
lemma bianchi (f : Wave r): Cycle (T.active f) (residual T f).val:=by
  intro i j k; apply T.faithful; rw [map_add,map_add,map_add,map_add]; simp_rw [activa,score]; exact cabin _ i j k
end Weather
end YM.GaugeFieldConstruction.Apit
