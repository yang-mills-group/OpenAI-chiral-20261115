import GaugeFieldConstruction.Aerie
/-!
# Scaling the Lie-closure. Adequate operations on the finite frame.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6300
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Loft
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Row
open Floor Carat Dawn Sailing Angles
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate
attribute [local instance] iG iF iX iU iT2 iW2 iV iS floatA floatY
attribute [local instance 30000] topx topg

local notation "F" => port Al
-- Lie closure. actual as function frame
inductive Nap (Y : C1 Al):Apit.G → Al → Prop
  | gen (a):Nap Y a (Y a)
  | zero:Nap Y 0 0
  | add {a b c d}: Nap Y a b→ Nap Y c d→Nap Y (a+c) (b+d)
  | sm (r:ℝ) {a b}: Nap Y a b→Nap Y (r • a) (r • b)
  | fork {a b c d}: Nap Y a b→Nap Y c d→Nap Y (bracket a c) ((port Al).l b d)
namespace Nap
variable {Y:C1 Al} {a b c d}
lemma sub (h:Nap Y a b) (u:Nap Y c d):Nap Y (a-c) (b-d):=by
  have v:= h.add (Nap.sm (-1) u); rw [show (-1:ℝ) • c= -c from neg_one_smul ℝ c,show (-1:ℝ) • d= -d from neg_one_smul ℝ d, show a + -c=a-c from (sub_eq_add_neg ..).symm,show b+ -d=b-d from (sub_eq_add_neg ..).symm] at v; exact v
lemma hem (p:Y∈ Apit.fixed (gr₁ timbre meter)) (x : Signed) (u:Nap Y a b):Nap Y (timbre.A x a) (meter x b) := by
  induction u with
  | gen a=> rw [(fix₁ _).mp p]; exact gen _
  | zero=> rw [map_zero,map_zero]; exact Nap.zero
  | add _ _ i j=> rw [map_add,map_add]; exact i.add j
  | sm r _ i=> rw [map_smul,map_smul]; exact sm r i
  | fork _ _ i j=> rw [mapT,timbre.joins]; exact i.fork j
lemma guard (p:∀ x,Canny (Y x)) (u:Nap Y a b):Canny b:= by
  induction u with
  | gen a=> exact p a
  | zero=> exact Canny.nil
  | add _ _ a b => exact Canny.add a b
  | sm r _ a => exact Canny.scale a r
  | fork _ _ a b=> exact Submodule.sub_mem allowed.P (Canny.large a b) (Canny.large b a)
end Nap
namespace Recoil
variable (D:Carat)
-- move actual *back* to free by f. ℝ.
def up (x:Al): Al:= fun i=> (lens D i).toLinearMap ∘ₗ x i ∘ₗ (lens D i).symm.toLinearMap
def rev : Al≃ₗ[ℝ] Al where
  toFun x i:= (lens D i).symm.toLinearMap ∘ₗ x i ∘ₗ (lens D i).toLinearMap
  invFun:= up D
  left_inv x:= by ext1 i; apply LinearMap.ext; intro v; simp [up]
  right_inv x:=by ext1 i; apply LinearMap.ext; intro v; simp [up]
  map_add' x y:=by ext1 i; apply LinearMap.ext; intro v; simp
  map_smul' r v:= by ext1 i; apply LinearMap.ext; intro x; change (lens D _).symm (r • v i _) = r • ((lens D i).symm _); exact ((lens D i).symm.toLinearMap.restrictScalars ℝ).map_smul r _
lemma dim (x:Al) (d i): rev D x d i=(lens D d).symm (x d (lens D d i)):=rfl
lemma bright (x:Al) (d i): (rev D).symm x d i=(lens D d) (x d ((lens D d).symm i)):=rfl
lemma light (a b:Al) : rev D (a*b)=rev D a* rev D b:=by ext1 d; apply LinearMap.ext; intro v; change (lens D _).symm (a d (b d _))=(lens D _).symm (a d (lens D d ((lens D d).symm (b d _)))); rw [(lens D d).apply_symm_apply]
lemma fork a b : rev D ((port Al).l a b)= (port Al).l (rev D a) (rev D b):=by change rev D (a*b-b*a)=_; rw [map_sub,light,light]; rfl
lemma thermal (v) (s:Signed) : rev D (meter s v)=meter s (rev D v):=by
  ext1 i; apply LinearMap.ext; intro x; rw [metered,dim,dim, metered]
  apply (lens D i).injective; rw [LinearEquiv.apply_symm_apply,(D.G i).h, (D.G i).h]; rw [LinearEquiv.apply_symm_apply]
lemma directed (v) (u:Canny v):Canny (rev D v):= by
  constructor
  · intro d; rw [dim,(D.G d).unit,u.unit,map_zero]
  · intro d x; rw [dim,dim]; apply (lens D d).injective; rw [LinearEquiv.apply_symm_apply,(D.G d).charge,(D.G d).charge,LinearEquiv.apply_symm_apply,u.soul]
  · intro d x; rw [dim,dim]; apply (lens D five).injective; rw [LinearEquiv.apply_symm_apply,D.include_, D.include_,u.up,(lens D d).apply_symm_apply]
  intro g d x; rw [dim,dim]; apply (lens D d).injective; rw [LinearEquiv.apply_symm_apply,(D.G d).f,(D.G d).f,u.moon,(lens D d).apply_symm_apply]
-- Unscaled grammar
end Recoil

def napker (x : C1 Al): Submodule ℝ Al where
  carrier:={v| Nap x 0 v}
  add_mem' {i j} h w:=by change Nap x 0 (i+j); have u:=Nap.add (show Nap x 0 i from h) (show Nap x 0 j from w); rw [add_zero] at u; exact u
  smul_mem' a g h:= by
    change Nap _ 0 _; have p:= Nap.sm a (show Nap x 0 g from h); rw [smul_zero] at p; exact p
  zero_mem':= Nap.zero

def arctic (Q:Carat) (v : C1 Al) (p:v∈ Apit.fixed (gr₁ timbre meter)): Turbine timbre (port Al) meter where
  s:= (Recoil.rev Q).toLinearMap ∘ₗ v
  joins := (fix₁ _).2 (fun i x=> by change meter i (Recoil.rev Q _) = _; rw [← Recoil.thermal, (fix₁ _).mp p]; rfl)
  R:= (napker v).map (Recoil.rev Q).toLinearMap
  fixedP i u h:= by
    obtain ⟨a,b,rfl⟩:=h; have ht:=Nap.hem p i (show Nap v 0 a from b); rw [map_zero] at ht; exact ⟨meter i a,ht,Recoil.thermal ..⟩
  fold i x h:= by
    obtain ⟨x,a,rfl⟩:=h; have v:= Nap.fork (Nap.gen (Y:=v) i) (show Nap v 0 x from a); rw [map_zero] at v; exact ⟨_,v,Recoil.fork ..⟩ -- name collision
  in_ i j:= by
    have h: Nap v 0 ((port Al).l (v i) (v j) - v (bracket i j)):= by
      have ht:= Nap.sub (Nap.fork (Nap.gen (Y:=v) i) (Nap.gen j)) (Nap.gen (bracket i j)); rw [sub_self] at ht; exact ht
    refine ⟨_,h,?_⟩; change Recoil.rev Q _=(port Al).l _ _-_; rw [map_sub,Recoil.fork]; rfl
  cross x y h b:= by
    obtain ⟨x,h,rfl⟩:=h; obtain ⟨y,b,rfl⟩:=b; have V:=Nap.fork (show Nap v 0 x from h) (show Nap v 0 y from b); rw [map_zero] at V; exact ⟨_,V,Recoil.fork ..⟩
lemma arctic_r (Q Y p): finrank ℝ (arctic Q Y p).R= finrank ℝ (napker Y):=LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Recoil.rev Q).toLinearMap (Recoil.rev Q).injective (napker Y)).symm -- adjust
lemma enclose {Q Y p x z} (e:z-(arctic Q Y p).s x∈(arctic Q Y p).R): Nap Y x ((Recoil.rev Q).symm z):=by
  obtain ⟨k,H,h⟩:= e; change Recoil.rev Q k=z - Recoil.rev Q (Y x) at h
  have p:= Nap.add (show Nap Y 0 k from H) (Nap.gen x); rw [zero_add, show k+Y x= (Recoil.rev Q).symm z from (Recoil.rev Q).injective (by rw [map_add,h]; rw [sub_add_cancel, (Recoil.rev Q).apply_symm_apply])] at p; exact p

variable {S:City} {P:Axis→ Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
namespace Beyond
variable (Q : Dawn L C u) (p: Typical C Q.tect) (H:Blush S atTop u)

def step (Y: Typical C Q.tect) (i):=arctic (u (Q.i i)) (angleT C Q.tect) Y.twists

include H
lemma ticks (x): Dips ℝ atTop (fun k=> (step Q p k).s x) (gest Q.d x) := by -- replace
  apply truth bolt bolt_in
  rintro ⟨d,v,b⟩
  let U k:= desks C (u (Q.i k)) d Q.tect x v
  have e:= excursion (Q.pays H x d) v
  exact dimmed _ _ _ e b

include p
lemma ahead : ∃ i:ℕ→ℕ, StrictMono i ∧ ∃ Y:ℕ→C1 Al,(∀ x,Dips ℝ atTop (fun k=> Y k x) (gest Q.d x)) ∧
    ∀ j,Y j∈ Apit.fixed (gr₁ timbre meter) ∧ Hom (port Al) (Y j) ∧ ∀ x,Nap (angleT C Q.tect) x ((Recoil.rev (u (Q.i (i j)))).symm (Y j x)):= by
  let N:=napker (angleT C Q.tect)
  letI : AddCommGroup ↥N:=@Submodule.addCommGroup ℝ Al _ _ _ N
  letI : Module.Finite ℝ ↥N:=@FiniteDimensional.finiteDimensional_submodule ℝ Al _ _ _ _ N
  obtain ⟨i,s,j,y,h⟩:= beacon (D:=↥N) meter (step Q p) mapT (gest Q.d) (accent Q.d) (musical Q.d) (ticks Q p H) (fun i=> arctic_r (u (Q.i i)) (angleT C Q.tect) p.twists)
  exact ⟨i,s,j,y,fun m=>⟨(h m).1,(h m).2.1,fun x=> enclose (Q:=u (Q.i (i m))) (p:=p.twists) ((h m).2.2 x)⟩⟩
end Beyond
end YM.GaugeFieldConstruction.Ember.Loft
