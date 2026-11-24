import GaugeFieldConstruction.Turquoise

/-!
# Build returned section, including Lie-closure and this very symbol's prices
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6700
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Loft
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Row Beyond Wardrobe
open Floor Carat Dawn Sailing Angles
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate
attribute [local instance] iG iF iX iU iT2 iW2 iV iS floatA floatY
attribute [local instance 30000] topx topg
variable {S: City} {P:Axis→Across} {L:Sheds S P} {C:Supplies L} {u:ℕ→Carat}

structure Valley (Q:Dawn L C u) where
  pi : C1 Al -- representation on all grades d commuting with inclusions. actual S convention
  paid (x): Nap (angleT C Q.tect) x (pi x)
  lie : Hom (port Al) pi
  caller (d) : FreeName d
  turns x d i: pi x d ((caller d).c i)=(caller d).c (enlarged Q.d d x i)
  flight d x : Calibration.lift d ((caller d).c x)=(caller five).c (Calibration.lift d x)

variable (Q : Dawn L C u) (v: Typical C Q.tect) (H:Blush S atTop u)
local instance ot : AddCommGroup ↥allowed.P:= @Submodule.addCommGroup ℝ Al _ _ _ _
local instance ot2: AddCommGroup ↥(Apit.fixed allowed.hall):= @Submodule.addCommGroup ℝ _ _ _ _ _
private instance : Module.Finite ℝ ↥(Apit.fixed allowed.hall):= by
  haveI :=@FiniteDimensional.finiteDimensional_submodule ℝ Al _ _ _ _ allowed.P
  exact @FiniteDimensional.finiteDimensional_submodule ℝ _ _ _ _ _ _


def composed {d} (p q:FreeName d):FreeName d where
  c:=p.c.trans q.c
  h s x:=by simp [p.h,q.h]
  unit:=by simp [p.unit,q.unit]
  f s x:=by simp [p.f,q.f]
  charge s:=by simp [p.charge,q.charge]

section
variable (a : Apit.fixed allowed.hall)
def reefer : Al:=1+a.val.val
lemma plus_v (d) (x): reefer a d x = x+a.val.val d x:=rfl
lemma whiteP : Canny a.val.val:= a.val.property
lemma artifact s : meter s a.val.val=a.val.val:=congr_arg Subtype.val (a.property s)
lemma sendsP (s d x): a.val.val d (spinFrame d s x)=spinFrame d s (a.val.val d x) := by
  have p:= artifact a s; have hv:= LinearMap.congr_fun (congr_fun p d) (spinFrame d s x)
  rw [metered,both'] at hv; exact hv.symm

variable (p : ∀ d, Injective (reefer a d))
def fitted (i:Floor): FreeName i where
  c:=LinearEquiv.ofBijective _ ⟨p i,LinearMap.surjective_of_injective (p i)⟩
  unit:=by change reefer _ _ _=_; rw [plus_v,(whiteP a).unit]; simp only [add_zero]
  h s z:=by change reefer a i _=spinFrame i s (reefer a i z); rw [plus_v,plus_v,map_add,sendsP] -- adjust
  f s z:=by change reefer a i _=flavors i s (reefer a i z); rw [plus_v,plus_v,map_add,(whiteP a).moon]
  charge z:=by change reefer a i _=shade i (reefer a i z); rw [plus_v,plus_v,map_add,(whiteP a).soul]
lemma paysT d x : Calibration.lift d ((fitted a p d).c x)=(fitted a p five).c (Calibration.lift d x):=by change Calibration.lift _ (reefer a d x)=reefer _ _ _; rw [plus_v,plus_v,map_add, (whiteP a).up]
end

lemma unit_live (g : ℕ→ Apit.fixed allowed.hall) (u:Dips ℝ atTop g 0): ∀ᶠ i in atTop, ∀ d, Injective (reefer (g i) d):= by
  apply eventually_all.mpr; intro d
  let W d : Al→ₗ[ℝ] Piece d:= LinearMap.proj d; let t i:UV d→ₗ[ℝ] UV d:=(reefer (g i) d).restrictScalars ℝ
  have h:Dips ℝ atTop (fun i=> (g i).val.val) 0:= maps u (allowed.P.subtype ∘ₗ (Apit.fixed allowed.hall).subtype)
  have P x:Dips ℝ atTop (fun i=>t i x) x:= by
    have Z:= maps (maps h (W d)) ((LinearMap.applyₗ x: Piece d→ₗ[ℂ] UV d).restrictScalars ℝ)
    rw [map_zero,map_zero] at Z; have p:= Sailing.plus (Sailing.fixed x) Z; rw [add_zero] at p; exact p
  exact (ringed (f:=t) (p:=atTop) (L:=LinearMap.id) P injective_id).1

include v H
lemma returned : Nonempty (Valley Q):= by
  obtain ⟨i,w,k,g,y⟩:= ahead Q v H
  let A (n : ℕ) := k n
  let Gf (n:ℕ):=u (Q.i (i n))
  let R n:=Recoil.rev (Gf n)
  let q (i:ℕ) : Party allowed:= ⟨k i,(y i).2.1,(y i).1,fun x=>by
    have h: Canny ((R i).symm ((k i) x)):= ((y i).2.2 x).guard v.canny
    change Canny _; rw [← (R i).apply_symm_apply ((k i) x)]; exact Recoil.directed _ _ h⟩
  let j: Party allowed:= ⟨gest Q.d,accent Q.d, whorl Q.d, holy Q.d⟩ -- Canny defeq
  obtain ⟨x,p,r⟩:= pitch q j g (musical Q.d)
  obtain ⟨n,V,h⟩:= (r.and (unit_live x p)).exists
  let c:=composed (fitted (x n) h four) ((Gf n).G four)
  refine ⟨⟨(R n).symm.toLinearMap ∘ₗ k n,(y n).2.2,?_,(fun d=>composed (fitted (x n) h d) ((Gf n).G d)),?_,?_⟩⟩
  · intro x z; apply (R n).injective
    change R n ((port Al).l ((R n).symm _) ((R n).symm _))= R n ((R n).symm (k n _)); unfold R; rw [Recoil.fork]; simp only [LinearEquiv.apply_symm_apply]; exact (y n).2.1 x z
  · intro a d z; let p:=fitted (x n) h d
    have T:= (q n).spends j (x n) V a; change (k n a)*reefer (x n)=reefer (x n)*gest Q.d a at T
    have hv: k n a d (p.c z)=p.c (enlarged Q.d d a z):= LinearMap.congr_fun (congr_fun T d) z
    change (Recoil.rev (Gf n)).symm (k n a) d ((lens (Gf n) d) (p.c z))=lens (Gf n) d _; rw [Recoil.bright,(lens (Gf n) d).symm_apply_apply,hv]; rfl
  intro d z; let A:=x n
  change Calibration.lift d (lens (Gf n) d ((fitted A h d).c z))=((Gf n).G five).c _
  rw [← Carat.include_,paysT]; rfl
#print axioms returned
end YM.GaugeFieldConstruction.Ember.Loft
