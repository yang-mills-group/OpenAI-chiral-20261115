import GaugeFieldConstruction.Wind

/-!
# Further pull by an intertwiner. Equivariant & within preserved constraints.
  Require no choice of a common compact group integration for the perturbed
  representations. Construct the *linear* solution near identity via H1 and projection.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6800
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Function Module Set Filter Fathom Sailing
open scoped Topology BigOperators
variable {H W U:Type*} [Group H] [Ring W] [Module ℝ W] [IsScalarTower ℝ W W] [SMulCommClass ℝ W W] {l:Filter U}
  {h:Helm H}
/-- without using combined action lift at infinity -/
def port (W : Type*) [Ring W] [Module ℝ W] [IsScalarTower ℝ W W] [SMulCommClass ℝ W W] : Mount W where
  l:= LinearMap.mul ℝ W - (LinearMap.mul ℝ W).flip -- mul requires Algebra
  swap x y:=by change x*y-y*x= -(y*x-x*y); abel
  jac x y z:= by change x*(y*z-z*y)-(y*z-z*y)*x+(y*(z*x-x*z)-(z*x-x*z)*y)+(z*(x*y-y*x)-(x*y-y*x)*z)=0; noncomm_ring
abbrev boy (A : C1 W):= (port W).l ∘ₗ A
structure Wardrobe (h: Helm H) (W:Type*) [Ring W] [Module ℝ W] [IsScalarTower ℝ W W] [SMulCommClass ℝ W W] where
  paint : H→*Endr W
  muls (g a b): paint g (a*b)=paint g a*paint g b
  P : Submodule ℝ W
  proper g y : y∈P→paint g y∈P
  lands a b:a∈P→b∈P→a*b∈P
namespace Wardrobe
variable (t : Wardrobe h W)
def hall : H→*Endr t.P where
  toFun i :=(t.paint i ∘ₗ t.P.subtype).codRestrict t.P (fun x=> t.proper i x.val x.property)
  map_one':=by apply LinearMap.ext; intro x; apply Subtype.ext; change t.paint 1 x.val =_; rw [map_one]; rfl
  map_mul' x y:=by apply LinearMap.ext; intro i; apply Subtype.ext; change t.paint (x*y) i.val=_; rw [map_mul]; rfl
lemma castT (x:t.P) (i) : (hall t i x).val=t.paint i x.val:=rfl

structure Party (t : Wardrobe h W) where
  a:C1 W
  hom:Hom (port W) a
  belongs :a∈fixed (gr₁ h t.paint)
  sits x:a x∈t.P
namespace Party
variable {t} (A B:Party t)

def mod (a b:C1 W):Tour W:= (((LinearMap.mul ℝ W) ∘ₗ a)-((LinearMap.mul ℝ W).flip ∘ₗ b))
lemma action i j: (mod A.a B.a) (bracket i j)=(mod A.a B.a) i*(mod A.a B.a) j-(mod A.a B.a) j*(mod A.a B.a) i:=by apply LinearMap.ext; intro z; change A.a _*z-z*B.a _= A.a i*(A.a j*z-z*B.a j)-(A.a j*z-z*B.a j)*B.a i - (A.a j*(A.a i*z-z*B.a i)-(A.a i*z-z*B.a i)*B.a j); rw [← A.hom,← B.hom]; simp [port]; noncomm_ring

def via : Tour t.P where
  toFun i := (mod A.a B.a i ∘ₗ t.P.subtype).codRestrict t.P (fun u=> Submodule.sub_mem _ (t.lands _ _ (A.sits i) u.property) (t.lands _ _ u.property (B.sits i)))
  map_add' i j:= by
    apply LinearMap.ext; intro v; apply Subtype.ext; exact LinearMap.congr_fun (map_add (mod A.a B.a) i j) v.val
  map_smul' r i:= by apply LinearMap.ext; intro v; apply Subtype.ext; exact LinearMap.congr_fun (map_smul (mod A.a B.a) r i) v.val
lemma via_pub (i v): (A.via B i v).val =mod A.a B.a i v.val:=rfl
lemma via_v (i v): (A.via B i v).val=A.a i*v.val-v.val*B.a i:=rfl
lemma stood : Stood (A.via B) := ⟨fun i j=>LinearMap.ext fun x=>Subtype.ext (LinearMap.congr_fun (action A B i j) x.val)⟩
def postal : Item h (A.via B) where
  Z:= t.hall
  marks i k g:=Subtype.ext (by change A.a _*_ - _*B.a _= t.paint g (A.a _*k.val- k.val*B.a _); rw [map_sub,t.muls, t.muls,(fix₁ _).mp A.belongs,(fix₁ _).mp B.belongs]; rfl)

abbrev Offer (t : Wardrobe h W):= fixed (gr₁ h t.hall)
def rage : Offer t :=
  ⟨(A.a-B.a).codRestrict t.P (fun x=>Submodule.sub_mem _ (A.sits x) (B.sits x)),(fix₁ _).mpr (fun i v=>Subtype.ext (by change t.paint i (_-_)=_; rw [map_sub,(fix₁ _).mp A.belongs,(fix₁ _).mp B.belongs]; rfl))⟩
def pulse : fixed t.hall→ₗ[ℝ] Offer t := ((A.via B).flip ∘ₗ (fixed t.hall).subtype).codRestrict _ (fun v=> tame (postal A B) v)
def M (f:fixed t.hall) : Offer t:= A.rage B+A.pulse B f
lemma tilt (f :fixed t.hall): lone (A.via B) (A.M B f).val=0:=by
  change lone _ ((A.rage B).val + (A.via B).flip f.val)=_; rw [map_add, ideal (A.stood B),add_zero]
  apply Subtype.ext; apply LinearMap.ext; intro i; apply LinearMap.ext; intro j; apply Subtype.ext
  have he:= ideal (X:=W) ⟨fun i j=>action A B i j⟩ (1:W)
  have hp := congr_arg (fun (x:C2 W) => x.val i j) he
  change (lone _ _).val _ _= (0:W) at hp; rw [turn] at hp
  simp [mod,← sub_mul] at hp; exact hp
lemma spends (f :fixed t.hall) (h:A.M B f=0) (i): A.a i*(1+f.val.val)=(1+f.val.val)*B.a i:= by
  have ht:= congr_arg (fun x:Offer t=> (x.val i).val) h; change A.a i-B.a i+(A.a i*f.val.val-f.val.val*B.a i)=0 at ht; rw [mul_add,add_mul,one_mul,mul_one]; apply sub_eq_zero.mp; refine Eq.trans ?_ ht; abel
end Party
end Wardrobe
section Iso
variable [Fintype H] [FiniteDimensional ℝ W] {t:Wardrobe h W}
open Wardrobe Party
-- submodule speed again
private lemma sub_speed {Y:Type*} [AddCommGroup Y] [Module ℝ Y] [Module.Finite ℝ Y] (V: Submodule ℝ Y) (x:U→V) (v:V) (p:Dips ℝ l (fun k=>(x k).val) v.val): Dips ℝ l x v:= (ringed (f:=fun k=> V.subtype) (L:=V.subtype) (p:=l) (fun i=>Sailing.fixed (V.subtype i)) V.subtype_injective).2 x v p

private instance : Module.Finite ℝ G:= @FiniteDimensional.finiteDimensional_submodule ℝ _ _ _ _ _ _
local instance ownD (t:Wardrobe h W) : AddCommGroup ↥t.P:=@Submodule.addCommGroup ℝ W _ _ _ _
local instance ownC (t: Wardrobe h W):AddCommGroup (Bile ↥t.P):= inferInstanceAs (AddCommGroup (G →ₗ[ℝ] G →ₗ[ℝ] ↥t.P))
local instance iPa (t: Wardrobe h W): AddCommGroup ↥(Offer t):=@Submodule.addCommGroup ℝ _ _ _ _ (Offer t)
local instance iW (t: Wardrobe h W): AddCommGroup ↥(fixed t.hall):=@Submodule.addCommGroup ℝ _ _ _ _ (fixed t.hall)
private instance : AddCommGroup (C2 t.P):= @Submodule.addCommGroup ℝ (Bile t.P) _ _ _ (opposite ↥t.P)
private instance : Module.Finite ℝ (C2 t.P):= @FiniteDimensional.finiteDimensional_submodule ℝ _ _ _ _ _ (opposite ↥t.P)

lemma pitch (A:U→Party t) (B:Party t) (p:∀ i, Dips ℝ l (fun k=> (A k).a i) (B.a i)) (b:Dome (boy B.a)) : ∃ f:U→fixed t.hall,Dips ℝ l f 0 ∧ ∀ᶠ k in l,(A k).M B (f k) =0:= by
  let Q:=LinearMap.range (B.pulse B)
  obtain ⟨R,hR⟩:= Submodule.exists_isCompl Q
  let F:=Q.projectionOnto R hR
  have h i x:Dips ℝ l (fun k=> (A k).via B i x) (B.via B i x):=by
    apply sub_speed t.P; simp only [via_v]
    exact dif (maps (p i) ((LinearMap.mul ℝ W).flip _)) (Sailing.fixed _)
  have hu (x:fixed t.hall): Dips ℝ l (fun k=>(A k).pulse B x) (B.pulse B x):= by apply sub_speed (Offer t); exact dotted (fun i=> h i x.val)
  have Hv:Dips ℝ l (fun k=>(A k).rage B) 0:= by
    apply sub_speed (Offer t); refine dotted (fun i=>?_); apply sub_speed t.P
    have ht:= dif (p i) (Sailing.fixed (B.a i) (p:=l) (F:=ℝ)); rw [sub_self] at ht; exact ht
  have hp x: F (B.pulse B x)= (B.pulse B).rangeRestrict x:= by
    change Q.projectionOnto R hR (Q.subtype ((B.pulse B).rangeRestrict x))=_; rw [Submodule.subtype_apply,Submodule.projectionOnto_apply_left]
  have hh : Dips ℝ l (fun k=> F ((A k).rage B)) 0:= by rw [← F.map_zero]; exact maps Hv F
  obtain ⟨φ,u,g⟩:= realization l (B.pulse B).rangeRestrict (fun k=>F ∘ₗ ((A k).pulse B)) 0 (fun _=>0) _ ((B.pulse B).surjective_rangeRestrict) (fun x=>by rw [← hp]; exact maps (hu x) F) (fun i j=> Sailing.fixed 0) hh
  let Z (S:Tour t.P): R→ₗ[ℝ] C2 t.P:= lone S ∘ₗ (Offer t).subtype ∘ₗ R.subtype
  have ht : Injective (Z (B.via B)):= by
    have hb := Dome.pull b t.P.subtype t.P.subtype_injective (B.via B) (fun _ _=>rfl)
    apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr
    intro x o; obtain ⟨v,V⟩:= equiv₁ (B.postal B) (B.stood B) hb (x.val:Offer t) o
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp hR.disjoint) _ ⟨v,Subtype.ext V⟩ x.property
  have v x:Dips ℝ l (fun k=>Z ((A k).via B) x) (Z (B.via B) x):= by
    apply sub_speed (opposite ↥t.P)
    let f:Offer t:= (x:R).val
    refine dotted fun i=> dotted fun j=> ?_; change Dips ℝ l (fun k=> (A k |>.via B i (f.val j))-((A k).via B j (f.val i))-f.val (bracket i j)) ((B.via B i _)-(B.via B j _)-f.val (bracket i j)); exact dif (dif (h _ _) (h _ _)) (Sailing.fixed _)
  refine ⟨φ,u,?_⟩; filter_upwards [g,(ringed v ht).1] with k o w
  let t':=(A k).M B (φ k)
  change F ((A k).rage B)+ F (_)+ 0=0 at o
  rw [add_zero] at o
  have e:t'∈R:=(Submodule.projectionOnto_apply_eq_zero_iff hR).mp ((F.map_add ..).trans o)
  suffices T : (⟨t',e⟩:R)=0 from congr_arg Subtype.val T
  apply w; rw [map_zero]; exact tilt (A k) B _
end Iso
end YM.GaugeFieldConstruction.Apit
