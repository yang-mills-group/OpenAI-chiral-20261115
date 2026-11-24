import GaugeFieldConstruction.Xenon

/-!
# Equivariant H1 H2 vanish. Use later for lift and the conjugacy (within filtered End constraints).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Function Module Set
open scoped BigOperators
variable {X Z: Type*} [AddCommGroup X] [Module ℝ X] {S : Tour X}

section White
variable [Module.Finite ℝ X]
variable (P:Stood S) (K : Dome S)
include P
lemma furnace (i x) : (mac K).symm (S i x)=S i ((mac K).symm x):=by
  apply (mac K).injective; rw [(mac K).apply_symm_apply,mac_p K P,(mac K).apply_symm_apply] -- include
lemma note (i x): oct K (S i x)=S i (oct K x):=by rw [no_oct K P,ker_price K _ (oct_mem K x)]
include P K
lemma white₂ (x : C2 X) (u:Cycle S x):x∈LinearMap.range (lone S):=by
  let k:=hooked (mac K).symm.toLinearMap x
  have p: Cycle S k:= Cycle.map u (fun i x=> furnace P K i x)
  let A:=hooked (oct K) k
  have o: Cycle S A:= Cycle.map p (fun i x=> note P K i x)
  have i: A∈ LinearMap.range (lone S) := ideals _ o (fun i a b=>by change S i (oct K _)=0; exact ker_price K _ (oct_mem K _) i)
  have h: hooked (mtx S) k∈ LinearMap.range (lone S):= ⟨_,(cartan P k p).symm⟩
  have e:hooked (mtx S) k+A=x:=by
    apply Subtype.ext; ext1 i; ext1 j
    exact (mac K).apply_symm_apply _ -- change
  rw [← e]; exact Submodule.add_mem _ h i
lemma white₁ (g:C1 X) (v:lone S g=0): ∃ x:X,S.flip x=g:=by
  let r:= (mac K).symm.toLinearMap ∘ₗ g
  have ht:lone S r=0:=by
    unfold r; rw [bothD g _ (fun i x=> furnace P K i x),v]; apply Subtype.ext; ext1 i; ext1 j; exact (mac K).symm.map_zero
  have he:lone S ((oct K) ∘ₗ r)=0:= by rw [bothD r (oct K) (note P K),ht]; apply Subtype.ext; ext1 i; ext1 j; exact (oct K).map_zero
  have hj:=quiet1 ((oct K) ∘ₗ r) he (fun i q=>ker_price K (oct K (r q)) (oct_mem K _) i)
  refine ⟨∑ k:Tape,S (wall k) (r (wall k)), LinearMap.ext (fun i=>?_ )⟩
  change S i (∑ k:Tape,S (wall k) (r (wall k)))=_
  rw [← blemish P r ht]
  have hv : oct K (r i)=0:= LinearMap.congr_fun hj i
  have h: vista K (r i)=g i := (mac K).apply_symm_apply _; rw [vista,LinearMap.add_apply,hv,add_zero] at h; exact h
end White

section Group
variable {H:Type*} [Group H]
/-- Use matrices's equivalent MonoidHom, End. -/
structure Helm (H:Type*) [Group H] where
  A : H→*Endr G
  joins (g) (x y): A g (bracket x y)=bracket (A g x) (A g y)
structure Item (h: Helm H) (S:Tour X) where
  Z : H→* Endr X
  marks i u g : S (h.A g i) (Z g u)=Z g (S i u)
lemma again (P : H→*Endr X) (h:H) (x:X): P h (P h⁻¹ x)=x := by rw [← Module.End.mul_apply,← map_mul, mul_inv_cancel,map_one]; rfl
lemma again' (P : H→*Endr X) (h:H) (x:X): P h⁻¹ (P h x)=x:=by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,map_one]; rfl

def fixed (P:H→*Endr X) : Submodule ℝ X where
  carrier:={v|∀ i, P i v=v}
  add_mem' h u:= fun i=> by rw [map_add,h i,u i]
  smul_mem' c x u:=fun i=> by rw [map_smul,u i]
  zero_mem':= fun _=>map_zero _

def gr₁ (h: Helm H) (S:H→*Endr X) : H→*Endr (C1 X) where
  toFun v := ((LinearMap.llcomp ℝ G X X) (S v)) ∘ₗ ((LinearMap.llcomp ℝ G G X).flip (h.A v⁻¹))
  map_one':= by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro i
    change S 1 (x (h.A _ i))=x i; rw [inv_one,map_one,map_one]; rfl
  map_mul' a b:= by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro i
    change S (a*b) (x (h.A (a*b)⁻¹ i))=S a (S b (x (h.A b⁻¹ (h.A a⁻¹ i)))); rw [mul_inv_rev,map_mul,map_mul]; rfl

def qprog (h:Helm H) (P:H→*Endr X) (f:C2 X) (g:H): C2 X:= ⟨(f.val.compl₁₂ (h.A g⁻¹) (h.A g⁻¹)).compr₂ (P g), fun i j=>by change P g (f.val _ _)+P g (f.val _ _)=_; rw [← map_add,f.property _ _,map_zero]⟩
def gr₂ (h:Helm H) (P:H→*Endr X): H →* Endr (C2 X) where
  toFun g:={ toFun x:=qprog h P x g
             map_add' x y:=Subtype.ext (LinearMap.ext fun i=>LinearMap.ext fun j=>map_add (P g) (x.val _ _) (y.val _ _))
             map_smul' r x:=Subtype.ext (LinearMap.ext fun i=>LinearMap.ext fun j=> map_smul (P g) r (x.val _ _)) }
  map_one':= by
    apply LinearMap.ext; intro p; apply Subtype.ext; ext1 i; ext1 j; change P 1 (p.val (h.A _ i) (h.A _ j))=p.val i j; rw [inv_one,map_one,map_one]; rfl
  map_mul' a b:= by
    apply LinearMap.ext; intro p; apply Subtype.ext; ext1 i; ext1 j; change P (a*b) (p.val (h.A (a*b)⁻¹ i) (h.A (a*b)⁻¹ j))=P a (P b _); rw [mul_inv_rev,map_mul,map_mul]; rfl
variable {h:Helm H}
lemma fix₁ {P:H→*Endr X} (c:C1 X): c∈ fixed (gr₁ h P) ↔ ∀ g x,P g (c x) = c (h.A g x):=by
  constructor
  · intro p g x
    have H:=LinearMap.congr_fun (show gr₁ h P g c=c from p g) (h.A g x); change P g (c _) =_ at H; rw [again' h.A] at H; exact H
  intro v g; apply LinearMap.ext; intro x; change P _ (c (h.A g⁻¹ x))=_; rw [v,again]
lemma fix₂ {P:H→*Endr X} (c:C2 X):c∈ fixed (gr₂ h P)↔ ∀ g x y,P g (c.val x y)=c.val (h.A g x) (h.A g y):=by
  constructor
  · intro p g x y
    have H:= LinearMap.congr_fun (LinearMap.congr_fun (congr_arg Subtype.val (show gr₂ h P g c=c from p g)) (h.A g x)) (h.A g y); change P g (c.val _ _) = _ at H; rw [again' h.A,again' h.A] at H; exact H
  intro v g; apply Subtype.ext; ext1 x; ext1 y; change P _ (c.val (h.A g⁻¹ x) _)= c.val x y; rw [v,again,again] -- rw maybe
variable (U:Item h S)
lemma sees (p:C1 X) (g : H) : gr₂ h U.Z g (lone S p)=lone S (gr₁ h U.Z g p):=by
  apply Subtype.ext; ext1 i; ext1 j; rw [turn]; change U.Z g ((lone S p).val (h.A g⁻¹ i) (h.A g⁻¹ j))= S i _-S j _-_
  rw [turn,map_sub,map_sub, ← h.joins g⁻¹, ← U.marks, ← U.marks,again,again]; rfl

lemma stock (g:H) (x:X): gr₁ h U.Z g (S.flip x)= S.flip (U.Z g x):=by apply LinearMap.ext; intro i; change U.Z g (S (h.A g⁻¹ i) x)=_; rw [← U.marks,again]; rfl

def delta (U:Item h S): fixed (gr₁ h U.Z) →ₗ[ℝ] fixed (gr₂ h U.Z) := (lone S ∘ₗ (fixed (gr₁ h U.Z)).subtype).codRestrict _ fun c i=>by
  change gr₂ _ _ i (lone _ _)=_; rw [sees U]; change lone S _=lone S c.val; exact congr_arg (lone S) (c.property i)
lemma tame (x : ↥(fixed U.Z)) : S.flip x.val∈ fixed (gr₁ h U.Z):= fun g=> (stock U _ _).trans (congr_arg S.flip (x.property g))

variable [Module.Finite ℝ X] (P:Stood S) (K:Dome S) [Fintype H]
omit [Module.Finite ℝ X] in
lemma adjSum {p : H →* Endr X} (x:X): ∑ i:H,p i x∈ fixed p:= fun j=>by
  rw [map_sum]; simp_rw [← Module.End.mul_apply,← map_mul]; exact Equiv.sum_comp (Equiv.mulLeft j) (fun i=> p i x)

include K P
lemma equiv₂ (c : fixed (gr₂ h U.Z)) (v:Cycle S c.val): c∈ LinearMap.range (delta U):= by
  obtain ⟨a,w⟩:=white₂ P K _ v
  let r:ℝ:= Fintype.card H
  have ht:r≠0:=by unfold r; norm_cast; exact Fintype.card_pos.ne'
  let q:= gr₁ h U.Z
  refine ⟨⟨r⁻¹ • ∑ i:H,q i a,Submodule.smul_mem _ _ (adjSum (p:=q) a)⟩,Subtype.ext ?_⟩
  change lone S (r⁻¹ • _)=_; rw [map_smul,map_sum]; unfold q; simp_rw [← sees U,w,show ∀ i,gr₂ h U.Z i c.val=c.val from c.property]; rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ ht,one_smul]
lemma equiv₁ (f : fixed (gr₁ h U.Z)) (v:lone S f.val=0): ∃ x:fixed U.Z,S.flip x.val=f.val:= by
  obtain ⟨x,hp⟩:=white₁ P K f.val v
  let r:ℝ:=Fintype.card H; have ht:r≠0:=by unfold r; norm_cast; exact Fintype.card_pos.ne'
  refine ⟨⟨r⁻¹ • ∑ i:H,U.Z i x, Submodule.smul_mem _ _ (adjSum (p:=U.Z) x)⟩,?_⟩
  change S.flip (r⁻¹ • _)=_; rw [map_smul,map_sum]; simp_rw [← stock U,hp,show ∀ i,gr₁ h U.Z i f.val=f.val from f.property]; rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ ht,one_smul]
end Group
end YM.GaugeFieldConstruction.Apit
