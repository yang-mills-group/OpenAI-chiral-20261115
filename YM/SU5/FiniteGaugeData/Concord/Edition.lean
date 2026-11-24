import YM.SU5.FiniteGaugeData.Concord.Splice
/-!
# Cylinder assembly reading

abstract constructors for evaluating in different modules at each level, e.g. native torus for
that period, but still on this algebra with genuine products (not just secants/pairing).
Later proofs rely on exact-reading/qualification for such predications, the linearity etc.
of the underlying readings must first be afforded (no bake assumption here).
-/
noncomputable section
namespace YM.CF.Buffered.Concord.Style
set_option autoImplicit false
open Function Filter Finset PiTensorProduct
open scoped ComplexOrder BigOperators Topology Classical TensorProduct
variable {A: Type*} [CommRing A][Algebra ℂ A]
variable {n k m:ℕ}(E : ℕ→ A →ₗ[ℂ] ℂ)(q : ∀ j,E j 1=1)

namespace Skirt
variable {B C:Type*}[AddCommGroup B][Module ℂ B][AddCommGroup C][Module ℂ C](f:A→ₗ[ℂ] B)(P:Skirt A B n)

def lower : Skirt A B 0 where
  soc x:= f (x 0)
  depends h := congrArg f (h 0 le_rfl)
  add x i a p q:=by obtain rfl:= Nat.eq_zero_of_le_zero a; simp only [update_self, map_add]
  smul x i a p q:=by obtain rfl:= Nat.eq_zero_of_le_zero a; simp only [update_self, map_smul]

private lemma bills (P:Skirt A B n)(x:ℕ→A)(a:A): P.soc (update x (n+1) a)=P.soc x:= P.depends (fun i p=> update_of_ne (by omega:i≠n+1) ..)

def upward (L:B→ₗ[ℂ]A→ₗ[ℂ] C) : Skirt A C (n+1) where
  soc x:=L (P.soc x) (x (n+1))
  depends {x y} h:=by rw [P.depends (s:=x) (t:=y) (fun i p=> h i (by omega)),h (n+1) le_rfl]
  add x i p a b:= by
    by_cases h:i=n+1; swap
    · have he:i ≤ n:=by omega
      rw [P.add _ i he,map_add]; simp only [update_of_ne (Ne.symm h),LinearMap.add_apply]
    subst i; simp only [bills, update_self,map_add]
  smul x i p a c:=by
    by_cases h:i=n+1; swap
    · have he:i ≤ n:=by omega
      rw [P.smul _ i he,map_smul]; simp only [update_of_ne (Ne.symm h),LinearMap.smul_apply]
    subst i; simp only [bills,update_self,map_smul]
end Skirt

variable (C:ℕ→Type*)[∀i, Ring (C i)][∀i,Algebra ℂ (C i)]
variable (T:∀ i,A→ₗ[ℂ] C i)(L:∀ i,C i→ₗ[ℂ] C (i+1))
/-- multiply by occupants *after* transmitting the entire previous product. -/
def prefixTube : (k:ℕ)→ Skirt A (C k) k
 | 0=> Skirt.lower (T 0)
 | k+1=> (prefixTube k).upward (LinearMap.mk₂ ℂ (fun x y=> L k x * T (k+1) y) (fun _ _ _=>by rw [map_add, add_mul]) (fun _ _ _=>by rw [map_smul,Algebra.smul_mul_assoc]) (fun _ _ _=>by rw [map_add,mul_add]) (fun _ _ _=>by rw [map_smul,Algebra.mul_smul_comm]))

def bill (n:ℕ) := (prefixTube C T L n).hardcover E q

lemma opens {f:ℕ→A} (n:ℕ)(p:fits n f) : bill E q C T L n (tprod ℂ f)=(prefixTube C T L n).soc f:= Skirt.hardcover_app E q (prefixTube C T L n) f p -- tune
lemma curtained (f:ℕ→A) : (prefixTube C T L 0).soc f=T 0 (f 0) := rfl
lemma vystep (f:ℕ→A)(k:ℕ): (prefixTube C T L (k+1)).soc f=L k ((prefixTube C T L k).soc f)*T (k+1) (f (k+1)):= rfl

-- correlation ends at highest step (NOT its successor's evaluation of geometrical product)
def atLeast (n:ℕ) : Subalgebra ℂ (Surface A) := pressed (pepper n ⊤)
variable {n : ℕ}
lemma vRun {x:Surface A} (p:x∈atLeast (A:=A) n)(h:T (n+1) 1=1): bill E q C T L (n+1) x = L n (bill E q C T L n x):=by
  refine display (P:=fun x=> bill E q C T L (n+1) x = L n (bill E q C T L n x)) ?_ ?_ ?_ ?_ (show x∈pressed _ from p)
  · intro f (t : f ∈ pepper n ⊤); obtain ⟨_,t⟩ := t
    rw [opens E q C T L n t, opens E q C T L _ (fits_later t (by omega)),vystep, t (n+1) (lt_add_one n),h,mul_one] -- typo add
  · rw [map_zero,map_zero,map_zero]
  · intro x y _ _ a b; rw [map_add,map_add,map_add,a,b]
  intro a x _ b; rw [map_smul,map_smul,map_smul,b]

-- single-factor inclusions are MONIC. In applications also gives the true reading at every such spot.

def stepFactor (a:ℕ) : A→ₐ[ℂ] Surface A := singleAlgHom (A:=fun (_:ℕ)=>A) a
lemma insert_at (a:ℕ)(x:A): stepFactor a x=tprod ℂ (update (1:ℕ→A) a x):= rfl
lemma visible (a:ℕ)(x:A): fits a (update (1:ℕ→A) a x):= fun b p=> update_of_ne (ne_of_gt p) ..
lemma stepAt (a:ℕ)(x:A) : stepFactor a x∈ atLeast a:= pressedIn (show update (1:ℕ→A) a x∈ pepper a ⊤ from ⟨Submonoid.mem_top _,visible a x⟩)

variable (ht:∀ i,T i 1=1)(hl:∀ i,L i 1=1)
include ht hl
lemma prefix_nat (u:ℕ) : (prefixTube C T L u).soc 1=1:=by induction u with | zero=> exact ht 0| succ i ih=> rw [vystep,ih, hl, Pi.one_apply,ht,mul_one]
lemma inclusion (a:ℕ)(x:A) : bill E q C T L a (stepFactor a x)=T a x:=by
  rw [insert_at, opens E q C T L a (visible a x)]
  obtain _ | a:=a; swap
  · let u:ℕ→A:=update (1:ℕ→A) (a+1) x; have he:(prefixTube C T L a).soc u=1:= ((prefixTube C T L a).depends (t:=1) (fun i p=> update_of_ne (by omega) ..)).trans (prefix_nat C T L ht hl a)
    rw [vystep,he,update_self,hl,one_mul]
  rw [curtained,update_self]

omit ht hl
include q
lemma factor_inj : Injective (stepFactor (A:=A) n) := by
  intro x y v
  let Z := fun _:ℕ=>A; let f:= fun _:ℕ=> (LinearMap.id (R:=ℂ) (M:=A)); let g:= bill E q Z f f n
  exact calc x=g (stepFactor n x):= (inclusion E q Z f f (fun _=>rfl) (fun _=>rfl) n x).symm
             _=g (stepFactor n y):= congrArg g v
             _=y:=inclusion E q Z f f (fun _=>rfl) (fun _=>rfl) n y
end YM.CF.Buffered.Concord.Style
