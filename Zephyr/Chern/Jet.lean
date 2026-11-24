import Zephyr.Chern.Coats
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice 


variable {ι:Type*} [Fintype ι]

/-- our chosen bivector contraction on axis pair. -/
def bow {V:Type*} [AddCommGroup V] (f:Axis→Axis→V) := f 0 1-f 1 0+(f 2 3-f 3 2)

def crossB (p q:Coats ι) := bow fun a b=> Δ a p * Δ b q

def firstTwist (p z:Coats ι) := z * crossB p p

def curly (p:Coats ι) : Coats ι := bow fun a b=> crossB (Δ a p) (Δ b p)

/-- second coefficient correction to product, excluding first jets multiplied directly -/
def secondTwist (p r z:Coats ι) :=
   z*(crossB p r+crossB r p) + (2:ℂ)⁻¹ • ((z*z)* curly p)

structure Jet (p r s z:Coats ι) : Prop where
  zero : p=p*p
  one : r=p*r+r*p + firstTwist p z
  two : s=p*s+s*p+r*r+secondTwist p r z

variable [DecidableEq ι]

def mirror (p : Coats ι) := 1-(p+p)

private lemma perfect {p : Coats ι} (h:p=p*p) : mirror p * mirror p = 1 := by
  unfold mirror
  simp only [sub_mul,one_mul,mul_sub,mul_one,add_mul,mul_add,←h]; abel

private lemma wings {p r b : Coats ι} (h : r=p*r+r*p+b) :
    mirror p*r+r*mirror p=b+b := by
  unfold mirror
  rw [sub_mul,mul_sub,one_mul,mul_one,add_mul,mul_add]
  nth_rewrite 1 4 [h]
  abel

private lemma sandwich {M t b : Coats ι}
    (j : M*M=1)
    (h : M*t+t*M=b+b) :
    gross (M*b)=gross t ∧
    gross (t*b)=gross (M*(t*t)) ∧
    gross (M*(b*b))=gross (t*b) := by
  have dup {x y:ℂ} (h : x+x=y+y) : x=y := by rw [←two_mul,←two_mul] at h;exact mul_left_cancel₀ two_ne_zero h
  have v2:=congrArg (fun X=>gross (X*t)) h
  simp only [add_mul,map_add] at v2
  rw [mul_assoc M,gross_rot _ t,←mul_assoc t,gross_rot (t*t)] at v2
  have v: gross (t*b)=gross (M*(t*t)):= by
    rw [gross_rot t]; exact dup (by exact v2.symm)
  refine ⟨?_,v,?_⟩
  · have e:=congrArg (fun X=>gross (M*X)) h
    simp only [mul_add,map_add] at e
    rw [←mul_assoc M M,j,one_mul, gross_rot M (t*M),mul_assoc t,j,mul_one] at e
    exact dup e.symm
  have e := congrArg (fun X=>gross (M* (X*X))) h
  simp only [add_mul,mul_add,map_add] at e
  rw [v]

  have az : gross (t*(M*t))=gross (M*(t*t)) := by rw [gross_rot t,mul_assoc]
  have ay : gross (t*(t*M))=gross (M*(t*t)) := by rw [←mul_assoc,gross_rot]
  have ax : gross (M*(t*M*(M*t)))=gross (M*(t*t)) := by rw [← mul_assoc (t*M),mul_assoc t M,j,mul_one]
  have aw : gross (M*(t*M*(t*M)))=gross (M*(t*t)) := by
    rw [gross_rot M, mul_assoc, mul_assoc t M M, j,mul_one,mul_assoc,az]

  have av (x) : gross (M*(M*t*x))=gross (t*x) := by rw [mul_assoc M t, ←mul_assoc M M,j,one_mul]
  rw [ax,aw,av,av,az,ay] at e
  exact dup (dup e.symm)

omit [DecidableEq ι] in
private lemma wing_price (M p r:Coats ι) (a b:Axis) :
    gross (M*(Δ a r * Δ b p)) = -gross (Δ a M * r * Δ b p) -
      gross (M*r*Δ a (Δ b p)) := by
  have h:=Δ_gross a (M*r * Δ b p)
  rw [Δ_mul,Δ_mul,add_mul, map_add,map_add] at h
  rw [←mul_assoc]
  linear_combination h

omit [DecidableEq ι] in
private lemma wing_price' (M p r:Coats ι) (a b:Axis) :
    gross (M*(Δ a p * Δ b r)) = -gross (Δ b M * Δ a p * r) -
      gross (M*Δ b (Δ a p)*r) := by
  rw [←mul_assoc,ibp,Δ_mul,add_mul,map_add]
  abel

def badgeB (p r:Coats ι) (a b:Axis) :=
  Δ a p * Δ b r - Δ b p * Δ a r

lemma Δ_badge (p z:Coats ι) (e : ∀ a, Δ a z=0) (a) :
    Δ a (mirror p * z)= -(Δ a p*z + Δ a p*z) := by
  simp only [mirror,Δ_mul,map_sub,Δ_one,map_add,e,mul_zero,add_zero,zero_sub,neg_mul,add_mul]

variable (p r z:Coats ι) (e : ∀ a, Δ a z=0)
    (m : ∀ a, Δ a p*z=z*Δ a p)
include e m

private lemma wing_pair (a b:Axis) :
    gross (mirror p*z * (badgeB p r a b+badgeB r p a b)) =
      -4*gross (r*(z*badgeB p p a b)) := by
  have h (i j) :
      gross (z * Δ i p * r * Δ j p)=gross (z * Δ j p * Δ i p * r) := by
    rw [gross_rot, ←mul_assoc,←mul_assoc,m]
  unfold badgeB
  rw [mul_add,mul_sub,mul_sub,map_add,map_sub,map_sub,wing_price',wing_price',wing_price,
    wing_price,Δ_symm a b p]
  simp only [Δ_badge p z e, neg_mul,add_mul,m,map_neg,map_add,h a b,h b a]
  rw [gross_rot r,mul_sub,sub_mul,map_sub]
  simp only [←mul_assoc]
  ring

private lemma wing_bow :
    gross (mirror p*(z*(crossB p r+crossB r p))) = -4*gross (r*firstTwist p z) := by
  change gross (mirror p*(z*(badgeB p r 0 1+badgeB p r 2 3+(badgeB r p 0 1+badgeB r p 2 3)))) =
    -4*gross (r*(z*(badgeB p p 0 1+badgeB p p 2 3)))
  rw [add_add_add_comm,←mul_assoc,mul_add,map_add,
    wing_pair p r z e m,wing_pair p r z e m,mul_add z,mul_add,map_add,mul_add]

omit e m in
theorem Jet.response {p r s z: Coats ι} (h:Jet p r s z)
    (e : ∀ a, Δ a z=0) (m : ∀ a, Δ a p*z=z*Δ a p) :
    gross s= -3 * gross (mirror p*(firstTwist p z*firstTwist p z))+
      (2:ℂ)⁻¹ * gross (mirror p*((z*z)*curly p)) := by
  have h0:= perfect h.zero
  have h1:=sandwich h0 (wings h.one)
  have ht:=h.two
  rw [add_assoc (_+_) ] at ht
  have h2:=(sandwich h0 (wings ht)).1
  rw [←h2, secondTwist,mul_add,mul_add (mirror p),map_add,map_add,h1.2.1.symm,wing_bow p r z e m,
    h1.2.2, Matrix.mul_smul, map_smul,smul_eq_mul]
  ring
