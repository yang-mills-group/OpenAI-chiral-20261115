import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Analysis.Complex.Basic
/-!
# Finitely many resolutions, linear read interfaces

Generic multilinear assembly. We VIEW inside the PiTensorProduct to obtain a single algebra,
actually working throughout JUST on the finite-level cylinders (and proving in particular that
natural equalities in this presentation don't erase any budget or compatibility there).
Use `wing` or gauge-invariant per-level algebra for restrictions; copies of the element `1` at
any level use nothing.
-/
noncomputable section
namespace YM.CF.Buffered.Concord.Style
set_option autoImplicit false
open Function Filter Finset
open PiTensorProduct
open scoped BigOperators ComplexOrder Topology Classical TensorProduct
variable {A:Type*} [CommRing A][Algebra ℂ A] {a b n k:ℕ}

abbrev Surface (A:Type*)[CommRing A][Algebra ℂ A] := ⨂[ℂ] (_:ℕ), A

def fits (n:ℕ)(f:ℕ→A):Prop:= ∀ k>n,f k=1

def passing (f:ℕ→A) := ∃ n,fits n f

lemma fits_one : fits n (1:ℕ→A) := fun _ _=> rfl
lemma fits_later {f:ℕ→A}(p:fits n f)(t:n≤b): fits b f:= fun k v=> p k (lt_of_le_of_lt t v)
lemma fits_times {f g:ℕ→A}(p:fits n f)(t:fits n g): fits n (f*g) := by intro i h; rw [Pi.mul_apply,p i h,t i h,one_mul]
lemma passing_times {f g:ℕ→ A}(p:passing f)(t:passing g): passing (f*g) := ⟨max p.choose t.choose, fits_times (fits_later p.choose_spec (le_max_left ..)) (fits_later t.choose_spec (le_max_right ..))⟩

-- use diagrams with any multiplicative restriction, e.g. singlets, halfs and support
abbrev SurfaceRule (A:Type*)[CommRing A][Algebra ℂ A] := Submonoid (ℕ→A)

def pepper (n:ℕ)(R:SurfaceRule A): SurfaceRule A where
  carrier := {f| f∈ R ∧ fits n f}
  mul_mem' := fun p t=> ⟨R.mul_mem p.1 t.1, fits_times p.2 t.2⟩
  one_mem' := ⟨R.one_mem,fits_one⟩
def pub (R:SurfaceRule A): SurfaceRule A where
  carrier := {f| f∈ R ∧ passing f}
  mul_mem' := fun p t=> ⟨R.mul_mem p.1 t.1, passing_times p.2 t.2⟩
  one_mem':= ⟨R.one_mem, 0,fits_one⟩

def pressed (R:SurfaceRule A):Subalgebra ℂ (Surface A) := by
 let P:=Submodule.span ℂ (PiTensorProduct.tprod (s:=fun _ :ℕ=>A) ℂ '' (R:Set (ℕ→A)))
 have he : (1:Surface A)∈ P:= Submodule.subset_span ⟨1,R.one_mem,rfl⟩
 refine {
    carrier:=P
    add_mem':=fun p t=> P.add_mem p t
    algebraMap_mem' a:=?_
    mul_mem':=?_ }
 swap
 · rw [Algebra.algebraMap_eq_smul_one]; exact P.smul_mem a he
 intro x y (p:x∈P) (t:y∈P)
 refine Submodule.span_induction (p:=fun z _=> z*y∈P) (fun z e=> ?_) (by rw [zero_mul]; exact P.zero_mem)
   (fun z v _ _ f g=>by rw [add_mul]; exact P.add_mem f g) (fun a z _ f=> by rw [Algebra.smul_mul_assoc]; exact P.smul_mem a f) p
 obtain ⟨g,f,rfl⟩:=e; refine Submodule.span_induction (p:=fun z _=> tprod ℂ g*z∈P) (fun z e=>?_) (by rw [mul_zero]; exact P.zero_mem) (fun z v _ _ f h=>by rw [mul_add]; exact P.add_mem f h) (fun a z _ f=> by rw [Algebra.mul_smul_comm]; exact P.smul_mem a f) t
 obtain ⟨v,h,rfl⟩:=e; rw [tprod_mul_tprod]; exact Submodule.subset_span ⟨g*v, R.mul_mem f h,rfl⟩

lemma pressed_m (R:SurfaceRule A) (x:Surface A) : x∈pressed R ↔ x∈ Submodule.span ℂ (PiTensorProduct.tprod (s:=fun _:ℕ=>A) ℂ '' (R:Set (ℕ→A))) := Iff.rfl
lemma pressedIn {R:SurfaceRule A}{f:ℕ→A}(p:f∈R) : PiTensorProduct.tprod ℂ f ∈ pressed R:= (pressed_m ..).2 (Submodule.subset_span ⟨_,p,rfl⟩)
lemma muscle {R T:SurfaceRule A}(p:R ≤ T) : pressed R≤ pressed T:=fun x h=> (pressed_m ..).2 (Submodule.span_mono (Set.image_mono p) ((pressed_m ..).1 h))
lemma to_pub (R:SurfaceRule A)(n:ℕ) : pressed (pepper n R) ≤ pressed (pub R):= muscle (fun _ t=> ⟨t.1,n,t.2⟩)
lemma to_pepper (R:SurfaceRule A){n m:ℕ}(h:n≤m) : pressed (pepper n R) ≤ pressed (pepper m R):=muscle (fun _ t=>⟨t.1,fits_later t.2 h⟩)

@[elab_as_elim]
theorem display {R:SurfaceRule A}{P: Surface A → Prop}(p : ∀ f∈R,P (PiTensorProduct.tprod ℂ f))(z:P 0)
    (h:∀ x y,x∈pressed R → y∈pressed R → P x→ P y→ P (x+y))(v:∀ (a:ℂ) x,x∈pressed R → P x→ P (a • x)) {x:Surface A}(t:x∈pressed R): P x := by
  refine Submodule.span_induction (p:=fun z _=> P z) (fun _ x=>?_) z (fun x y a b=> h x y ((pressed_m ..).2 a) ((pressed_m ..).2 b)) (fun a x d=> v a x ((pressed_m ..).2 d)) ((pressed_m ..).1 t)
  obtain ⟨x,d,rfl⟩:=x; exact p _ d
lemma by_stages (R:SurfaceRule A) (x:Surface A)(h:x∈ pressed (pub R)): ∃ n,x∈ pressed (pepper n R):=by
  refine display (P:=fun x=> ∃ n,x∈pressed (pepper n R)) ?_ ?_ ?_ ?_ h
  · intro f hf; obtain ⟨q,n,v⟩:=hf; exact ⟨n,pressedIn (show f∈ pepper n R from ⟨q,v⟩)⟩
  · exact ⟨0,(pressed _).zero_mem⟩
  swap; · intro a x p h; obtain ⟨n,h⟩:=h; exact ⟨n,(pressed _).smul_mem h a⟩ -- order?
  intro x y _ _ a b; obtain ⟨n,h⟩:=a; obtain ⟨m,k⟩:= b; exact ⟨max n m,(pressed _).add_mem (to_pepper R (le_max_left ..) h) (to_pepper R (le_max_right ..) k)⟩

-- reflection for tensor products on these spaces
variable (g:ℕ→ A →ₗ⋆[ℂ] A)
def rotating (f:ℕ→A) := fun n=> g n (f n)
private lemma rotational [DecidableEq ℕ] (f:ℕ→A)(i:ℕ)(x:A): rotating g (update f i x)=update (rotating g f) i (g i x):= by funext j; by_cases h:j=i<;> simp [rotating, h, update_of_ne]

private def pivotPanel : Surface A →+ Surface A := liftAddHom (fun (p:ℂ×(ℕ→A))=> tprodCoeff ℂ (star p.1) (rotating g p.2))
   (by intro r x i t; exact zero_tprodCoeff' _ _ i (show g i (x i)=0 by rw [t,map_zero]))
   (by intro p; change tprodCoeff ℂ (star 0) _=_; rw [star_zero, zero_tprodCoeff])
   (by intro h r x i a b; dsimp only; rw [rotational, rotational, rotational,map_add, add_tprodCoeff])
   (by intro r a u; dsimp only; rw [star_add, add_tprodCoeff'])
   (by intro h r x i a; dsimp only; rw [rotational, map_smulₛₗ (f:=g i), starRingEnd_apply, show g i (x i)=rotating g x i from rfl,smul_tprodCoeff_aux, star_mul'])

private lemma cameo (x:ℕ→A)(z:ℂ) : pivotPanel g (tprodCoeff ℂ z x)=tprodCoeff ℂ (star z) (rotating g x):= rfl

def inversion : Surface A→ₗ⋆[ℂ] Surface A where
  toFun := pivotPanel g
  map_add':= map_add _
  map_smul' z x:= by
    induction x using PiTensorProduct.induction_on' with
    | add u v p a=>rw [_root_.smul_add,map_add,map_add,p,a, _root_.smul_add]
    | tprodCoeff a f=> change pivotPanel g (z • tprodCoeff ℂ a f)=star z • pivotPanel g (tprodCoeff ℂ a f); rw [cameo g f a,smul_tprodCoeff',smul_tprodCoeff',cameo,smul_eq_mul,smul_eq_mul,star_mul']

lemma inv_at (x:ℕ→ A): inversion g (tprod ℂ x)=tprod ℂ (rotating g x):=by
  change pivotPanel g (tprod ℂ x)=_; simp_rw [tprod_eq_tprodCoeff_one, cameo,star_one]

lemma inv_mul (w:∀ i (x y:A),g i (x*y)=g i x*g i y)(x y:Surface A) : inversion g (x*y)=inversion g x*inversion g y:=by
  induction x using PiTensorProduct.induction_on' with
  | add _ _ p v=> rw [add_mul,map_add,map_add,p,v,add_mul]
  | tprodCoeff a x=>
    induction y using PiTensorProduct.induction_on' with
    | add _ _ p v=> rw [mul_add,map_add,map_add,p,v,mul_add]
    | tprodCoeff b y=>
      simp only [tprodCoeff_eq_smul_tprod,smul_tprod_mul_smul_tprod,map_smulₛₗ,inv_at, map_mul]; unfold rotating; simp only [Pi.mul_apply,w, Pi.mul_def]
lemma inv_one (w:∀ i,g i 1=1) : inversion g 1=1:=by rw [one_def (R:=ℂ)]; rw [inv_at, show rotating g 1=1 from funext w]
lemma inv_inv (p:∀ i, Involutive (g i)) : Involutive (inversion g) := by
  intro x; induction x using PiTensorProduct.induction_on' with
  | add _ _ p v=> rw [map_add,map_add,p,v]
  | tprodCoeff a x=> simp_rw [tprodCoeff_eq_smul_tprod,map_smulₛₗ (f:=inversion g),inv_at,starRingEnd_apply,star_star,show rotating g (rotating g x)=x from funext fun i=> p i (x i)]
lemma inv_room {P Q: SurfaceRule A}(h:Set.MapsTo (rotating g) P Q){x}(p:x∈pressed P): inversion g x∈ pressed Q:=by
  refine display (P:=fun x=> inversion g x ∈ pressed Q) ?_ ?_ ?_ ?_ p
  · intro f e; rw [inv_at]; exact pressedIn (h e)
  · rw [map_zero]; exact (pressed _).zero_mem
  · intro a b _ _ p q; rw [map_add]; exact (pressed Q).add_mem p q
  intro a b _ p; rw [map_smulₛₗ]; exact (pressed _).smul_mem p _
end YM.CF.Buffered.Concord.Style
