import YM.SU5.Assay.Panel
import YM.SU5.FiniteGaugeData.Tower.Gallery
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat
open Etch
namespace Weir
-- Variant of (67) for E. Independent mirror flights with arbitrary cover lifts.
def bank (σ:Cover)(W b:ℤ)(i:Axis) := σ i + W*b
def Barn (K:Calibration)(W:ℤ)(σ x:Cover)(S:Finset Cover):Prop:=∀ i,Between K i (bank σ W (x i) i) (bank σ W (x i+1) i) S
section p
variable {K:Calibration}{W:ℤ}{S:Finset Cover}{σ x:Cover}{F f:Family K}
inductive Sloop (K:Calibration)(W:ℤ)(σ x:Cover)(f:Family K):Cover→Family K→Prop
| first:Sloop K W σ x f x f
| rift {y:Cover}{F:Family K}(i:Axis)(b:ℤ)(v:Sloop K W σ x f y F): Sloop K W σ x f (bent i (2*b) y) (mirror K i (bank σ W b i) F)
lemma Barn.rift (h:Barn K W σ x S)(i:Axis)(b:ℤ): Barn K W σ (bent i (2*b) x) (reflectedBox i (bank σ W b i) S):=by
 intro j
 by_cases a:j=i
 · subst j; unfold bent; rw[pet_i]; convert Between.mirror K i (h i) (bank σ W b i) using 1 <;> unfold bank <;> ring
 intro t u
 obtain ⟨y,g,e⟩:=reflect_stays i _ S u; unfold bent; rw [e,if_neg a,pet_j _ a]; exact h j y g
lemma Sloop.granted {y:Cover}(p:InTest K true S false f)(h:Barn K W σ x S)(g:Sloop K W σ x f y F): ∃ T:Finset Cover,InTest K true T false F∧ Barn K W σ y T:=by
 induction g with
 | first=> exact ⟨_,p,h⟩
 | rift i b _ e=> obtain ⟨T,t,v⟩:=e; exact ⟨_,axial K i _ t,v.rift i b⟩
lemma Sloop.toll {A:ℝ}{y:Cover}(u:pay f A)(g:Sloop K W σ x f y F):pay F A:=by
 induction g with
 | first=> exact u
 | rift i b _ e=> exact pay_flips K e i _
end p
section geo
variable {K:Calibration}{m n:Side}{W:ℤ}{σ:Cover}
structure LatticeFare (K:Calibration)(m n:Side)(W:ℤ)(σ:Cover): Prop where
 earn: 0<W
 fare: (((K.c m).val:ℕ):ℤ) = W*n.val
 auth:∀ (j:Axis)(b:ℤ),(∃ s:ℤ, bank σ W b j=gaugeShift K.B s) ∨ ∃ s:ℤ, bank σ W (b+n.val) j=gaugeShift K.B s
variable (n)
def atDeck (x:Cover) := wrap (More n) x
variable {n}{x y:Cover}
local notation "N"=> (K.c m)
private lemma grew (a:Per (More n)):∃ t:ℤ, (0≤t ∧ t<2*n.val)∧a=t:=by
 have h:a.val<n.val*2:=ZMod.val_lt a
 refine ⟨a.val,⟨by positivity,by omega⟩,?_⟩; rw[Int.cast_natCast,ZMod.natCast_zmod_val]
lemma setBank (b:Cover)(v:Site (More n)): ∃ x:Cover,(∀ i,b i ≤ x i ∧ x i < b i + 2*n.val) ∧ atDeck n x=v:=by
 choose t p q using fun i:Axis=> grew (v i-(b i:Per (More n)))
 refine ⟨fun i=> b i + t i,fun i=>?_,?_⟩
 · obtain ⟨e,z⟩:=p i; beta_reduce; constructor <;> omega
 funext i; change (((b i+t i:ℤ)): Per (More n))= v i
 rw [Int.cast_add,←q]; abel
lemma bank_bent (a:Axis)(b:ℤ)(h:atDeck n x=atDeck n y): atDeck n (bent a (2*b) x)=atDeck n (bent a (2*b) y):=by
 funext i; have t:= congrFun h i
 change (↑(x i):Per (More n))= (↑(y i):_) at t
 change Int.cast (pet x a _ i)= (↑(pet y a _ i):Per (More n)); by_cases e:i=a
 · subst i; rw[pet_i,pet_i]; push_cast; rw[t]
 rw [pet_j _ e,pet_j _ e]; exact t
lemma twice_bent (i:Axis)(b:ℤ)(x:Cover):bent i b (bent i b x)=x:=by
 unfold bent; funext j; by_cases h:j=i
 · subst j; simp only [pet_i]; omega
 rw[pet_j _ h,pet_j _ h]
lemma bank_bent_iff (i:Axis)(b:ℤ): atDeck n (bent i (2*b) x)=atDeck n (bent i (2*b) y)↔atDeck n x=atDeck n y:= ⟨fun a=> by simpa only [twice_bent] using bank_bent i b a,bank_bent i b⟩
lemma perBall : (Int.cast (2*(n.val:ℤ)):Per (More n))=0:= by rw[ZMod.intCast_zmod_eq_zero_iff_dvd]; have h:(More n).val=n.val*2:=rfl; rw [h]; push_cast; rw [mul_comm]; -- tune
lemma farBent (i:Axis)(b:ℤ)(x:Cover): atDeck n (bent i (2*(b+n.val)) x)=atDeck n (bent i (2*b) x):=by
 funext j; change (↑(pet x i _ j) : Per (More n))=Int.cast (pet x i _ j); by_cases h:j=i
 · subst j; rw[pet_i,pet_i, mul_add,show _ + _ - x i-1 = 2*b-x i-1+2*(n.val:ℤ) from (by ring : 2*b+2*(n.val:ℤ)-x i-1=2*b-x i-1+2*(n.val:ℤ))]; rw[Int.cast_add,perBall,add_zero]
 rw [pet_j _ h,pet_j _ h]
variable (n) in
def Creek (i:Axis)(b:ℤ)(x:Cover):Prop:= (atDeck n x i-(b:Per (More n))).val < n.val
lemma creek_bank (a:Axis)(b:ℤ)(h:atDeck n x=atDeck n y):Creek n a b x↔Creek n a b y:=by unfold Creek; rw [h]
private lemma int_val {a:ℤ}(l:0≤a)(e:a<2*n.val): (Int.cast a:Per (More n)).val=a.toNat:=by
 nth_rw 1 [← Int.toNat_of_nonneg l]; rw[Int.cast_natCast,ZMod.val_natCast_of_lt]; change _<n.val*2; omega
lemma inCreek {a:Axis}{b:ℤ}(p:b≤x a)(q:x a<b+n.val): Creek n a b x:=by
 unfold Creek; change ((x a:Per (More n))-↑b).val<n.val; have g:=n.property
 rw[←Int.cast_sub,int_val (by omega) (by omega)]; omega
lemma halfFar {a:Axis}{b:ℤ}(p:b-n.val≤x a)(q:x a<b): Creek n a (b+n.val) x:=by
 -- wrap
 unfold Creek; change ((x a: Per (More n))-↑(_ :ℤ)).val<n.val
 rw[← Int.cast_sub, ← add_zero (Int.cast _),←perBall (n:=n),← Int.cast_add,int_val (by omega) (by omega)]; omega
lemma halfNear {a:Axis}{b:ℤ}(p:b-n.val≤x a)(q:x a<b): ¬Creek n a b x:=by
 unfold Creek; change ¬ ((x a: Per (More n))- ↑(b:ℤ)).val<n.val
 rw[←Int.cast_sub, ← add_zero (Int.cast _),←perBall (n:=n),← Int.cast_add,int_val (by omega) (by omega)]; omega
lemma creek_flip (a:Axis)(b:ℤ):Creek n a b (bent a (2*b) x) ↔ ¬Creek n a b x:=by
 obtain ⟨y,t,q⟩:= setBank (pet x a (b-n.val)) (atDeck n x)
 rw[←creek_bank a b q,← creek_bank a b (bank_bent a b q)]
 obtain ⟨z,u⟩:= t a; rw[pet_i] at z u; have v:bent a (2*b) y a=2*b-y a-1:=pet_i ..
 by_cases d:b≤y a
 · have h:= inCreek (n:=n) (a:=a) d (by omega); have h':=halfNear (x:=bent a (2*b) y) (a:=a) (n:=n) (b:=b) (by omega) (by omega); simp [h,h']
 have h:=halfNear (x:=y) (a:=a) (n:=n) z (by omega); have h':=inCreek (n:=n) (x:=bent a (2*b) y) (a:=a) (b:=b) (by omega) (by omega); simp[h,h']
lemma grant_cast {y z:ℤ}(a:LatticeFare K m n W σ)(h:(y:Per (More n))= (z:Per (More n))) : ((↑(W*y):Per (More N)))=Int.cast (W*z):=by
 apply sub_eq_zero.mp; rw[←Int.cast_sub,ZMod.intCast_zmod_eq_zero_iff_dvd]; replace h:=sub_eq_zero.mpr h
 rw[←Int.cast_sub,ZMod.intCast_zmod_eq_zero_iff_dvd] at h
 obtain ⟨d,h⟩:=h; refine ⟨d,?_⟩; rw [←mul_sub,h,show (More n).val=n.val*2 from rfl,show (More N).val=(K.c m).val*2 from rfl]
 simp only [Nat.cast_mul,Nat.cast_ofNat, a.fare]; ring
lemma Creek.inside {i:Axis}{b:ℤ}{S:Finset Cover}(w:LatticeFare K m n W σ)(g:Barn K W σ x S)(ut:Creek n i b x): Satin.region S N ⊆ band N i (bank σ W b i) K.ℓ :=by
 intro v t; obtain ⟨y,hY,rfl⟩:=mem_image.mp t
 apply (band_spec ..).mpr; unfold Creek at ut
 let u:ℕ:= (atDeck n x i-(b:Per (More n))).val -- binder tune shadow!
 have hp: ((((u:ℕ):ℤ):Per (More n)))= (x i: Per (More n))-(b:Per (More n)):=by rw[Int.cast_natCast,ZMod.natCast_zmod_val]; rfl
 let d:= y i-bank σ W (x i) i+W*u
 have ht:= g i y hY
 unfold bank at ht; have he:(((K.c m).val:ℕ):ℤ) = W*n.val:=w.fare
 have hx0:0≤(u:ℤ):=by positivity
 have hx : (u:ℤ)+1≤ n.val:=by -- tune
    have ht:u<n.val:=ut; omega
 have h: ((K.ℓ:ℤ) ≤ d)∧ d+ K.ℓ≤ (K.c m).val:=by
    unfold d bank; rw[he]; obtain ⟨h,h'⟩:=ht; constructor
    · linarith only [h,mul_nonneg w.earn.le hx0]
    linarith only [h',mul_le_mul_of_nonneg_left hx w.earn.le]
 change K.ℓ≤((y i:Per (More N))- _).val ∧ ((y i: Per (More N))- _).val+_ ≤ _
 have hz:(↑(y i):Per (More N))-↑(bank σ W b i)= (d:Per (More N)):=by
   unfold d bank
   rw[Int.cast_add (y i-_),grant_cast w (show (↑((u:ℕ):ℤ):Per (More n))= Int.cast (x i-b) from hp.trans (Int.cast_sub ..).symm)]
   push_cast; ring
 clear he ht
 have hZ:0<(((K.c m).val:ℕ):ℤ):=Int.natCast_pos.mpr (K.c m).property
 rw[hz,int_val (by omega) (by have t:=(K.c m).property; omega)]; omega
end geo
end Weir
end YM.CF.Buffered.Afterglow.Tower.SlabMark
