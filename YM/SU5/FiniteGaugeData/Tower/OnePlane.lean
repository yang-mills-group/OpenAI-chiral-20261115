import YM.SU5.FiniteGaugeData.Tower.Upright
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Uniform price for arbitrarily separated boxes via a one-plane lemma

Geometry. Either two axis-width-d boxes on the actual torus fit a bounded
price chamber at once, or one can apply buffered RP on a separating
aligned plane which puts ONE box near the plane (its union with reflected
copy fits a bounded chamber), leaving BOTH supports in the required opposite
halves even when antipodal. Reflected supports retain all axis widths. This
will imply volume/distance-independent cost globally on separated pairs via
a maximum principle on the supremum norm price; don't multiply correlation
equalities on nonindependent fields, don't pay operators on growing boxes as
though the `Homes` threshold worked there.
-/
open Fock Laurent Bloch Next.Free Fir Branch Tap Tenant Precision Drapes Vault Tree Heat
variable {Z:Calibration}{n:Side}
local notation "c"=> (Z.c n)

private lemma carousel {N:Side}{a b k:ℤ}(w:a=b+(N.val:ℤ)*k){d:ℕ}{x:Per N} (h:Chord b d x): Chord a d x:=by
 obtain ⟨y,v,p,rfl⟩:=h; refine ⟨y+(N.val:ℤ)*k,?_,?_,?_⟩
 · rw [w]; omega
 · rw [w]; omega
 push_cast; simp

-- reorient two labeled arcs to start-distance ≤ c. allow swap. always
-- possible, including when coincident.
private lemma orient {S T:Support (More (Z.c n))}{i:Axis}{d:ℕ}(h:rest Z n S i d)(t:rest Z n T i d):∃ a b:ℤ, a≤b ∧ b≤a+(c).val∧
 ((∀ x∈S,Chord a d (x i))∧(∀ x∈T,Chord b d (x i)) ∨ (∀ x∈T,Chord a d (x i))∧(∀ x∈S,Chord b d (x i))):=by
 obtain ⟨a,h⟩:=h; obtain ⟨b,t⟩:=t
 let m:ℤ:=(c).val; let L:ℤ:=(More (c)).val
 have ht: L=2*m:=by unfold L m; rw [show (More c).val=(c).val*2 from rfl]; push_cast; ring
 have he:0 < m:= by unfold m; exact_mod_cast (c).property
 let r:=(b-a)%L
 have hv:b-a = r+L*((b-a)/L):=(Int.emod_add_mul_ediv ..).symm
 have hu:0≤r:= Int.emod_nonneg _ (by omega); have hz:r<L:=Int.emod_lt_of_pos _ (by omega)
 by_cases g:r≤ m
 · refine ⟨a,a+r,(by omega),(by change a+r ≤ a+m; omega),Or.inl ⟨h,?_ ⟩ ⟩; intro x v; refine carousel (k:= - ((b-a)/L)) ?_ (t x v); change _ = _+L*(-_); linarith only [hv]
 refine ⟨a+r,a+L,(by omega),(show a+L≤ a+r+m by omega),Or.inr ⟨?_,?_⟩⟩
 · intro x H; refine carousel (k:= - ((b-a)/L)) ?_ (t x H); change _=b+ L*(-_); linarith only [hv]
 intro x H; apply carousel (k:=1) (b:=a); change _=a+L*1; ring; exact h _ H

-- either common arc or separate with near *lower* arc
-- aligned plane chosen so z >= a+d+ℓ, z <= a+d+gap
private lemma align (a:ℤ)(d:ℕ):∃ z:ℤ, a+d+Z.ℓ ≤ gaugeShift Z.B z ∧ gaugeShift Z.B z ≤ a+d+stepgap Z:= by
 let k:ℤ:=4*Z.B.val; have ht:0<k:=by unfold k; positivity
 let z:=(a+d+Z.ℓ)/k
 refine ⟨z+1,?_⟩; unfold gaugeShift stepgap; change _ ≤ k*(z+1)∧ k*(z+1) ≤ _
 have he:=(Int.emod_add_mul_ediv (a+d+Z.ℓ:ℤ) k)
 have hv:=Int.emod_nonneg (a+d+Z.ℓ:ℤ) ht.ne'
 have h':=Int.emod_lt_of_pos (a+d+Z.ℓ:ℤ) ht
 rw [mul_add,mul_one]; change _ + k*z = _ at he
 unfold k at *; push_cast; omega

private lemma place_band (i:Axis)(z:ℤ)(T:Support (More (Z.c n)))(b:ℤ)(d:ℕ)(p:z+Z.ℓ≤ b)(v:b+d+Z.ℓ≤z+(Z.c n).val)(t:∀x∈T,Chord b d (x i)):T⊆ band c i z Z.ℓ:=by
 intro x w; obtain ⟨y,k,r,e⟩:= t x w
 let Y:=(y-z).toNat
 have hx:0≤y-z:=by omega
 have ha:Y<(More c).val:=by change _<(c).val*2; have h:0<(c).val:=(c).property; unfold Y; omega
 apply (band_spec ..).mpr; rw [←e,←Int.cast_sub,← Int.toNat_of_nonneg hx,Int.cast_natCast,ZMod.val_natCast_of_lt ha]; omega
private lemma ref_arc (i:Axis)(z:ℤ)(S:Support (More (Z.c n))){a:ℤ}{d:ℕ}(h:∀x∈S,Chord a d (x i)):∀x∈S.image ((plane i z).anon c), Chord (2*z-a-d) d (x i):=by
 rintro y b; obtain ⟨x,t,rfl⟩:= mem_image.mp b; obtain ⟨q,v,w,H⟩:=h x t
 refine ⟨2*z-q,by omega,by omega,?_⟩
 have he:= across_coord i z x
 rw [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,H, eq_add_of_sub_eq he]; ring
lemma stays {S:Support (More (Z.c n))}{j a:Axis}{d:ℕ}(u:rest Z n S a d)(s:ℤ):rest Z n (S.image ((plane j s).anon c)) a d:=by
 obtain ⟨x,p⟩:=u; by_cases h:a=j
 · subst a; exact ⟨_, ref_arc j s S p⟩
 refine ⟨x,fun y t=>?_⟩; obtain ⟨y,v,rfl⟩:=mem_image.mp t
 rw [show (plane j s).anon c y a=y a from by simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,h,Ne.symm h]]; exact p _ v
private lemma common_trans {S:Support (More (Z.c n))}{j a:Axis}{d:ℕ}(u:rest Z n S a d)(p:a≠j)(z:ℤ):rest Z n (S∪S.image ((plane j z).anon c)) a d:=by
 obtain ⟨b,u⟩:=u; refine ⟨b,fun i t=>?_⟩; rcases mem_union.mp t with w|w; exact u _ w
 obtain ⟨i,h,rfl⟩:=mem_image.mp w; rw [show (plane j z).anon c i a=i a from by simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,p,p.symm]]; exact u _ h
lemma rest_raise {S:Support (More (Z.c n))}{i:Axis}{d e:ℕ}(h:rest Z n S i d)(p:d≤e): rest Z n S i e:=by obtain ⟨a,h⟩:=h; refine ⟨a,fun i x=>?_⟩; obtain ⟨y,t,v,u⟩:=h _ x; exact ⟨y,t,by omega,u⟩

def widthPair (Z:Calibration)(d:ℕ):ℕ:= 2*d+2*(stepgap Z)
-- swapped or not, if stands in front may directly, behind via refl of A
structure clears (Z: Calibration)(n:Side)(i:Axis)(d:ℕ) (S T:Support (More (Z.c n)))(z:ℤ):Prop where
 pos:T⊆band (Z.c n) i (gaugeShift Z.B z) Z.ℓ
 neg:S.image ((plane i (gaugeShift Z.B z)).anon (Z.c n)) ⊆band (Z.c n) i (gaugeShift Z.B z) Z.ℓ
 short: ∀ j,rest Z n (S∪S.image ((plane i (gaugeShift Z.B z)).anon (Z.c n))) j (widthPair Z d)
private lemma after_align{S T:Support (More (Z.c n))}(i:Axis){a b:ℤ}{d:ℕ}(h:a≤ b)(t:b≤a+(c).val)(x:∀ x∈ S,Chord a d (x i))(y:∀ x∈T,Chord b d (x i))(E:∀ j,rest Z n S j d) (e:widthPair Z d+addgap Z≤ (c).val):
 rest Z n (S∪T) i (widthPair Z d) ∨ ∃ z:ℤ, clears Z n i d S T z :=by
 let g:=stepgap Z; have ht: Z.ℓ≤g:=Nat.le_add_right ..
 let z(a:ℤ):= gaugeShift Z.B a
 obtain ⟨v,m,q⟩:= align (Z:=Z) a d; let V:=z v; change _≤V at m; change V≤ _ at q
 by_cases b': b< V+Z.ℓ
 · left; refine ⟨a,fun w p=>?_⟩; rcases mem_union.mp p with p|p
   
   · obtain ⟨u,r,v,k⟩:=(x w p); exact ⟨u,r,by unfold widthPair; omega,k⟩
   · obtain ⟨u,r,w,k⟩:=(y w p); exact ⟨u,by omega,by unfold widthPair; unfold g at *; omega,k⟩
 right
 unfold widthPair addgap at e
 refine ⟨v,place_band i V T b d (not_lt.mp b') (by omega) y,place_band i V _ (2*V-a-d) d (by omega) ?_ (ref_arc i V S x),fun j=>?_⟩
 · unfold g at *; omega
 by_cases J:j=i
 · subst j; refine ⟨a,fun j k=> ?_⟩; rcases mem_union.mp k with k|k
   · obtain ⟨w,y,z,f⟩:= x j k; exact ⟨w,y,(by unfold widthPair; omega),f⟩
   obtain ⟨w,y,z',f⟩:=ref_arc i V S x j k; exact ⟨w,(by unfold g at *; omega),(by unfold g at *; unfold widthPair; omega),f⟩
 exact rest_raise (common_trans (E j) J _) (by unfold widthPair; omega)

lemma one_plane{S T:Support (More (Z.c n))}{d:ℕ}(h:∀ i,rest Z n S i d)(p:∀ i,rest Z n T i d)(e:widthPair Z d+addgap Z≤ (c).val):
 (∀ i,rest Z n (S∪T) i (widthPair Z d)) ∨ (∃ i z,clears Z n i d S T z ∨ clears Z n i d T S z):=by
 by_cases k:∀ i,rest Z n (S∪T) i (widthPair Z d); exact Or.inl k
 right; push Not at k; obtain ⟨i,x⟩:=k; obtain ⟨a,b,f,g,V⟩:= orient (h i) (p i); rcases V with ⟨A,B⟩ | ⟨A,B⟩
 · obtain q|⟨z,Z⟩:= after_align i f g A B h e; exact (x q).elim; exact ⟨i,z,Or.inl Z⟩
 obtain q|⟨z,Z⟩:= after_align i f g A B p e; rw [Finset.union_comm] at q; exact (x q).elim; exact ⟨i,z,Or.inr Z⟩
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.one_plane
