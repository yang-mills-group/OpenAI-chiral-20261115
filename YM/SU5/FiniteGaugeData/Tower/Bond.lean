import YM.SU5.FiniteGaugeData.Tower.Ink
import YM.SU5.FiniteGaugeData.Tower.Consistent
import YM.SU5.FiniteGaugeData.Tower.Diagnostic
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
# Local even physical algebra and single observing hierarchy

Retain across the actual cross-level E compatibility all gauge singlets in
both languages (in general should expect flow into the joint pair language,
even when inserting a continuous link-only mark). `CovCover` demands more
than `Singlet`: THIS is a property on all periods, since the Course periods
need not be accepted by the progression. Show equivalent on this support
system. No arbitrary ICC/spectator CAR outside the physical chiral
polarizations. All fixed transported reflected-product diagnostics & positive
forms from now on can use this one coherent system (in resolution sense,
not contact or continuum Wightman).
-/
section actual
open Fock
variable (Z:Calibration)
def CovCover (f:Family Z):Prop:= ∀ m,covariant (f m)
lemma covariant_parts {A B:Family Z}(x:CovCover Z A)(h:CovCover Z B):
    CovCover Z (A+B)∧ CovCover Z (A*B):=
 ⟨by intro n g p; simp_rw [Pi.add_apply,x _ g p,h _ g p,map_add],by intro n g p; simp_rw [Pi.mul_apply,x _ g p,h _ g p,map_mul]⟩
lemma covariant_scale{A:Family Z}(x:CovCover Z A)(y:ℂ):CovCover Z (y•A):=by
 intro n g p; simp_rw [Pi.smul_apply,x _ g p,twist_scalar]
lemma covariant_one:CovCover Z (1:Family Z):=by intro m g x; exact (map_one _).symm
lemma covariant_zero:CovCover Z (0:Family Z):=by intro m g x; exact (map_zero _).symm
lemma covariant_flips (a:Axis)(z:ℤ){A:Family Z}{S:Finset Cover}(t:InTest Z true S false A)(p:CovCover Z A):CovCover Z (mirror Z a z A):=fun m=>covariant_reflected (t.support m) (p m) z a
lemma aligned {F:Family Z}{S:Finset Cover}(h:InTest Z true S false F)(p:Singlet F): CovCover Z F:=by
 obtain ⟨s,t⟩:= eventually_atTop.mp ((separates Z S).and p)
 let b:Side:=s*2+1 -- not ? addition on PNat exists
 let m:=Z.q*b
 have he : s.val*2 ≤ b.val:= Nat.le_add_right ..
 have ht : s≤ m:= show s.val≤ Z.q.val*b.val from (le_trans (by omega : s.val≤b.val) (Nat.le_mul_of_pos_left _ Z.q.property))
 obtain ⟨w,H⟩:= t m ht
 refine complete_cov Z h m ⟨w⟩ (H ⟨b,?_,rfl⟩)
 exact ⟨s.val,(by change s.val*2+(1:ℕ)= _; omega)⟩

/-- Native physical gauge-invariant local observable system at one level.
At any host with Tivoli support, this is EXACTLY the even Borel (+ continuous
first-link-only for wide=false) gauge--CAR system at that period. -/
def observ (S:Finset Cover)(wide:Bool): Subalgebra ℂ (Family Z) where
 carrier:={F|F∈ supported Z S wide ∧ CovCover Z F}
 mul_mem':=fun p t=>⟨Subalgebra.mul_mem (supported Z S wide) p.1 t.1,(covariant_parts Z p.2 t.2).2⟩
 add_mem':=fun p t=>⟨Subalgebra.add_mem (supported Z S wide) p.1 t.1,(covariant_parts Z p.2 t.2).1⟩
 zero_mem':=⟨InTest.zero,covariant_zero Z⟩
 one_mem':=⟨InTest.one,covariant_one Z⟩
 algebraMap_mem' c:=⟨(supported Z S wide).algebraMap_mem _,by rw [Algebra.algebraMap_eq_smul_one]; exact covariant_scale Z (covariant_one Z) c⟩
lemma obs_in(S:Finset Cover)(wide:Bool)(F:Family Z):F∈ observ Z S wide↔ InTest Z wide S false F∧ CovCover Z F:=Iff.rfl
lemma obs_flip (a:Axis)(z:ℤ){F:Family Z}{S:Finset Cover}{wide:Bool}(p:F∈ observ Z S wide):mirror Z a z F∈ observ Z (reflectedBox a z S) wide:=by
 obtain ⟨x,v⟩:= (obs_in ..).1 p; cases wide
 · exact ⟨axial Z a z x,covariant_flips Z a z x.widen v⟩
 exact ⟨axial Z a z x,covariant_flips Z a z x v⟩
lemma basis_obs {m:Side}{S:Finset Cover}(t:Tivoli S (Z.c m))(f:Mark (Z.c m))(h:AtSupport false (Satin.region S (Z.c m)) f)(v:covariant f):∃ F∈ observ Z S true, (F:Family Z) m=f:= by refine ⟨extendAtlas S Z m t f,⟨dictionary S Z m t f h,atlas_color Z m t h v⟩,native S Z m t f h⟩ -- syntax setlike? mem variable
lemma actual_obs {m:Side}{S:Finset Cover}(t:Tivoli S (Z.c m))(F : Evaluation (Z.c m))(h:AtSupport false (Satin.region S (Z.c m)) (toMark F))(v:covariant (toMark F))(c:Continuous F):∃ f∈ observ Z S false, (f:Family Z) m=toMark F:= by refine ⟨extendAtlas S Z m t (toMark F),⟨narrow_dict S Z m t (toMark F) h F rfl c,atlas_color Z m t h v⟩,native S Z m t (toMark F) h⟩
end actual

section induction
variable {S:Finset Cover}{F:Family (tent Y H)}(h:F∈ observ (tent Y H) S true)

include h
lemma lifts_native (x k:ℕ)(e:legalAt Y s x k): block Y H s x k S F∈ observ (tent Y H) (wingspan Λ l S) true:=by
 let W:= wingspan Λ l S
 refine ⟨booked ..,?_⟩
 have t:= ((obs_in ..).1 h)
 unfold block; rw [if_pos ⟨e,t.1⟩,distribute_back]; split; swap; · exact covariant_zero _
 let g:= (Vale.apt (Y.ir x) Λ.block Λ.R.L s); let a:=((Y.voyage x).X (Y.uv k)); let K₁:=steps Λ.V (Y.ir x) Λ.block (Y.uv k); let p:= (fullness Y x k e.1).cap_grant
 obtain ⟨j⟩:= p.grant s e.2; obtain ⟨w,v,i,F0,u⟩:= j.cap
 have he: covariant (aboveD Y H s x k F):= gauge_pushed g Λ.K.j (Journey.aliasLaw Λ) (show Stencil.LaurentRadius _ Λ.R.L _ from Journey.legal Λ) Λ.R.odd_side (a.gram (s+1)).J.M (a.wave s) (K₁ s) Chi.canonical (a.gram (s+1)).beta Λ.J.d ((Y.voyage x).CapeT s) (p.aligned s e.2) (p.branch s e.2) j.legal.1 j.legal.2 (stationed Y H s S x t.1) (castV (terrain Y H (Y.ir x) s) (t.2 _)) F0
 let δ:=terrain Y H (Y.ir x) (s+1)
 exact atlas_color (tent Y H) (momentm Y x (s+1)) _ (ship_box δ.symm W (upper Y H s S x k e t.1)) (castV δ.symm he)
where castV {x y:Side}(h:x=y){f:Mark x}(p:covariant f):covariant (ship h f):=by subst x; exact p

variable (n k₀:ℕ→ℕ)(D:Cresc Y H n k₀)
include h D
lemma color_stays : destined Y H s n k₀ S D F∈ observ (tent Y H) (wingspan Λ l S) true:=by
 have ht:= (obs_in ..).1 h
 refine ⟨attaches ..,?_⟩
 intro m g x
 apply tendsto_nhds_unique (ev_image Y H s n k₀ D S ht.1 m (simultaneous g x))
 refine (((Fock.breeze _).continuousAt.tendsto.comp (ev_image Y H s n k₀ D S ht.1 m x)).congr' (Eventually.of_forall fun r=>?_))
 have hu: CovCover K (block Y H s (n r) (k₀ r) S F):=by
    by_cases p:legalAt Y s (n r) (k₀ r)
    · exact ((obs_in ..).1 (lifts_native Y H s h (n r) (k₀ r) p)).2
    rw [block,if_neg (by tauto)]; exact covariant_zero _
 exact (hu m g x).symm
end induction
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.color_stays
#print axioms YM.CF.Buffered.Afterglow.Tower.basis_obs
