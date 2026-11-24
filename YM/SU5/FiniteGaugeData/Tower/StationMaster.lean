import YM.SU5.FiniteGaugeData.Tower.StationRide
import YM.SU5.FiniteGaugeData.Tower.Hours
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Set
/-!
# Bounded stationary-grid slab ops at arbitrary observing resolution

Single Hilbert system, sewn entries, actual chiral atoms. No continuity
assertion on Op norm vs grid **space offsets** of the inserter. Eventually
will be able to show time smoothing in parameterizations of these slabs
and use with independent rotations assumptions. Not a Dirac-Fock space of
observables modulo |density| and requires the chosen `Coherent+Clipped` path
so that one-stack bills close. -/
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (Qt : Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
variable (w:ℕ)(f:Entry Y H s j strict w)(hw:0 < w)
local notation "A"=> Ark.Ht Y H Q.circuit j 0 strict C
local notation "Γ" i:max=> Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s Q.circuit j 0 strict C
local notation "u"=>advance Y H V Q.circuit j 0 strict C
local notation "tM" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "T" i:max h:max f:max=>furnished Y H s Q j strict w f i h
local notation "D₀" t:max=>Λ.R.L.val^(t-s)*w
local notation "M" i:max x:max=>slabT Y H i j strict (Λ.R.L.val^(i-s)*w) x
local notation "Λ₀" t:max => L₀^(t-s)

-- Heat has dense range by OS dynamics, despite no assertion of strong continuity on space.
-- Combined with `sounds` means crowd on heated domain dense (not just generated).
include V C
lemma complete_time (t:ℝ≥0):DenseRange (u t):= OS.Semigroup.whole ((clockdrive Y H V Q.circuit j 0 strict C).monoAxis j) t
noncomputable def portal(t:ℕ): ℕ:=2*(Λ.R.L.val^(t-s)*(3*w)) -- count number tick units
local notation "δ" t:max=> portal (Λ:=Λ) s w t
local notation "G₀" t:max=>tick Y H t j 0 strict (portal (Λ:=Λ) s w t)
noncomputable def situated := ⋃ (r:ℕ)(_ : s≤ r), range fun t: Tower.Field Y H r j 0 strict=> actor Y H r Q.circuit j 0 strict C (tick Y H r j 0 strict (portal (Λ:=Λ) s w r) t)
include w
lemma all:situated Y H s Q j strict C w=(u (tM s (3*w))) '' itinerary Y H V Q.circuit j 0 strict C:=by
 ext p
 constructor
 · intro a; obtain ⟨r,v⟩:= mem_iUnion.mp a; obtain ⟨h,e⟩:= mem_iUnion.mp v; obtain ⟨i,hp⟩:=e
   refine ⟨(κ r) i,mem_iUnion.mpr ⟨r,mem_range_self i⟩, (horizontal_time Y H V s Q j strict C w _ h i).trans hp⟩
 rintro ⟨x,h,t⟩; obtain ⟨r,x'⟩:= mem_iUnion.mp h; obtain ⟨v,d⟩:=x'
 let m:=max s r; have hm:r ≤ m:=le_max_right ..; have ht:s≤ m:=le_max_left ..
 let y:=Raise Y H Q.circuit j 0 strict r m hm v
 refine mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨ht,y,?_⟩⟩
 change (κ m) (tick _ _ _ _ _ _ (2*(L₀^(m-s)*(3*w))) y)=p
 rw [←horizontal_time Y H V s Q j strict C w m ht y,join_actor Y H V]; change advance _ _ _ _ _ _ _ _ _ (arrows _ _ V _ _ _ _ C r v)= _; rw [d,t]
lemma concurs : Dense (situated Y H s Q j strict C w):=by
 rw [all Y H V]
 intro x
 have h:=complete_time Y H V Q j strict C (tM s (3*w)) x
 refine closure_minimal (t:=closure _) ?_ isClosed_closure h -- univ error
 rintro x ⟨v,rfl⟩
 exact (u (tM s (3*w))).continuous.continuousAt.continuousWithinAt.mem_closure (sounds Y H V Q.circuit j 0 strict C v) (mapsTo_image _ _)
include Qt hw
lemma uniform_operator :∃B:ℝ,0<B ∧ ∀ t:ℕ,∀ p:s≤t,∀x:Γ t, ‖(κ t) ((M t (T t p f)) x)‖≤ B * ‖(κ t) x‖:=by
 let f' := inverse Y H s j strict w f
 obtain ⟨B,hF,p⟩:=drives_paid Y H V s Q j strict C w f' Qt hw
 refine ⟨B,hF,fun t e x=> ?_⟩
 let M':=(κ t) ((M t (T t e f)) x); let x':=(κ t) x; let c':=B*‖x'‖
 have ht(y:A): ‖inner ℂ M' y‖ ≤ c'*‖y‖:=by
    let L:Set A:={y : A | ‖inner ℂ M' y‖ ≤ c'*‖y‖}
    have h₁:IsClosed L:= isClosed_le (continuous_const.inner continuous_id|>.norm) (continuous_const.mul continuous_norm)
    refine closure_minimal (t:=L) ?_ h₁ (concurs Y H V s Q j strict C w y)
    intro z vz; obtain ⟨r,i'⟩:= mem_iUnion.mp vz; obtain ⟨v,u'⟩:=mem_iUnion.mp i'; obtain ⟨a,rfl⟩:=u'
    let S:=max t r; have h:t ≤ S:=le_max_left ..; have q:r ≤ S:=le_max_right ..
    let X:= Raise Y H Q.circuit j 0 strict t S h x
    let Y0:= Raise Y H Q.circuit j 0 strict r S q a
    have hg : Raise Y H Q.circuit j 0 strict r S q ((G₀ r) a)=(G₀ S) Y0:=by
       rw [← tick_up Y H V _ Q.circuit]
       have hp: L₀^(S-r)*δ r=δ S:=by unfold portal; rw [mul_left_comm _ 2,← mul_assoc _ (L₀^(r-s)) _, ← pow_add,show S-r+(r-s)=S-s by omega]
       rw [hp]
    change ‖inner ℂ ((κ t) ((M t (T t e f)) x)) ((κ r) ((G₀ r) a))‖≤ _
    have hv:=e.trans h
    change _ ≤ (B*‖(κ t) x‖)*‖(κ r) ((G₀ r) a)‖
    rw [←join_actor Y H V Q.circuit j 0 strict C t S h, ←join_actor Y H V Q.circuit j 0 strict C r S q,along Y H V s Q j strict C,hg,
      ←join_actor Y H V Q.circuit j 0 strict C t S h x, symmetry Y H V S Q.circuit]
    apply (norm_inner_le_norm ..).trans
    rw [←reverse_launch Y H V s Q j strict C w f S hv]
    have he:=p S hv Y0
    refine le_trans (mul_le_mul_of_nonneg_left he (norm_nonneg _)) (le_of_eq ?_); unfold portal; ring
 have hi:=ht M'
 rw [inner_self_eq_norm_sq_to_K,norm_pow] at hi; change ‖((‖M'‖:ℝ):ℂ)‖^2≤ _ at hi; simp only [Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)] at hi
 change ‖M'‖≤c'; have Hcc:0≤c':=mul_nonneg hF.le (norm_nonneg _); nlinarith [norm_nonneg M', norm_nonneg x']

lemma main : ∃ B:A→L[ℂ] A, ∀ t:ℕ,∀ p:s≤ t,∀x:Γ t, B ((κ t) x)=(κ t) ((M t (T t p f)) x):=by
 obtain ⟨B,h,t⟩:=uniform_operator Y H V s Q Qt j strict C w f hw
 let c:ℂ:=((B⁻¹:ℝ):ℂ); have he:‖c‖=B⁻¹:=by unfold c; simp [h.le]
 let A':Lamination Y H s Q.circuit j 0 strict C:={
     go t p:= c • (M t (T t p f))
     weak x p i:= by
       rw [LinearMap.smul_apply]; change ‖arrows Y H V Q.circuit j 0 strict C x (c • _)‖≤ _
       rw [map_smul,norm_smul,he]; change B⁻¹ * ‖(κ x) _‖≤ _; exact (mul_le_mul_of_nonneg_left (t x p i) (by positivity)).trans (le_of_eq (by field))
     same t r p v i:=by
       rw [LinearMap.smul_apply,LinearMap.smul_apply,←along Y H V s Q j strict C]; apply Subtype.ext
       let a:=(M t (T t p f)) i; let I:=t
       have he:TestFamily (tent Y H) true a.val:=(exam j _ K ((purpose_ok ..).1 a.property).1).1
       exact woven_smul Y H Q.circuit t (r-t) he c }
 let d:=onship Y H V s Q.circuit j 0 strict C A'
 refine ⟨(↑B:ℂ)•d,fun i p v=>?_⟩
 rw [ContinuousLinearMap.smul_apply, show d ((κ i) v)=_ from todeck Y H V s Q.circuit j 0 strict C A' p v]
 change _ • arrows _ _ V _ _ _ _ C i ((c • (M i (T i p f))) v) =_
 rw [LinearMap.smul_apply,map_smul,smul_smul, show (↑B:ℂ)*c=1 by unfold c; push_cast; field_simp,one_smul]; rfl
noncomputable def boxOp:A→L[ℂ] A:=(main Y H V s Q Qt j strict C w f hw).choose
local notation "B₀" f:max=>boxOp Y H V s Q Qt j strict C w f hw
lemma snatch{t:ℕ}(p:s≤ t)(x:Γ t): (B₀ f) ((κ t) x) = (κ t) ((M t (T t p f)) x):=(main Y H V s Q Qt j strict C w f hw).choose_spec t p x
lemma snatch_equal (x:Γ s): (B₀ f) ((κ s) x) = (κ s) (slabT Y H s j strict w f x):=by
 rw [snatch Y H V s Q Qt j strict C w f hw le_rfl]
 apply congrArg (κ s); apply Subtype.ext; repeat' rw [slab_eq]; -- same macro issue
 change stream Y H D s (s-s) f.val.val*(relocate K j _ x.val)= f.val.val*(relocate K j _ x.val)
 rw [Nat.sub_self, stream, pow_zero,one_mul]; rfl
lemma respects: (B₀ f).adjoint=B₀ (inverse Y H s j strict w f):=by
 apply _root_.YM.Kernel.Gram.by_bud C; intro i
 apply all_voices Y H Q.circuit j 0 strict C; intro t x
 let A₁:Arena Y H Q.circuit j 0 strict:=C
 let B:= B₀ f; let B':=B₀ (inverse Y H s j strict w f)
 let S:=max s (max t i.1); let h₁:s≤ S:=le_max_left ..; let h₂:t ≤ S:=(le_max_left ..).trans (le_max_right ..); let h₃:i.1≤ S:=(le_max_right ..).trans (le_max_right ..)
 let x':= (κ i.1) i.2
 change inner ℂ ((κ t) x) (B.adjoint x')=inner ℂ ((κ t) x) (B' x')
 unfold B B' x'
 rw [←join_actor Y H V Q.circuit j 0 strict C t S h₂ x,←join_actor Y H V Q.circuit j 0 strict C i.1 S h₃ i.2,ContinuousLinearMap.adjoint_inner_right,
    snatch Y H V _ Q _ j _ _ _ _ _ h₁,snatch Y H V _ Q _ j _ _ _ _ _ h₁, symmetry Y H V S Q.circuit,reverse_launch Y H V s Q j strict C]

end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.respects
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.snatch_equal
