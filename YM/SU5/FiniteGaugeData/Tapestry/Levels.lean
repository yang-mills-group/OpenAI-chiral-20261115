import YM.SU5.FiniteGaugeData.Tapestry.Sandwich
import YM.SU5.FiniteGaugeData.Tapestry.Concord
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Canonical overlap, independent of support box used

Families act as a genuine common language across levels. This only gives a
continuum-of-resolutions interpretation in the sense spelled out by the limits;
NOT treating the two link fields at different levels as the same field setup or
claiming rotationally covariant continuum observables. At intersections use
`render` (all coefficients gathered), not an equivalence modulo unpriced L^p
or positivity seminorm. Cross-level map is **not required to be a homomorphism**;
only separated multiplicativity, proved below. Consumption namespace.
-/
set_option quotPrecheck false

open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S T:Finset Cover)(s i k:ℕ)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (X:Exhibition Y H a b I E L B)
local notation "K"=> tent Y H
local notation "ν" i:max j:max=> side Y i j
local notation "Ω" i:max => side Y i s
local notation "sUp" S:max=>followBox (Λ:=Λ) (l:=l) S
local notation "i₀" t:max=> a (WedgeStage.vol t)
local notation "k₀" t:max => b (WedgeStage.uv t)

lemma present_broad (p:S⊆T)(f:Swatch S) : present Y H s i T (Tapestry.broad K S T p f)=present Y H s i S f:=by rw [present_exhibit, present_exhibit,broadRender]
lemma present_colorless : present Y H s i S (colorless K S)=1:=by rw [present_exhibit,bareUnit,actual_one]
lemma present_brocade (f F:Swatch S) : present Y H s i S (brocade K S f F) = present Y H s i S f* present Y H s i S F:=by rw [present_exhibit,present_exhibit,present_exhibit,bareMult,actual_product]
lemma present_bounce (z:ℤ)(α:Axis)(f:Swatch S) : present Y H s i (negativeSide S z α) (mirrorL K S z α f)=reflMark α z (present Y H s i S f):=by rw [present_exhibit,present_exhibit,mirrored_render]; exact displayRef ..
-- union for geometric qualifiers
def relativeApart (u:ℕ) := Disjoint (Satin.liner S u) T
include H in
lemma farEnough {u:ℕ} (p:relativeApart S T u): ∀ᶠ i:ℕ in atTop, ∀ x ∈ region S (Ω i),∀ y∈region T (Ω i), u<separation x y:=by
  -- Hosp on liner S union T
  filter_upwards [roomyTail Y H s (liner S u ∪ T)] with i h
  intro x X y Z; by_contra! v; have he: y∈ Lattice.halo u (region S (Ω i)):= halo_spec.mpr ⟨x,X,v⟩
  obtain ⟨a,r₀,rfl⟩:=mem_image.mp (linen_contains _ _ _ he); obtain ⟨b,t,w⟩:=mem_image.mp Z
  exact Finset.disjoint_left.mp p (show b∈Satin.liner S u from (Roomy.seats h|>.seat_ (mem_union_right _ t) (mem_union_left _ r₀) w).symm ▸ r₀) t -- parentheses

lemma followGrows (p:S⊆ T) : followBox (Λ:=Λ) (l:=l) S⊆ followBox (Λ:=Λ) (l:=l) T:=by
  intro i h; obtain ⟨a,h,q⟩:= Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨_, Finset.image_subset_image p h,q⟩

lemma ascendSep {f F : Mark (Ω i)} (p:Satin.PairIdx Y s i k)
    {U' V' : Support (More (Ω i))}(f': AtSupport false U' f)(F': AtSupport false V' F)
    (r:∀ x∈ U',∀ y∈ V', 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)<separation x y) : ascender Y s i k (f*F)=ascender Y s i k f*ascender Y s i k F:=
 separated_mult (Vale.apt ..) (patternA Y s i k) Λ.K.j (patternQ Y s i k).val _ Λ.R.odd_side _ _ (patternβ Y s i k) _ (legal Λ) ((Y.voyage i).ownership s).paid.bill ((fullness Y i k p.1).cap_grant.branch s p.2) (threshold Y).1 (threshold Y).2 f F f' F' (tissue Y i s) r
lemma ascendTurn {f : Mark (Ω i)} (α:Axis)(z:ℤ)(p:Satin.PairIdx Y s i k)(f' : AtSupport false univ f): ascender Y s i k (reflMark α z f)=reflMark α ((Λ.R.L.val:ℤ)*z) (ascender Y s i k f):=
 rising (Vale.apt (Y.ir i) Λ.block Λ.R.L s) (patternA Y s i k) Λ.K.j (patternQ Y s i k).val _ Λ.R.odd_side _ _ (patternβ Y s i k) _ α z ((fullness Y i k p.1).cap_grant.aligned s p.2) f' ((fullness Y i k p.1).cap_grant.branch s p.2) ((Y.voyage i).ownership s).paid (legal Λ) (threshold Y).1 (threshold Y).2

namespace Exhibition
include X
lemma uniformRoom : ∀ᶠ t in followStage, Roomy S (Ω (i₀ t)):= (X.univ_.pick.grow_i.tendsto_atTop.comp overStage).eventually (roomyTail Y H s S)
lemma uniformRoad : ∀ᶠ t in followStage, Spanned Y S s (i₀ t) (k₀ t):=(X.cone_bill Y H S s).mono fun i t=>t.1
lemma buoy (f:Swatch S) : Tendsto (fun t=> coupon Y H S s (i₀ t) (k₀ t) f) followStage (𝓝 (B S s f)):=cn_apply (X:=Swatch S) (Y:=Swatch (sUp S)) (X.coneAdvance Y H S s) (tendsto_const_nhds (x:=f))

omit X
lemma overlapPrinciple {J:Type*}{A:Filter J}[A.NeBot]{U V}{M:J→Swatch S}{P:J→Swatch T}{R:J→ℕ}
    (p:Tendsto M A (𝓝 U))(q:Tendsto P A (𝓝 V))(h:∀ᶠ t in A, present Y H s (R t) S (M t)= present Y H s (R t) T (P t))(t:∀ᶠ i in A,Hosp (S∪T) (side Y (R i) s)) : render S K U=render T K V:=by
  let f:= Tapestry.broad K S (S∪T) subset_union_left; let F:= Tapestry.broad K T (S∪T) subset_union_right
  rw [←broadRender K S (S∪T) subset_union_left,←broadRender K T (S∪T) subset_union_right]
  refine congrArg (render (S∪T) K) (tendsto_nhds_unique_of_eventuallyEq (f.continuous.continuousAt.tendsto.comp p) (F.continuous.continuousAt.tendsto.comp q) ?_)
  filter_upwards [h,t] with i u e; apply present_inj Y H s (R i) _ e; exact ((present_broad Y H S _ _ _ subset_union_left _).trans u).trans (present_broad Y H T _ _ _ subset_union_right _).symm
include X
lemma overlap {f:Swatch S} {t: Swatch T} (x: render S K f=render T K t): render (sUp S) K (B S s f)=render (sUp T) K (B T s t):=by
  apply overlapPrinciple Y H (sUp S) (sUp T) (s+1) (X.buoy Y H S s f) (X.buoy Y H T s t) _ ((X.uniformRoom Y H ((sUp S) ∪ (sUp T)) (s+1)).mono fun i h=> Roomy.seats h)
  filter_upwards [X.uniformRoad Y H S s,X.uniformRoad Y H T s] with j l' m
  rw [onSpanned Y H S s _ _ l', onSpanned Y H T s _ _ m]; rw [present_exhibit,present_exhibit,x]

lemma overlapRow {f:Swatch S} {t:Swatch T}(p:Matinee Y S s i)(q:Matinee Y T s i) (h:Hosp ((sUp S)∪(sUp T)) (ν i (s+1)))(x: render S K f=render T K t):
    render (sUp S) K (L S s i f)=render (sUp T) K (L T s i t):=by
  have fs:=cn_apply (X:=Swatch S) (Y:=Swatch (sUp S)) (X.inner S s i) (tendsto_const_nhds (x:=f)); have gs:=cn_apply (X:=Swatch T) (Y:=Swatch (sUp T)) (X.inner T s i) (tendsto_const_nhds (x:=t))
  apply overlapPrinciple Y H (sUp S) (sUp T) (s+1) fs gs _ (Filter.Eventually.of_forall (p:=fun _:ℕ=> Hosp ((sUp S)∪ (sUp T)) (ν i (s+1))) (fun _=>h)) (R:=fun _=>i)
  filter_upwards [X.matineeRow Y H S s i p,X.matineeRow Y H T s i q] with j u v; rw [onSpanned Y H S s _ _ u,onSpanned Y H T s _ _ v,present_exhibit,present_exhibit,x]

lemma unit_preserved : B S s (colorless K S)=colorless K (sUp S):=by
  apply render_inj (sUp S) K; apply overlapPrinciple Y H _ _ (s+1) (R:=fun t=>i₀ t) (X.buoy Y H S s (colorless K S)) tendsto_const_nhds _ ((X.uniformRoom Y H _ (s+1)).mono fun i h=>Roomy.seats h) -- sets unif
  filter_upwards [X.uniformRoad Y H S s] with i q; rw [onSpanned Y H S s _ _ q,present_colorless,present_colorless,ascendUnit Y s _ _ q.1]
lemma interlevel_reflect (f: Swatch S)(α:Axis)(z:ℤ) :
  let R:= negativeSide S z α
  render (sUp R) K (B R s (mirrorL K S z α f)) = bounce K ((Λ.R.L.val:ℤ)*z) α (render (sUp S) K (B S s f)):=by
  intro R
  rw [← mirrored_render]
  let z':= (Λ.R.L.val:ℤ)*z
  let t:= mirrorL K (sUp S) z' α
  apply overlapPrinciple Y H _ _ (s+1) (R:=fun t=>i₀ t) (X.buoy Y H R s (mirrorL K S z α f)) (t.continuous.continuousAt.tendsto.comp (X.buoy Y H S s f)) _ ((X.uniformRoom Y H _ (s+1)).mono fun i h=> Roomy.seats h)
  filter_upwards [X.uniformRoad Y H S s,X.uniformRoad Y H R s] with i q u; dsimp only [Function.comp_apply,t]; rw [onSpanned Y H R s _ _ u, present_bounce, present_bounce,onSpanned Y H S s _ _ q]; exact ascendTurn Y s _ _ α z q.1 ((presented ..).mono (subset_univ _))

omit X in
lemma bilTend {I A A' R:Type*}[NormedAddCommGroup A][NormedSpace ℂ A][NormedAddCommGroup A'][NormedSpace ℂ A'][NormedAddCommGroup R][NormedSpace ℂ R]{v:Filter I} {f:I→A}{F:I→A'}{z:A}{t:A'} (W:A→L[ℂ] (A'→L[ℂ] R)) (p:Tendsto f v (𝓝 z))(q:Tendsto F v (𝓝 t)): Tendsto (fun i=> W (f i) (F i)) v (𝓝 (W z t)):= cn_apply (W.continuous.continuousAt.tendsto.comp p) q
omit X in
lemma brocadeTendsto {A:Type*}{v:Filter A}(K':Calibration)(S:Finset Cover){f F:A→Swatch S}{z t:Swatch S} (p:Tendsto f v (𝓝 z))(q:Tendsto F v (𝓝 t)) : Tendsto (fun i=> brocade K' S (f i) (F i)) v (𝓝 (brocade K' S z t)):= bilTend (A:=Swatch S) (A':=Swatch S) (R:=Swatch S) (brocadeL K' S) p q
/-- General separated-factor law for the limit step (Tor separation is
    eventual, can ask directly by cover `relativeApart`). -/
lemma interlevel_mul {f:Swatch S}{g:Swatch T}{R:Finset Cover}{z:Swatch R}
    (x: render R K z=render S K f*render T K g)
    (h:∀ᶠ i:ℕ in atTop,∀ s'∈ region S (Ω i),∀ t'∈ region T (Ω i), 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)<separation s' t') :
    render (sUp R) K (B R s z)= render (sUp S) K (B S s f)* render (sUp T) K (B T s g):=by
  let M:Finset Cover := (sUp S) ∪ (sUp T); let Z:= Tapestry.broad K (sUp S) M subset_union_left; let W:= Tapestry.broad K (sUp T) M subset_union_right
  have he:∀ f F,render M K (brocade K M (Z f) (W F))=render (sUp S) K f* render (sUp T) K F:= by intro f F; unfold Z W; rw [bareMult,broadRender,broadRender]
  rw [←he]
  apply overlapPrinciple Y H _ _ (s+1) (R:=fun t=>i₀ t) (X.buoy Y H R s z) (brocadeTendsto K M (Z.continuous.continuousAt.tendsto.comp (X.buoy Y H S s f)) (W.continuous.continuousAt.tendsto.comp (X.buoy Y H T s g))) _ ((X.uniformRoom Y H _ (s+1)).mono fun i h=> Roomy.seats h)
  filter_upwards [X.uniformRoad Y H S s,X.uniformRoad Y H T s,X.uniformRoad Y H R s,(X.univ_.pick.grow_i.tendsto_atTop.comp overStage).eventually h] with i a b c P
  dsimp only [Function.comp_apply, Z,W]; rw [onSpanned Y H R s _ _ c,present_brocade,present_broad,present_broad, onSpanned Y H S s _ _ a,onSpanned Y H T s _ _ b]
  rw [show present Y H s _ R z= present Y H s _ S f * present Y H s _ T g from (by simp_rw [present_exhibit,x,actual_product])]; exact ascendSep _ _ _ _ c.1 (presented ..) (presented ..) P
end Exhibition
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.unit_preserved
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.overlap
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.interlevel_mul
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.interlevel_reflect
