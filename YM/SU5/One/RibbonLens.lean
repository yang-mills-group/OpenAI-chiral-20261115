import YM.SU5.One.Bazaar
import YM.SU5.One.PickOne
/-!
# Separated extraction data preparation
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry Tapestry.Altitude
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E) (s:ℕ)
local notation "K"=>tent Y H
local notation "L"=>Λ.R.L
local notation "𝒮"=> wingspan Λ l

section geom
variable (S T:Finset Cover)
lemma slide_far (a:Axis) : ∀ᶠ z:ℤ in atTop, Disjoint T (address a z S):=by
 let f(x:Cover):=x a
 obtain ⟨x,t⟩:=(T.finite_toSet.image f).bddAbove
 obtain ⟨y,u⟩:=(S.finite_toSet.image f).bddBelow
 filter_upwards [eventually_ge_atTop (|x|+|y|+1)] with n h
 apply Finset.disjoint_left.mpr; intro i A B; obtain ⟨w,H,rfl⟩:=mem_image.mp B
 have ht: y≤w a:= u (Set.mem_image_of_mem f H)
 have hg : (w+(2*n) • step a:Cover) a≤ x:= t (Set.mem_image_of_mem f A)
 simp at hg; have h0:=le_abs_self x; have h1:= neg_le_abs y; have h2:=abs_nonneg x; have h3:=abs_nonneg y; omega
lemma slide_both (a:Axis) : ∃ z:ℤ, relativeApart S (address a z S) (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)) ∧ Disjoint (𝒮 S) (address a (Λ.R.L.val*z) (𝒮 S)) := by
 let u:=slide_far S (Satin.liner S (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l))) a
 let ℓ:=Λ.R.L
 have v:= (Tendsto.const_mul_atTop' (show (0:ℤ)<ℓ.val by exact_mod_cast Λ.R.L.2) (tendsto_id (x:=atTop))).eventually (slide_far (𝒮 S) (𝒮 S) a)
 exact (u.and v).exists
end geom

section advance
-- on each box use revelation and canonical native orientation. Applies before requires pose axis.
variable (b:Bool)(S:Finset Cover)(n m:ℕ)
local notation "uP" i:max => side Y n i
lemma distribution (f: Family K): distribute Y H s n f=exhibit Y H s n f := (arranged ..).symm

def bazAt : Bazaar S b →ₗ[ℂ] Mark (side Y n s) := (exhibit Y H s n).comp (fresco S b K)
lemma bazAtSpec (f:Bazaar S b): bazAt Y H s b S n f= exhibit Y H s n (fresco S b K f):=rfl
lemma bazAtSafe (f:Bazaar S b): AtSupport b (Satin.region S (uP s)) (bazAt Y H s b S n f):= exhibited Y H s n S (plaid S b _ _)
lemma bazAtInj (r:Hosp S (uP s)): Injective (bazAt Y H s b S n) :=
 (arrange _ _ (terrain Y H (Y.ir n) s)).injective.comp (revelation S b K (momentm Y n s) ((terrain Y H (Y.ir n) s).symm ▸ r))
lemma exhibit_inj {f g:Family K} (p:InTest K true S b f)(t:InTest K true S b g)(h:Hosp S (uP s)) (e:exhibit Y H s n f=exhibit Y H s n g): f=g:=by
 obtain ⟨x,rfl⟩:= outlined _ _ _ p; obtain ⟨y,rfl⟩:= outlined _ _ _ t
 exact congrArg (fresco S b K) (bazAtInj Y H s b S n h e)
lemma bazaarExists {f:Mark (uP s)} (r:Roomy S (uP s))(h:AtSupport b (Satin.region S (uP s)) f) : ∃ t: Bazaar S b,bazAt Y H s b S n t=f:=by
 let u:= terrain Y H (Y.ir n) s; let W:= arrange _ _ u
 have hv : arrange _ _ u (W.symm f)=f:= W.apply_symm_apply f
 have ht:= (displaySupport S u b (W.symm f)).2 (hv.symm ▸ h)
 refine ⟨reup S b K (momentm Y n s) (u.symm ▸ r) ht,?_⟩
 change arrange _ _ u (reveal S b K (momentm Y n s) _) = f; rw [reveal_reup]; exact hv

def art (p: Satin.PairIdx Y s n m) (r: Roomy (wingspan Λ l S) (side Y n (s+1))) (f:Bazaar S b): Bazaar (wingspan Λ l S) b:= (bazaarExists Y H (s+1) b _ n r (ascendSupport Y s n m S p (bazAtSafe Y H s b S n f))).choose
lemma artReads (p: Satin.PairIdx Y s n m) (r: Roomy (wingspan Λ l S) (side Y n (s+1))) (f:Bazaar S b) :
 exhibit Y H (s+1) n (fresco (𝒮 S) b K (art Y H s b S n m p r f)) = ascender Y s n m (exhibit Y H s n (fresco S b K f)):= (bazaarExists Y H (s+1) b _ n r (ascendSupport Y s n m S p (bazAtSafe Y H s b S n f))).choose_spec

def reelAt (p:Satin.PairIdx Y s n m)(r:Roomy (𝒮 S) (side Y n (s+1))) : Bazaar S b→ₗ[ℂ] Bazaar (𝒮 S) b where
 toFun:= art Y H s b S n m p r
 map_add' x y:=by
    apply bazAtInj Y H (s+1) b (𝒮 S) n (Roomy.seats r); rw [map_add]; simp_rw [bazAtSpec, artReads]; simp only [map_add]; exact ascendPlus Y s n m p _ _ (bazAtSafe Y H s b S n _).env (bazAtSafe Y H s b S n _).env
 map_smul' a x:=by apply bazAtInj Y H (s+1) b (𝒮 S) n (Roomy.seats r); rw [map_smul,bazAtSpec,bazAtSpec,artReads,artReads,map_smul,map_smul]; exact ascendScale Y s n m p _ (bazAtSafe Y H s b S n x).env a

def reel : Bazaar S b→ₗ[ℂ] Bazaar (wingspan Λ l S) b:= if h: Satin.PairIdx Y s n m ∧ Roomy (𝒮 S) (side Y n (s+1)) then reelAt Y H s b S n m h.1 h.2 else 0
lemma reelPlot (p:Satin.PairIdx Y s n m) (r:Roomy (𝒮 S) (side Y n (s+1)))(f: Bazaar S b):
    exhibit Y H (s+1) n (fresco (𝒮 S) b K (reel Y H s b S n m f))=ascender Y s n m (exhibit Y H s n (fresco S b K f)):=by
 unfold reel; rw [dif_pos ⟨p,r⟩]; exact artReads Y H s b S n m p r f
lemma even_block {f:Family K}(u:InTest K true S false f)(p:Satin.PairIdx Y s n m)(v:Tivoli (𝒮 S) ((K).c (momentm Y n (s+1)))):
 exhibit Y H (s+1) n (Tower.block Y H s n m S f)=ascender Y s n m (exhibit Y H s n f):=by rw [←distribution, ← distribution]; exact reserved Y H s S n m p u v -- legalAt?

section norm
variable (J:Calibration)

def tess (f:Bazaar S b)(a:Axis)(z:ℤ): Bazaar (address a z S) b:= kitB _ b J (flow_port J a z (plaid S b J f))
lemma tess_r (a:Axis)(z:ℤ)(f:Bazaar S b): fresco (address a z S) b J (tess b S J f a z)=chime J a z (fresco S b J f):=fresco_kitB ..
lemma tess_c (a:Axis)(z:ℤ)(f:Bazaar S b): ‖tess b S J f a z‖≤Tapestry.splay S b*‖f‖:=by
 let F:=fresco S b J f; let T:=address a z S; obtain ⟨m,p⟩:= (separates J T).exists
 apply bazaarQuote T b J m _ ⟨p⟩; intro x; rw [←revealFresco,tess_r]
 exact chime_pay J a z _ (F:=F) (frescoLe S b J · f ·) m x
lemma tess_n (a:Axis)(z:ℤ)(f:Bazaar S b): ‖f‖≤ Tapestry.splay (address a z S) b*‖tess b S J f a z‖ :=by
 let F:= fresco S b J f; let T:= address a z S
 obtain ⟨m,w⟩:= (separates J S).exists
 have hv:=plaid S b J f
 have hu:mirror J a 0 (mirror J a z (chime J a z F))=F:=by unfold chime; rw [reversal J a z (axial J a 0 hv),reversal J a 0 hv]
 let x:=tess b S J f a z
 have he:pay F (Tapestry.splay T b*‖x‖):=by
    let p:pay (fresco T b J x) (Tapestry.splay T b*‖x‖):= (frescoLe T b J · x ·)
    have hz:tess b S J f a z=x:=rfl
    have q:= pay_flips J (pay_flips J p a z) a 0; exact hu ▸ ( (show fresco T b J x=chime J a z F from tess_r b S J a z f) ▸ q : pay (mirror J a 0 (mirror J a z (chime J a z F))) _)

 exact bazaarQuote S b J m f ⟨w⟩ (he m)

variable (g:Axis)(z:ℤ)
lemma reel_two (n:ℕ)(q:Satin.PairIdx Y s n m)(r:Roomy (𝒮 S) (side Y n (s+1)))(f:Bazaar S b): let x:= tess b S K f g z; let y:= reel Y H s b S n m f
 exhibit Y H (s+1) n (fresco (address g (Λ.R.L.val*z) (𝒮 S)) b K (tess b (𝒮 S) K y g (Λ.R.L.val*z)))= ascender Y s n m (exhibit Y H s n (fresco (address g z S) b K x)):=by
 intro x y; dsimp only [x,y]; rw [tess_r,tess_r]; unfold chime
 have ht(s₀:ℕ)(i:ℤ)(f:Family K): exhibit Y H s₀ n (mirror K g i f)=reflMark g i (exhibit Y H s₀ n f):=displayRef ..
 simp_rw [ht]; let t:= (bazAtSafe Y H s b S n f).mono (subset_univ _)
 rw [reelPlot Y H s b S n m q r, ←bazAtSpec, ascendTurnB Y s n m q _ _ ((t.refl g 0).mono (subset_univ _)), ascendTurnB Y s n m q _ _ t,mul_zero]

/-- at the finite trajectory, the two reel outputs on ONE upper world are the jointly paid even mark in Tower.block, not just their financial amount. This is equality per point. -/
lemma reeled_pair (p:Satin.PairIdx Y s n m) (r:Roomy (𝒮 S) (side Y n (s+1))) (c:Tivoli (wingspan Λ l (S∪ address g z S)) ((K).c (momentm Y n (s+1))))
    (h:∀ x∈ Satin.region S (uP s),∀ y∈ Satin.region (address g z S) (uP s), 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)<separation x y)
    (f t:Bazaar S b) : let R:=address g z S; let M:=Λ.R.L.val*z; let Q:=address g M (𝒮 S)
    let x:=fresco S b K f; let y:=fresco (address g z S) b K (tess b S K t g z)
    let u:= reel Y H s b S n m
    exhibit Y H (s+1) n (Tower.block Y H s n m (S∪ R) (x*y)) = exhibit Y H (s+1) n (fresco (𝒮 S) b K (u f) * fresco Q b K (tess b (𝒮 S) K (u t) g M)):=by
 intro R M Q x y u; let hx:=plaid S b K f; let hy:=plaid R b K (tess b S K t g z)
 have hZ : InTest K true (S∪R) false (x*y):= by simpa only [Bool.xor_self] using (hx.mono subset_union_left).mul (hy.mono subset_union_right)
 rw [even_block Y H s (S∪R) n m hZ p c,actual_product, ascendSepB (f:=exhibit Y H s n x) (F:=exhibit Y H s n y) Y s n m p (bazAtSafe Y H s b S n f) (exhibited Y H s n R hy) h,actual_product, show exhibit Y H (s+1) n (fresco Q b K (tess b (𝒮 S) K (u t) g M))= _ from reel_two Y H s b S m g z n p r t]; dsimp only [u]; rw [reelPlot Y H s b S n m p r]
end norm
end advance
end YM.CF.Buffered.Afterglow.Tower.One
