import YM.SU5.One.Mosaic

/-!
# Define the common graded refinement system. Same approved charge transport. Compatible everything with G.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 350000
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
variable {D: ℕ→ Family (tent Y H) → Family (tent Y H)}{n m:ℕ→ℕ}(d: Coherent Y H (i:=i) (k:=k) (E:=E) D n m)
local notation "K"=>tent Y H
local notation "𝒮"=> wingspan Λ l
section rich
variable {α:ℕ→ℕ}{M: Collection Λ l}
local notation "ι"=> (i ∘ n) ∘ α
local notation "μ"=> (k ∘ m) ∘ α
variable (Q:AdmitsCollection Y H ((i ∘ n)∘α) ((k∘m)∘α) M)(h: Tendsto α atTop atTop)
variable (S T:Finset Cover)
local notation "ℓ" s:max i:max=>offersB Y H s ((ι) i) ((μ) i)
local notation "ρ" i:max=> ℓ s i
local notation "A"=>exhibit Y H s
local notation "B"=>exhibit Y H (s+1)
variable (b e:Bool)
local notation "W" S:max=>𝒮 S
local notation "ν" S:max=>side Y S (s+1)

include V d h
lemma occupiedH : Tendsto ((i∘n)∘α) atTop atTop:= ((V.pick.grow_i.comp d.growsA).tendsto_atTop.comp h)
include Q
lemma planeSees : ∀ᶠ i' in atTop,∀ f:Bazaar S b,
   exhibit Y H (s+1) ((ι) i') (fresco (W S) b K (offersB Y H s ((ι) i') ((μ) i') S b f)) = ascender Y s ((ι) i') ((μ) i') (exhibit Y H s ((ι) i') (fresco S b K f)):=by
 filter_upwards [Q.continuousTail s S b,(occupiedH Y H V d h).eventually (roomyTail Y H (s+1) (W S)),h.eventually (d.finance (s+1))] with r x y z
 intro f; rw [show ((ρ r) S b) f=reel Y H s b S ((ι) r) ((μ) r) f from DFunLike.congr_fun x f]; exact reelPlot Y H s b S ((ι) r) ((μ) r) ⟨z.depth,z.enters⟩ y _
omit V d h Q
lemma viewing (J:Calibration)(N:Side)(x: Fields (J.c N)): Continuous (fun f:Bazaar S b=> fresco S b J f N x) := by
 let U: Bazaar S b →ₗ[ℂ] FC (Single (J.c N)):= (LinearMap.proj x).comp (reveal S b J N)
 let T:= U.mkContinuous (Tapestry.splay S b) (fun f=> revealLe S b J N f x); exact T.continuous
include Q
lemma funnel {T:ℕ→ Bazaar S b}{f: Bazaar S b}(p:Tendsto T atTop (𝓝 f)) :
 Tendsto (fun i'=> ((ρ i') S b) (T i')) atTop (𝓝 (M s S b f)):= cn_apply (X:=Bazaar S b) (Y:=Bazaar (𝒮 S) b) (Q.proceeds ..) p
lemma pinpoint (N:Side)(x: Fields ((tent Y H).c N))(f:Bazaar S b): Tendsto (fun i' => fresco (𝒮 S) b K (((ρ i') S b) f) N x) atTop (𝓝 (fresco (𝒮 S) b K ((M s S b) f) N x)):= ( (viewing _ _ _ N x).tendsto _).comp (funnel Y H s Q S b (tendsto_const_nhds (x:=f)))

include V d h
lemma synchronizes (f:Bazaar S b)(g:Bazaar T b)(u:fresco S b K f=fresco T b K g):
   fresco (𝒮 S) b K (M s S b f)=fresco (𝒮 T) b K (M s T b g):=by
 funext N x; apply tendsto_nhds_unique_of_eventuallyEq (pinpoint Y H s Q S b N x f) (pinpoint Y H s Q T b N x g)
 let U:=𝒮 S∪𝒮 T
 filter_upwards [planeSees Y H V s d Q h S b,planeSees Y H V s d Q h T b,(occupiedH Y H V d h).eventually (roomyTail Y H (s+1) U)] with i p q w
 exact congr_fun (congr_fun (exhibit_inj Y H (s+1) b U ((ι) i) ((plaid (𝒮 S) b K _).mono subset_union_left) ((plaid (𝒮 T) b K _).mono subset_union_right) (Roomy.seats w) ((p f).trans ((congrArg (fun v=> ascender Y s ((ι) i) ((μ) i) (exhibit Y H s ((ι) i) v)) u).trans (q g).symm))) N) x

lemma silhouette (f:Bazaar S b)(J':Finset Cover)(g:Bazaar J' b) (j:Axis)(z:ℤ)(w:fresco J' b K g=mirror K j z (fresco S b K f)):
   let T:=Λ.R.L.val*z
   fresco (𝒮 J') b K (M s J' b g)=mirror K j T (fresco (𝒮 S) b K (M s S b f)):=by
 intro T; funext N x
 let H':= pinpoint Y H s Q S b N (reflFields j T x) f
 apply tendsto_nhds_unique_of_eventuallyEq (pinpoint Y H s Q J' b N x g) (( (theta_cont (carR j T _)).tendsto _).comp H')
 let W':= (𝒮 J')∪ reflectedBox j T (𝒮 S)
 have hz(s n z)(f:Family K): exhibit Y H s n (mirror K j z f)=reflMark j z (exhibit Y H s n f):=displayRef ..
 filter_upwards [planeSees Y H V s d Q h J' b,planeSees Y H V s d Q h S b,h.eventually (d.finance (s+1)),(occupiedH Y H V d h).eventually (roomyTail Y H (s+1) W')] with i p q u v
 let a:= (ι) i; let t:= (μ) i
 let F':= fresco (𝒮 J') b K ((ρ i) J' b g); let G':= fresco (𝒮 S) b K ((ρ i) S b f)
 have ht: F'=mirror K j T G':= by
    apply exhibit_inj Y H (s+1) b W' a ((plaid ..).mono subset_union_left) ((axial K j T (plaid ..)).mono subset_union_right) (Roomy.seats v)
    have hx(p):=ascendTurnB Y s a t p j z ((exhibited Y H s a S (plaid S b K f)).mono (subset_univ _))
    change (exhibit Y H (s+1) ((ι) i)) (fresco (𝒮 J') b K ((ρ i) J' b g)) = exhibit Y H (s+1) ((ι) i) (mirror K j T (fresco (𝒮 S) b K ((ρ i) S b f)))
    rw [hz, p g, q f,w, hz]; exact hx ⟨u.depth,u.enters⟩
 exact congr_fun (congr_fun ht N) x

lemma tier_cost (x:Bazaar S false): fresco (𝒮 S) false K (M s S false x) = D s (fresco S false K x):=by
 let F:= fresco S false K x
 have hp(f:Family K)(t:InTest K true S false f)(n:Side)(y: Fields ((K).c n)): Tendsto (fun r=> Tower.block Y H s ((ι) r) ((μ) r) S f n y) atTop (𝓝 (D s f n y)):=by
    obtain ⟨C',b',p⟩:= d.implements s S
    obtain ⟨T,v⟩:= Journey.valuation Y H t
    let w:=max T 0+1; have hz:pay f w:= fun i y=> (v i y).trans ((le_max_left ..).trans (by dsimp [w]; linarith)); have ht:0<w:=by dsimp [w]; linarith [le_max_right T 0]
    apply Metric.tendsto_nhds.mpr; intro ε h0
    filter_upwards [h.eventually (p ((ε/2)/w) (by positivity))] with i q
    rw [dist_eq_norm]; exact ((q f t _ hz).2.2.1 n y|>.trans_eq (div_mul_cancel₀ _ ht.ne')).trans_lt (half_lt_self h0)
 funext N y; apply tendsto_nhds_unique_of_eventuallyEq (pinpoint Y H s Q S false N y x) (hp F (plaid S false K x) N y)
 filter_upwards [planeSees Y H V s d Q h S false, h.eventually (d.finance (s+1)),(occupiedH Y H V d h).eventually (turning Y H (s+1) (𝒮 S)),(occupiedH Y H V d h).eventually (roomyTail Y H (s+1) (𝒮 S))] with i p e z a
 have h' := (even_block Y H s S _ ((μ) i) (plaid S false K x) (show Satin.PairIdx Y s ((ι) i) ((μ) i) from ⟨e.depth,e.enters⟩) z)
 exact congr_fun (congr_fun (exhibit_inj Y H (s+1) false (𝒮 S) ((ι) i) (plaid ..) (booked ..) (Roomy.seats a) ((p x).trans h'.symm)) N) y

lemma enamored (f:Bazaar S b)(g:Bazaar T e)(U:Finset Cover)(x:Bazaar U (b.xor e)) (v:fresco U (b.xor e) K x=fresco S b K f*fresco T e K g)(q:∀ᶠ u in atTop,∀ i∈ Satin.region S (side Y u s),∀ j∈ Satin.region T (side Y u s),2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)<separation i j):
   fresco (𝒮 U) (b.xor e) K (M s U (b.xor e) x)=fresco (𝒮 S) b K (M s S b f)*fresco (𝒮 T) e K (M s T e g) :=by
 let W':=𝒮 U∪(𝒮 S ∪ 𝒮 T)
 let r:=occupiedH Y H V d h
 funext N z; apply tendsto_nhds_unique_of_eventuallyEq (pinpoint Y H s Q U (b.xor e) N z x) ((pinpoint Y H s Q S b N z f).mul (pinpoint Y H s Q T e N z g))
 filter_upwards [planeSees Y H V s d Q h S b, planeSees Y H V s d Q h T e, planeSees Y H V s d Q h U (b.xor e), r.eventually q, r.eventually (roomyTail Y H (s+1) W'), h.eventually (d.finance (s+1))] with i p t k he a z'
 have ht : fresco (𝒮 U) (b.xor e) K ((ρ i) U (b.xor e) x) = fresco (𝒮 S) b K ((ρ i) S b f)*fresco (𝒮 T) e K ((ρ i) T e g):=by
    apply exhibit_inj Y H (s+1) (b.xor e) W' ((ι) i) ((plaid ..).mono subset_union_left) ((((plaid (𝒮 S) b K _).mono subset_union_left).mul ((plaid (𝒮 T) e K _).mono subset_union_right)).mono subset_union_right) (Roomy.seats a)
    rw [k x, actual_product, p f, t g,v,actual_product]
    exact ascendSepB Y s ((ι) i) _ ⟨z'.depth,z'.enters⟩ (bazAtSafe Y H s b S _ f) (bazAtSafe Y H s e T _ g) he
 exact congr_fun (congr_fun ht N) z

lemma charges_survive (f g:Bazaar S b) (U: Cover→ SU.E) (x:Circular S (parentGauge Λ U) (fresco S b K f) (fresco S b K g)):
   Circular (𝒮 S) U (fresco (𝒮 S) b K (M s S b f)) (fresco (𝒮 S) b K (M s S b g)):=by
 let O:=𝒮 S
 have HP:∀ᶠ i in atTop, Circular O U (fresco O b K ((ρ i) S b f)) (fresco O b K ((ρ i) S b g)):=by
   filter_upwards [planeSees Y H V s d Q h S b, h.eventually (d.finance (s+1)),(occupiedH Y H V d h).eventually (roomyTail Y H (s+1) O)] with i p e z
   let o:= (ι) i; let t:= (μ) i
   let F:=fresco O b K ((ρ i) S b f); let G:=fresco O b K ((ρ i) S b g)
   obtain ⟨φ,T⟩:= scoreTrace U (Roomy.seats z)
   obtain ⟨Wx,hw,c⟩:= reColor U (plaid O b K ((ρ i) S b f))
   suffices h: Wx=G by rw [h] at c; exact c
   have ht:= truePrinting O U Y H (s+1) o c T
   have hp:=truePrinting S (parentGauge Λ U) Y H s o x (hierarchyTrace S U Y s o φ T)
   have hx:Harmony φ (exhibit Y H (s+1) o F) (exhibit Y H (s+1) o G):=by
      unfold F G o O; rw [p f,p g]; exact ascendHarmony Y s o t ⟨e.depth,e.enters⟩ (bazAtSafe Y H s b S _ g) φ (bazAtSafe Y H s b S _ f).env hp
   exact exhibit_inj Y H (s+1) b O o hw (plaid ..) (Roomy.seats z) (funext fun i=> (twist _).injective ((ht i).symm.trans (hx i)))
 intro n φ P x; exact tendsto_nhds_unique_of_eventuallyEq (pinpoint Y H s Q S b n (simultaneous φ x) f) (((breeze (quantU (tradew _ φ))).tendsto _).comp (pinpoint Y H s Q S b n x g)) (HP.mono fun i h=> h n φ P x)
end rich
end YM.CF.Buffered.Afterglow.Tower.One
