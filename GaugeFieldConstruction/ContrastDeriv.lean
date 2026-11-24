import GaugeFieldConstruction.SymposiumΛL
/-!
# Identification of derivative fields and their W-order pricing

Closed under *iterated* real Mink direction derivatives and linear combinations. Real edge
sweeps use UP directions in absolute coordinates (may hold several spectators at once). Costs
on an arbitrary open box of **real** configurations determine the whole tube kernel. In
particular there is neither a Mink diagonal/contact ambiguity for these tests, nor any loss
of nonvanishing by taking the boundary `𝓝[east n] 0`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.NSF.Boundary.WOrder
open YM.Boundary Function Filter Set Mink MeasureTheory Analysis Kernel Complex Metric Distribution
open scoped BigOperators Topology ContDiff InnerProductSpace
variable {n:ℕ}
local notation3 "CUP" => ({z:ℂ|0≤z.im}: Set ℂ)
local notation3 "HUP" => ({z:ℂ|0<z.im}: Set ℂ)

/-- Physical reading relation. `pricedCorner` is mandatory (all strict heights tend to 0,
    weak by compact tests). Extra directions compare to Mink edge. -/
structure Carries (w:Full n→ℂ) (X:Distn (Points n)):Prop where
  hol : AnalyticOnNhd ℂ w (tube n)
  pricedCorner (f:Joint n)(h:HasCompactSupport (f:Points n→ℂ)) : Tendsto
    (fun y:Heights n=> ∫ x:Points n,w (glow x (dawn y))* f x) (𝓝[east n] 0) (𝓝 (X f))
  line (f:Joint n)(h:HasCompactSupport (f:Points n→ℂ)) {v: Points n}(hv: v∈fields n) :
    ∃ F:ℂ→ℂ, ContinuousOn F CUP ∧ AnalyticOnNhd ℂ F HUP ∧
      (∀ r:ℝ,F (r:ℂ) = X (Probe.ahead (r • v) f)) ∧
      ∀ z:ℂ,z∈HUP→ F z = ∫ x:Points n,w (HullWrapΛL v x z)*f x

section
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{D:∀ i,Blanket i}
variable {F:Waves S}{A:Y.Aurora D}
variable (e:A.FullBody F)(hA:Bid.cones Y) (p:F.NonTangentialFree Y)
include e hA p
lemma Carries_W (V:Fin n→ S.Union) : Carries (A.emit V) (Y.W n V) where
  hol := e.hol n V
  pricedCorner f _ := by
    apply Tendsto.congr' _ (p.corner n V f)
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp_rw [e.pure n V _ _ hy]
  line f h v hv :=
    ⟨LiftBeforeΛL (D n) (Y.W n V) f v, VBefΛL (D n) (Y.W n V) f hv,
     analyticBeforeΛL e f h hv V, (fun r=> by
      simp only [LiftBeforeΛL,HullAheadΛL,ofReal_im,ofReal_re,zero_smul,
          (D n).flatD (Work.C12.answer _ (Work.C10.answer n) _) (hA n V)]),
     ΦPriceΛL e f hv V⟩
end
variable {w l:Full n→ℂ} {X Y:Distn (Points n)} (a:Carries w X)(b:Carries l Y)
local notation "⊖" X:max "on" d:max => -(X ∘L DriftΛL d)
lemma ahead_d (d t:Points n)(f:Joint n) : Probe.ahead t (DriftΛL d f)= DriftΛL d (Probe.ahead t f) := by
 ext1 x; rw [Probe.ahead_at, DriftΛKnownL,DriftΛKnownL]
 have hf: ⇑(Probe.ahead t f)= fun x:Points n=> f (x-t) :=rfl
 rw [hf, fderiv_comp_sub]
include a
lemma Carries.mink (d:Points n): Carries (MintSpΛ w d) (⊖ X on d) := by
 constructor
 · intro z hz
   exact ((ContinuousLinearMap.apply ℂ ℂ (penΛ n d)).analyticAt _).comp ((a.hol z hz).fderiv)
 · intro f h; let M:=DriftΛL d f
   have ha: HasCompactSupport (M:Points n→ℂ) := h.mono' (Set.Subset.trans (subset_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset d f))
   refine Tendsto.congr' ?_ (Tendsto.neg (a.pricedCorner M ha))
   filter_upwards [self_mem_nhdsWithin] with i hi
   exact (FeeΛSpL (etched hi) w a.hol f d h).symm
 intro f h v hv; let M:=DriftΛL d f
 have ha: HasCompactSupport (M:Points n→ℂ) := h.mono' (Set.Subset.trans (subset_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset d f))
 obtain ⟨F,H,u,l,k⟩:=a.line M ha hv
 refine ⟨-F,H.neg,u.neg,?_,?_⟩
 · intro r; rw [Pi.neg_apply,l]; change -X _ = -X (DriftΛL d (Probe.ahead (r • v) f)); rw [show Probe.ahead (r • v) M=_ from ahead_d ..]
 intro z hz; rw [Pi.neg_apply,k z hz]; let i:= z.im • v; let j:= z.re • v
 let p:= Probe.ahead j f; let q:= Probe.ahead j M
 have eq (f:Joint n)(w:Full n→ℂ): (∫ x:Points n,w (HullWrapΛL v x z)*f x) = ∫ x:Points n,w (glow x i)* Probe.ahead j f x:= by
    rw [← integral_add_right_eq_self (fun x:Points n=> w (glow x i)* Probe.ahead j f x) j]
    simp only [HullWrapΛL,Probe.ahead_at,add_sub_cancel_right]; rfl
 rw [eq, eq]; unfold M; rw [ahead_d]; exact (FeeΛSpL (upStretchΛL hv _ (show 0<z.im from hz)) w a.hol p d (AheadSmΛL f h _)).symm

/-- Wick stripe accounting for compact probes -/
lemma Carries.stripe {y:Points n}(hy:y∈fields n)(t:Points n)(f:Joint n)
    (h:HasCompactSupport (f:Points n→ℂ)): Integrable (fun x:Points n=>w (glow (x+t) y)*f x) := by
 have hz: Continuous fun x:Points n=> w (glow (x+t) y):=(continuous_iff_continuousAt.mpr fun x=> (phiFΛ hy w a.hol (x+t)).continuousAt.comp (f:=fun x:Points n=>x+t) (continuous_id.add continuous_const).continuousAt)
 exact (hz.mul f.continuous).integrable_of_hasCompactSupport h.mul_left
lemma Carries.two (f:Joint n)(h:HasCompactSupport (f:Points n→ℂ)){y:Points n}(hy:y∈fields n): Integrable (fun x:Points n=>w (glow x y)*f x):=by simpa using a.stripe hy 0 f h
include b
lemma Carries.sum : Carries (w+l) (X+Y) := by
 constructor
 · exact a.hol.add b.hol
 · intro f h; apply Tendsto.congr' _ ((a.pricedCorner f h).add (b.pricedCorner f h))
   filter_upwards [self_mem_nhdsWithin] with i hi; simp only [Pi.add_apply,add_mul]; rw [integral_add (a.two f h (etched hi)) (b.two f h (etched hi))]
 intro f h v hv; obtain ⟨F,r,x,k,u⟩:=a.line f h hv; obtain ⟨G,w',l',K,p⟩:=b.line f h hv
 refine ⟨F+G,r.add w',x.add l',fun v=>by simp [k,K],?_⟩
 intro z hz
 simp only [Pi.add_apply,add_mul]
 rw [u z hz,p z hz]
 exact (integral_add (a.stripe (upStretchΛL hv _ (show 0<z.im from hz)) (z.re • v) f h) (b.stripe (upStretchΛL hv _ (show 0<z.im from hz)) (z.re • v) f h)).symm
omit b
lemma Carries.scale (c:ℂ) : Carries (c • w) (c • X) := by
 constructor
 · exact analyticOnNhd_const.mul a.hol
 · intro f h; apply Tendsto.congr' _ ((tendsto_const_nhds (x:=c)).mul (a.pricedCorner f h))
   filter_upwards [self_mem_nhdsWithin] with i hi; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
 intro f h v hv; obtain ⟨F,r,x,k,u⟩:=a.line f h hv; refine ⟨c • F,continuousOn_const.mul r,analyticOnNhd_const.mul x,fun v=>by simp[k],?_⟩
 intro z hz; simp only [Pi.smul_apply,smul_eq_mul, mul_assoc,u z hz,integral_const_mul]
omit a in
lemma Carries.ze : Carries (0:Full n→ℂ) 0 where
 hol := analyticOnNhd_const
 pricedCorner _ _ := by simpa using (tendsto_const_nhds (x:=(0:ℂ)))
 line _ _ _ _ := ⟨0,continuousOn_const,analyticOnNhd_const,fun _=> rfl,fun _ _=> by simp⟩
omit a in
lemma Carries.many {ι:Type*} (v:Finset ι){w:ι→Full n→ℂ}{X:ι→Distn (Points n)}
    (h:∀ i∈ v,Carries (w i) (X i)): Carries (∑ i∈v,w i) (∑ i∈v,X i):= by
 classical
 induction v using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact Carries.ze
 | insert i s k e=> rw [Finset.sum_insert k,Finset.sum_insert k]; exact (h i (Finset.mem_insert_self ..)).sum (e fun i p=> h i (Finset.mem_insert_of_mem p))

lemma vane_of (Z:Distn (Points n)) (U:Set (Points n)) (u:IsOpen U) (W:IsVanishingOn Z U)
    {v:Points n} (hv:v∈fields n) (t:ℝ) (h:Z=X): IsVanishingOn Z (terrainΛL (t • v) U):= by
 subst Z; apply (Distn.from_compact X).2; intro f W' hc
 let k:=t • v; let g:= Probe.ahead (-k) f
 have he: Probe.ahead k g=f:= AheadBabyΛL ..; have hk: HasCompactSupport (g:Points n→ℂ):= AheadSmΛL f hc _
 obtain ⟨F,H,x,l,-⟩:=a.line g hk hv
 have hU:tsupport g⊆U:= by
    intro i p; have ht:= W' (show i- -k∈ tsupport f from AheadWildΛL f _ p); change i- -k-k∈U at ht; simpa using ht
 have he': F ∘ ofReal =ᶠ[𝓝 0] 0:= by
    let f(x:ℝ×Points n):= x.2+x.1 • v
    have hw:∀ᶠ r in 𝓝 (0:ℝ),∀ j∈tsupport g,f (r,j)∈U :=hk.eventually_forall_of_forall_eventually (fun i hi=> (u.preimage (show Continuous f from continuous_snd.add (continuous_fst.smul continuous_const))).mem_nhds (show (0,i) ∈ f⁻¹' U from show i+(0:ℝ) • v∈U from by simpa using hU hi))
    filter_upwards [hw] with r hr; change F (r:ℂ)=0; rw [l]; apply W; intro i hi; have hf:=hr (i-r • v) (AheadWildΛL g _ hi); change _+ r • v∈U at hf; simpa using hf
 rw [← he,←l]; exact SweepΛL H x he' (show (t:ℂ)∈CUP from by simp)

lemma world_vanish (U:Set (Points n)) (u:IsOpen U) (p:U.Nonempty) (W:IsVanishingOn X U) : X=0 := by
 have he:∀ x:Points n,IsVanishingOn X (terrainΛL x U):= by
    intro x; let b:Points n:= dawn (rate n); have hb:b∈fields n:= etched ΛProfileL
    have he:Continuous (fun t:ℝ=> b+t • x):=continuous_const.add (continuous_id.smul continuous_const)
    have h:∀ᶠ t in 𝓝[>] (0:ℝ), b+t • x∈fields n:= ((he.continuousAt.tendsto (x:=0)).mono_left nhdsWithin_le_nhds).eventually ((smooth_fields n).mem_nhds (show b + (0:ℝ) • x ∈ fields n from by simpa using hb))
    obtain ⟨t,r,H⟩:= (h.and self_mem_nhdsWithin).exists
    have hx:t≠0:=(show 0<t from H).ne'; let i:=(-t⁻¹) • b; let j:=t⁻¹ • (b+t • x); have hz:j+i=x:=by unfold j i; rw [smul_add,smul_smul,inv_mul_cancel₀ hx,one_smul,neg_smul]; abel
    rw [show terrainΛL x U=terrainΛL j (terrainΛL i U) from ?_]; exact vane_of a _ _ (OpenTerrainΛL i U u) (vane_of a X U u W hb _ rfl) r t⁻¹ rfl
    ext c; change c-x∈ U ↔ c-j-i∈U; rw [sub_sub,hz]
 obtain ⟨x,r⟩:=p
 have hs: dsupport X⊆∅:= by
    intro l hp; have hu:l∈terrainΛL (l-x) U:=by change l - (l-x)∈ U; simpa using r
    exact absurd (he (l-x)) ((mem_dsupport_iff_not_isVanishingOn l).mp hp _ hu (OpenTerrainΛL _ _ u))
 have hu:=(Distn.due X ∅ isClosed_empty).1 hs
 ext1 i; exact hu i (by simp)
open Probe
/-- The price on finite products of LOCAL compactly supported Schwartz data can determine
    a Carries distribution. This is truly an n-box (can choose pairwise separated). -/
theorem productDetermine (W:Fin n→Set E4)(h:∀ i,IsOpen (W i))(q:∀ i,(W i).Nonempty)
    (t:∀ (f:Fin n→ Test4), (∀ i, tsupport (f i)⊆ W i ∧ HasCompactSupport ⇑(f i)) → X (Joint.materialize n f)=0): X=0:= by
 choose f U w z hU qU tU using fun i=> WrapUnitΛL (W i) (h i) (q i)
 let P := ⋂ i:Fin n,(fun x:Points n=> x i)⁻¹' U i
 have hp:P.Nonempty:=by choose x hx using qU; exact ⟨points x, mem_iInter.mpr fun i=> hx i⟩
 let J:=Joint.materialize n f; let Y:= X.comp (Probe.sew J); have hg: Y=0:=by
    have he(g:Fin n→ Test4): sew J (Joint.materialize n g)=Joint.materialize n fun i=> sew (f i) (g i):=by
       ext1 x; simp only[sews,J,Joint.material_at,Finset.prod_mul_distrib]
    have ht: Submodule.span ℂ (range (Joint.materialize n)) ≤ (Y.toLinearMap).ker:= by
       apply Submodule.span_le.mpr; rintro _ ⟨v,rfl⟩; change X (sew _ (Joint.materialize n _))=0; rw[he]
       have hq(i:Fin n):tsupport (sew (f i) (v i))⊆ tsupport (f i):= (shrinks ..).trans inter_subset_left
       exact t _ (fun i=>⟨(hq i).trans (z i),(w i).of_isClosed_subset (isClosed_tsupport _) (hq i)⟩)
    ext1 i; exact Submodule.topologicalClosure_minimal _ ht Y.isClosed_ker (Work.C25.answer n |>.symm ▸ (show i∈ (⊤:Submodule ℂ (Joint n)) from trivial))
 apply world_vanish a P (isOpen_iInter_of_finite fun i=> (hU i).preimage (by fun_prop)) hp
 intro b hB; have hyp:Y b=0:=by rw[hg]; rfl
 have hy: sew J b=b:=by
    ext1 i; rw[sews]; by_cases e:i∈tsupport b
    · have he:J i=1:= by
         unfold J; rw [Joint.material_at]; exact Finset.prod_eq_one fun a _=> tU a (mem_iInter.mp (hB e) a)
      simp [he]
    rw [show b i=0 from image_eq_zero_of_notMem_tsupport e,mul_zero]
 change X (sew J b)=0 at hyp; rwa [hy] at hyp

lemma from_front (he:X=0) : EqOn w 0 (tube n) := by
 have he (y:Points n)(p:y∈ fields n): emberΛ (y:=y) w=0:= by
    have hc:Continuous (emberΛ (y:=y) w):=continuous_iff_continuousAt.mpr (fun x=> (phiFΛ p w a.hol x).continuousAt)
    refine MeasureTheory.Measure.eq_of_ae_eq (μ:=volume) ?_ hc continuous_const
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable ?_
    intro g hg k
    have hx:HasCompactSupport (fun x:Points n=> (g x:ℂ)):= k.comp_left (g:= ofReal) (by simp)
    let f:=hx.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg); have h: HasCompactSupport (f:Points n→ℂ) := hx
    obtain ⟨F,W,V,M,q⟩:=a.line f h p
    have he: F I=0:= SweepΛL W V (Eventually.of_forall (fun r:ℝ=> (M r).trans (by rw [he]; rfl))) (show I∈CUP from by simp)
    rw [q I (show I∈HUP from by simp)] at he
    have hf(x:Points n):g x • emberΛ (y:=y) w x=w (HullWrapΛL y x I) * f x:= by
       simp only[HullWrapΛL,I_im,I_re,one_smul,zero_smul,add_zero]; change (_:ℝ) • w _= _ * ((g x:ℝ):ℂ)
       rw [mul_comm,Complex.real_smul]
    simp_rw [hf]; exact he
 intro z hz
 rw [← valley z]; exact congrFun (he (shade z) hz) (reality z)
lemma from_tube (he:EqOn w 0 (tube n)) : X = 0 := by
 have he (f:Joint n) (h:HasCompactSupport (f:Points n→ℂ)) : X f=0 := by
    haveI:= awaits (light n)
    refine tendsto_nhds_unique_of_eventuallyEq (a.pricedCorner f h) tendsto_const_nhds ?_
    filter_upwards [self_mem_nhdsWithin] with t q
    have h0(i:Points n) : w (glow i (dawn t))=0:= he (roseΛ (etched q) _)
    simp_rw [h0]; simp
 ext1 f
 have hx:= Probe.persistent f; exact tendsto_nhds_unique_of_eventuallyEq ((X.continuous.tendsto f).comp hx) tendsto_const_nhds (Eventually.of_forall (fun i=>he _ (Probe.finite_cap i)))

include b
theorem tube_contrast : EqOn w l (tube n) ↔ X=Y:= by
 have hp: Carries (w-l) (X-Y):=by
   have hz:(-1:ℂ) • Y= -Y:= by ext1 i; simp
   simpa [sub_eq_add_neg,hz] using a.sum (b.scale (-1))
 constructor
 · intro h; exact sub_eq_zero.mp (from_tube hp (fun x hz=> sub_eq_zero.mpr (h hz)))
 intro p; exact fun i h=> sub_eq_zero.mp (from_front hp (sub_eq_zero.mpr p) h)

#print axioms Carries_W
#print axioms Carries.mink
#print axioms Carries.many
#print axioms productDetermine
#print axioms tube_contrast
end YM.NSF.Boundary.WOrder
end
