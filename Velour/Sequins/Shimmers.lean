import Velour.Sequins.Pearl
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

open YM.Velour

local notation "Ⓟ"=> Vantage
local notation "ℓ"=> reviewEarlierBox.invites
local notation "Ⓡ"=> reviewLaterBox.invites
abbrev Sighting:= SampleDose→ SampleDose→ℕ→ℕ→ CrossRead
variable (s:ℕ→ℕ) -- stage attained
variable (f:Sighting) -- literal signal
abbrev Eye(F U:SampleDose):Prop:=tsupport F.val⊆ℓ ∧ tsupport U.val⊆Ⓡ
def Beckon (m:SampleDose→SampleDose→CrossRead)(p:Ⓟ→CrossRead):Prop:=
 (∀ (F U:SampleDose), Eye F U → ∀ g:ℕ→ℕ, (∀ᶠ i in atTop,s i≤g i) →
             Tendsto (fun i=> f F U i (g i)) atTop (𝓝 (m F U))) ∧
 ∀ a∈ℓ,∀ b∈Ⓡ, Tendsto (fun i=> m (velourSampleBead a i) (velourSampleBead b i)) atTop (𝓝 (p (b-a)))
abbrev SightLine:= Ⓟ→ℂ→ CrossRead
abbrev nudge(b:Ⓟ)(r:ℝ):Ⓟ:= b+foldSpace (r • basis 3)

def Streams(p:Ⓟ→CrossRead)(q:SightLine):Prop:=
 ∀ a∈ℓ, ∀ b∈Ⓡ,
  (∀ i j, AnalyticOnNhd ℂ (fun z=>q (b-a) z i j) {z:ℂ | 0<z.im}) ∧
   -- all small Eu probes. z.im *total* gap, z.re real time.
  ∀ᶠ r:ℝ in 𝓝 0, q (b-a) (((b-a) 3+r:ℝ)*Complex.I)=p (nudge b r-a)

abbrev aim(u:Ⓟ)(t:ℝ):ℂ:=(u 3:ℝ)+(t:ℂ)*Complex.I
def rinse_LocalFieldBounds(F U:SampleDose)(q:SightLine)(t:ℝ): CrossRead:=
 Matrix.of fun i j=> ∫a:Ⓟ,∫b:Ⓟ, (F.val a:ℂ)*(U.val b:ℂ)*q (b-a) (aim (b-a) t) i j

/-- Continue the prices supplied by the EU experiment (on this pair of boxes). 
Basis is the literal Eu readings; no price rotation for fields stipulated. -/
def Shimmers (F U:SampleDose)(eu real:CrossRead):Prop:=
 Eye F U ∧ ∃m p q,
   eu=m F U ∧ Beckon s f m p ∧ Streams p q ∧
      -- explicit absolute convergence at all positive padding, then approach (real clocks).
      (∀ (i j:Lead.Clan)(t:ℝ),0<t → Integrable
        (uncurry fun a b:Ⓟ=> (F.val a:ℂ)*(U.val b:ℂ)*q (b-a) (aim (b-a) t) i j)
          (volume.prod volume)) ∧
      Tendsto (rinse_LocalFieldBounds F U q) (𝓝[>]0) (𝓝 real)

lemma streams_unique {p p':Ⓟ→CrossRead}{q q':SightLine}
 (h:∀a∈ℓ,∀ b∈Ⓡ,p (b-a)=p' (b-a))(g:Streams p q)(g':Streams p' q')
 {a b:Ⓟ}(u:a∈ℓ)(v:b∈Ⓡ) {z:ℂ}(t:0<z.im): q (b-a) z=q' (b-a) z:=by
 let F(r:ℝ):=((b-a) 3+r:ℝ)*Complex.I
 -- ℂ? type inferred? Complex multiplication, implicit
 have hx:Continuous F:=by unfold F; fun_prop
 have w:0<(F 0).im:=by
   suffices 0<(b-a) 3 from by simpa [F,Pi.sub_apply] using this
   exact sub_pos.mpr ((show a 3< -1 from (u 3 (mem_univ _)).2).trans
     ((show (-1:ℝ)<1 by norm_num).trans (v 3 (mem_univ _)).1))
 have e:Tendsto F (𝓝[≠](0:ℝ)) (𝓝[≠] (F 0)):=by
   refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ((hx.tendsto _).mono_left nhdsWithin_le_nhds) ?_
   filter_upwards [eventually_mem_nhdsWithin] with r l j
   have p:=congrArg Complex.im j; simp [F] at p; exact l p
 have i: Tendsto (nudge b) (𝓝 0) (𝓝 b):=
   by simpa [nudge] using ((show Continuous (nudge b) by unfold nudge; fun_prop).tendsto 0) -- ▸ rewrites b?

 obtain ⟨d,m⟩:=g _ u _ v
 obtain ⟨d',m'⟩:=g' _ u _ v
 have I:∀ᶠ r:ℝ in 𝓝 0, q (b-a) (F r)=q' (b-a) (F r):=by
   filter_upwards [m,m',i.eventually (reviewLaterBox.doorOpen.mem_nhds v)] with r h₁ h₂ h₃
   exact (h₁.trans (h _ u _ h₃)).trans h₂.symm
 ext1 i j
 refine ((d i j).eqOn_of_preconnected_of_frequently_eq (d' i j)
   (convex_halfSpace_im_gt _).isPreconnected w ?_) t
 exact e.frequently (((I.filter_mono nhdsWithin_le_nhds).mono
     fun r y=> congrArg (fun m=>m i j) y).frequently)

lemma shimmers_unique {F U:SampleDose}{m n m' n':CrossRead}
 (v:Shimmers s f F U m n)(w:Shimmers s f F U m' n'):
 m=m' ∧ n=n':=by
 obtain ⟨e,M,p,q,rfl,⟨a,b⟩,c,_,d⟩:=v
 obtain ⟨_,M',p',q',rfl,⟨a',b'⟩,c',_,d'⟩:=w
 have r(i j:SampleDose)(k:Eye i j):M i j=M' i j:=by
   have l:∀ᶠ i in atTop,s i≤ s i:= .of_forall fun _=> le_rfl
   exact tendsto_nhds_unique (a i j k _ l) (a' i j k _ l)
 have h:∀i∈ℓ,∀ j∈Ⓡ,p (j-i)=p' (j-i):=by

   intro i y j x
   refine tendsto_nhds_unique_of_eventuallyEq (b _ y _ x) (b' _ y _ x) ?_
   filter_upwards [concentrates i _ (reviewEarlierBox.doorOpen.mem_nhds y),
       concentrates j _ (reviewLaterBox.doorOpen.mem_nhds x)] with z g l
   exact r _ _ ⟨g,l⟩
 refine ⟨r _ _ e,tendsto_nhds_unique_of_eventuallyEq d d' ?_⟩
 filter_upwards [eventually_mem_nhdsWithin] with k tk
 ext1 i j
 simp only [rinse_LocalFieldBounds,Matrix.of_apply]
 exact integral_congr_ae (.of_forall fun y=> integral_congr_ae (.of_forall fun x=> by
   by_cases l:F.val y=0; · simp [l]
   by_cases m:U.val x=0; · simp [m]
   dsimp only
   rw [streams_unique h c c' (e.1 (subset_closure l)) (e.2 (subset_closure m))
     (show 0<(aim (x-y) k).im by simpa [aim] using (show 0<k from tk))]))



variable {P:Spine}{K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}
local notation "ξ"=> P.advocate 3 x 3
local notation "ω"=> P.colorZero 3 ξ
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "ℋ"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ℰ"=> P.seasons 3 ξ
local notation "C"=> Lead.Clan
variable {R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}{A:ℕ→P.Apron}{n:ℕ→ℕ}{w:C→Prism}
    {V: ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)}
    {g h : ℕ} {X : P.HandleWith x c r A n}
variable {realY : C → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)}{Z:C→C→Boundary.Distn E4}
local notation "𝓕₄"=> M4Furnish P K c r x R i₀ F U A n w V g h X realY Z
local notation "𝓑"=> P.Bobbin 3 ξ
local notation "D"=> (ℰ).muslin
local notation "Ω"=> P.firstTulle 3 ξ
local notation "θ"=> P.detects 3 ξ
local notation "Q"=> P.bobQuote 3 ξ
local notation "γ"=> P.ThinVelour x A c r n w
local notation "Λ"=> P.profilesZ x V w

variable (P x V w)
def spray (d:Vantage)(z:ℂ):CrossRead:=Matrix.of fun i j=> paintedFrom (ℰ) (Λ i) (Λ j) (polarBase d) z
local notation "L"=> P.spray x w V
local notation "M"=> (ℰ).unit.translation
variable (i j:C)(a b:Vantage)(F U)(t:ℝ)
local notation "J" i:max b:max => M (foldSpace.symm b) (Λ i (t/2))
local notation "Xv" F:max i:max b:max=> ((F).val b:ℂ) • J i b

lemma spray_price: L (b-a) (aim (b-a) t) i j=inner ℂ (J i a) (J j b):=by
 rw [←ContinuousLinearMap.adjoint_inner_right]
 change _ =inner ℂ _ (star (M _) (J j b))
 rw [(ℰ).unit_star,←mul_apply_eq_comp,(ℰ).unit_step]
 have e:(aim (b-a) t).im=t:=by simp [aim]
 have r:(aim (b-a) t).re=(b-a) 3:=by simp [aim]
 rw [spray,Matrix.of_apply]
 rw [paintedFrom,separationPrice,e,r,←skew_axis,sub_add_cancel,map_sub,sub_eq_neg_add]

private lemma disperse: (F.val a:ℂ)*(U.val b:ℂ)*L (b-a) (aim (b-a) t) i j = inner ℂ (Xv F i a) (Xv U j b):=by
 rw [P.spray_price,inner_smul_left, inner_smul_right,starRingEnd_apply]
 simp [mul_assoc]

private lemma dewspray:Integrable (fun a=>Xv F i a) ∧ Continuous (fun a=>Xv F i a):=by
  have e:Continuous (fun a=>Xv F i a):=(Complex.continuous_ofReal.comp F.smooth.continuous).smul (((ℰ).unit.moves (Λ i (t/2))).comp foldSpace.symm.continuous)
  refine ⟨e.integrable_of_hasCompactSupport ((F.budget.comp_left Complex.ofReal_zero).smul_right),e⟩
lemma spray_cost:
 Integrable
        (uncurry fun a b:Ⓟ=> (F.val a:ℂ)*(U.val b:ℂ)*L (b-a) (aim (b-a) t) i j)
          (volume.prod volume):=by
 have u:=P.dewspray x F w V i t
 have v:=P.dewspray x U w V j t
 simp_rw [P.disperse]
 exact (u.1.norm.mul_prod v.1.norm).mono'
    (((u.2.comp continuous_fst).inner (𝕜:=ℂ) (v.2.comp continuous_snd)).aestronglyMeasurable)
    (ae_of_all _ fun _=>norm_inner_le_norm ..)
lemma spray_dissolve:
  rinse_LocalFieldBounds F U L t i j=
    inner ℂ (collect (ℰ) (sachet_LocalFieldBounds F) (Λ i (t/2))) (collect (ℰ) (sachet_LocalFieldBounds U) (Λ j (t/2))):= by
 have u:=P.dewspray x F w V i t;have v:=P.dewspray x U w V j t
 simp_rw [collect_eq,integral_sachet]
 unfold rinse_LocalFieldBounds; rw [Matrix.of_apply]
 simp_rw [P.disperse]
 let Z:= (∫b,Xv U j b)
 calc
   _ = ∫a, inner ℂ (Xv F i a) Z:= integral_congr_ae (.of_forall fun a=> integral_inner v.1 _)
   _ = inner ℂ (∫a,Xv F i a) Z:=by 
        conv_lhs=> arg 2; ext; rw [←inner_conj_symm]
        rw [integral_conj, integral_inner u.1,inner_conj_symm]
   _ = _:=rfl


variable {P x V w F U}
namespace M4Furnish
variable (u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z)
include u
lemma spray_streams : Streams (P.pointPrism x V w) L:=by
  intro α j β k
  refine ⟨fun v y =>u.boundary.loft v y (polarBase _),?_⟩
  have e:Tendsto (nudge β) (𝓝 0) (𝓝 β):=by simpa [nudge] using
     ((show Continuous (nudge β) by unfold nudge; fun_prop).tendsto (0:ℝ))
  filter_upwards [e.eventually (reviewLaterBox.doorOpen.mem_nhds k)] with d y
  let q:=nudge β d-α
  have t:0<q 3:=sub_pos.mpr
     (((show α 3< -1 from (j _ (mem_univ _)).2).trans (by norm_num : (-1:ℝ)<1)).trans
       (show 1<nudge β d 3 from (y _ (mem_univ _)).1))
  have t₁:q 3=(β-α) 3+d:=by
    dsimp only [q,nudge,Pi.sub_apply,Pi.add_apply]
    have g:(foldSpace (d • basis 3)) 3=d:= by simp [foldSpace,basis]
    rw [g]; abel
  have k':polarBase (β-α)=polarBase q:=by
    simp only [←skew_axis,t₁,add_smul] -- handles correction
    dsimp only [q,nudge]
    rw [map_sub,map_sub,map_add,ContinuousLinearEquiv.symm_apply_apply]
    abel
  ext1 i j
  unfold spray; rw [Matrix.of_apply,k',←t₁]; exact u.boundary.point i j _ t

/-- Criterion directly on EU measurements in the neighbourhood -/
lemma achieved (b:Beckon s f (P.readPrism x V w 1) (P.pointPrism x V w)):
 Shimmers s f F U (P.readPrism x V w 1 F U) (paycheck realY F U):=by
 refine ⟨⟨u.boxF,u.boxU⟩,_,_,_,rfl,b,spray_streams u,fun _ _ _ _=>spray_cost ..,?_⟩
 have p:Tendsto (fun t:ℝ=>t/2) (𝓝[>]0) (𝓝[>]0):=by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
       (eventually_mem_nhdsWithin.mono fun y g=>half_pos (show (0:ℝ)<y from g))
    exact (by simpa using (((show Continuous (fun t:ℝ=>t/2) by fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))))
 refine tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr fun j=>?_ )
 simp_rw [P.spray_dissolve,collect_eq]
 exact (((u.boundary.boundary i (sachet_LocalFieldBounds F)).2.comp p).inner
        ((u.boundary.boundary j (sachet_LocalFieldBounds U)).2.comp p))
#print axioms achieved
end M4Furnish
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

