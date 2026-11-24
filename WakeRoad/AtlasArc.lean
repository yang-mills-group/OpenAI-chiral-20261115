import WakeRoad.ArcSeam
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe
namespace Spine.NativeSeam
open YM.OS YM.OS.Semigroup SatinRegistration YM.Velour YM.SatinMacro
variable (P:Spine)(x:P.Spectrum0 3)
local notation "jₓ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x jₓ
local notation "G"=> P.ManyF jₓ ξ
local notation "ℰ"=> P.seasons jₓ ξ
local notation "Ω"=> P.heaven jₓ ξ
local notation "W"=>carry P x
local notation "T"=>(ℰ).E
variable (B D:P.Apron)
-- want geometry qualification also on all aperture extents in **spacetime** and positive wall strict
variable {p q:Vantage}
def Cracks (p q:Vantage):Prop:=
   p jₓ+B.realWidth P jₓ<0∧ D.realWidth P jₓ<q jₓ ∧
   (∀ i:Axis,p i+B.realWidth P i<q i-D.realWidth P i) ∧ q jₓ + D.realWidth P jₓ - (p jₓ-B.realWidth P jₓ) < q (0:Axis) - D.realWidth P (0:Axis)-(p (0:Axis)+B.realWidth P (0:Axis))
lemma cracked (h:Cracks P B D p q): ∀ᶠ y:Vantage×Vantage in 𝓝 (p,q), Cracks P B D y.1 y.2:=by
 let A(i:Axis):Vantage×Vantage→ℝ:=fun y=>y.1 i; let Nv (i:Axis):Vantage×Vantage→ℝ:=fun y=> y.2 i
 have ha(i):Continuous (A i):=by unfold A; fun_prop
 have hb(i):Continuous (Nv i):=by unfold Nv; fun_prop
 let F(i):= B.realWidth P i; let V(i):= D.realWidth P i
 apply ((((ha jₓ).add continuous_const).continuousAt.tendsto.eventually_lt tendsto_const_nhds h.1).and _)
 refine (tendsto_const_nhds.eventually_lt (hb jₓ).continuousAt.tendsto h.2.1).and ?_
 refine (eventually_all.mpr (show ∀ i:Axis,∀ᶠ y in 𝓝 (p,q), A i y+ F i<Nv i y-V i from fun i=> ((ha i).add continuous_const).continuousAt.tendsto.eventually_lt ((hb i).sub continuous_const).continuousAt.tendsto (h.2.2.1 i))).and ?_
 exact (((hb jₓ).add continuous_const).sub ((ha jₓ).sub continuous_const)).continuousAt.tendsto.eventually_lt (((hb 0).sub continuous_const).sub ((ha 0).add continuous_const)).continuousAt.tendsto h.2.2.2
abbrev crystal(p q:Vantage): ℂ:= inner ℂ (frost P x B p) (flush P x D q)-native P x B*native P x D
abbrev bedtime(p q:Vantage) : ℂ:= inner ℂ (faded P x 0 B p) (sounded P x 0 D q) -native P x B*native P x D
lemma e_crystal (h:crystal P x B D p q≠0): ∀ᶠ y:Vantage×Vantage in 𝓝 (p,q), crystal P x B D y.1 y.2 ≠0 :=by
 have hz:Continuous (fun y:Vantage×Vantage=> crystal P x B D y.1 y.2):= ((((frost_cont P x B).comp continuous_fst).inner ((flush_cont P x D).comp continuous_snd)).sub continuous_const)
 exact hz.continuousAt.eventually_ne h

-- changed y time-only to recover real margin; on arbitrarily close rectangles
lemma afloat (h:Cracks P B D p q)(J:P.Ellis 3 x)(e:crystal P x B D p q ≠ 0):
    ∃ᶠ y:Vantage×Vantage in 𝓝 (p,q), Cracks P B D y.1 y.2 ∧ crystal P x B D y.1 y.2 ≠ 0 ∧ bedtime P x B D y.1 y.2 ≠ 0:=by
    let t:Vantage:= q-p
    let m:ℝ:= B.realWidth P 3+D.realWidth P 3
    have hm:m < t jₓ:=by change _<q jₓ-p jₓ; unfold m; linarith only [h.1,h.2.1]
    let c:=(t 3-m).toNNReal
    let f(z:ℂ):= melody P x B D t z
    have h₀ : f (SatinMacro.rise c) ≠ 0:=by
       unfold f c
       rw [show t=q-p from rfl,show m=_+D.realWidth P 3 from rfl,←chord_price P x B D p q J hm,P.bodyPair_fwd x B D jₓ p q J hm]
       unfold crystal at e; rw [frost_payment P x B D h.1 h.2.1] at e; exact e
    have he:0<(SatinMacro.rise c).im:=by rw [SatinMacro.rise_im]; unfold c; rw [Real.coe_toNNReal _ (sub_nonneg.mpr hm.le)]; linarith
    let y(u:ℝ): Vantage×Vantage:=(p,p+update t jₓ u)
    have ht:Continuous y:=by
       apply Continuous.prodMk continuous_const
       refine continuous_const.add (continuous_pi fun i=>?_)
       by_cases g:i=jₓ; · subst i; simp_rw [update_self]; exact continuous_id
       simp_rw [update_of_ne g ..]; exact continuous_const
    have hs:y (t jₓ)=(p,q):=by unfold y;rw [update_eq_self]; unfold t; simp
    have hn: (∃ᶠ u:ℝ in 𝓝 (t jₓ), f u≠0):=by
       by_contra h'
       rw [Filter.not_frequently] at h'; simp only [ne_eq,not_not] at h'
       obtain ⟨a,b,⟨u,v⟩,w⟩:=mem_nhds_iff_exists_Ioo_subset.mp h'
       obtain ⟨z,l,g⟩:=rim_alive (s:=f) (SatinMacro.carried_holo _ _ _ _) (SatinMacro.carried_only_time ..) he h₀ (lt_trans u v)
       exact g (w l)
    -- f u value on new positions via continuity proof
    have hNew(u:ℝ): f u=bedtime P x B D p (y u).2:=by
       let r:=update t jₓ u
       have hw:p+r-p=r:=add_sub_cancel_left ..
       unfold bedtime
       rw [←real_kernel P x B D r p (y u).2 hw J] -- bedtime def not reduced by rw
       unfold f melody; rw [show r 3=u from update_self ..,show r=update t jₓ u from rfl,wharf_same]
    -- convert filter.
    have hcost:=hn.mono (fun i e=> show bedtime P x B D (y i).1 (y i).2≠0 from (hNew i) ▸ e)
    have hu:Tendsto y (𝓝 (t 3)) (𝓝 (p,q)):= hs ▸ ht.tendsto _
    exact (((cracked P B D h).and (e_crystal P x B D e)).and_frequently (hu.frequently hcost)).mono (fun i ⟨⟨u,v⟩,g⟩=>⟨u,v,g⟩)
-- simultaneously on one badge with both Eu and Mink full supports. collect {
structure Hallmark (F U:SampleDose)(δ:ℝ): Prop where
    admission: SpanSeam P B D F U
    all_regions : ∃ A A':Set Vantage, IsOpen A ∧ IsOpen A' ∧ IsCompact (closure A) ∧ IsCompact (closure A') ∧ tsupport F.val ⊆ A ∧ tsupport U.val ⊆ A' ∧ ∀ p∈ closure A, ∀ q∈closure A',Cracks P B D p q
    credit:0 < δ
    sunJ:Gingham.Jubilation (EuCosts P x B D F U) δ
    darkJ:Gingham.Jubilation (RealCosts P x B D F U 0) δ
    -- each margin against OWN disconnected costs. Not presuming whole field is pure in this lemma.
    gridJ: ∀ᶠ n:ℕ in atTop,Gingham.Topaz (gridValues P x B D F U n) (EuCosts P x B D F U) δ
    noirJ: ∀ᶠ t in 𝓝[>] (0:ℝ≥0), Gingham.Topaz (RealCosts P x B D F U t) (RealCosts P x B D F U 0) δ
open _root_.YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Gingham (nib nib_to Condenses)
lemma late_canvas (p q:Vantage)(u:Cracks P B D p q):
    ∀ᶠ n:ℕ in atTop, ∃ A A': Set Vantage, IsOpen A∧ IsOpen A'∧IsCompact (closure A)∧ IsCompact (closure A')∧ tsupport (nib p n).val ⊆ A∧ tsupport (nib q n).val⊆ A' ∧ ∀ p∈ closure A, ∀ q∈ closure A', Cracks P B D p q := by
    obtain ⟨T',hp,V,hy,t⟩:= mem_nhds_prod_iff.mp (cracked P B D u)
    obtain ⟨a,hk,hv⟩:= Metric.mem_nhds_iff.mp hp; obtain ⟨b,ht,hz⟩:= Metric.mem_nhds_iff.mp hy
    filter_upwards [(nib_to p).2 (Metric.ball p (a/2)) (Metric.ball_mem_nhds _ (half_pos hk)),(nib_to q).2 (Metric.ball q (b/2)) (Metric.ball_mem_nhds _ (half_pos ht))] with n p q' -- p shadows
    refine ⟨_,_,Metric.isOpen_ball,Metric.isOpen_ball,Metric.isBounded_ball.isCompact_closure,Metric.isBounded_ball.isCompact_closure,p,q',?_⟩
    intro y k z h
    refine t (show (y,z)∈ T' ×ˢ V from ⟨hv ((Metric.closedBall_subset_ball (half_lt_self hk)) (Metric.closure_ball_subset_closedBall k)), hz ((Metric.closedBall_subset_ball (half_lt_self ht)) (Metric.closure_ball_subset_closedBall h))⟩)
private lemma chits {Cx D':Gingham.Parts}(g:Gingham.discrepancy Cx≠0)(h:Gingham.discrepancy D'≠0) : ∃ δ:ℝ,0<δ∧Gingham.Jubilation Cx δ∧Gingham.Jubilation D' δ:=by
 let d:=min ‖Gingham.discrepancy Cx‖ ‖Gingham.discrepancy D'‖; have hp:0<d:=lt_min (norm_pos_iff.mpr g) (norm_pos_iff.mpr h)
 exact ⟨d/9,by linarith,lt_of_lt_of_le (show 8*(d/9)<d from (by linarith)) (min_le_left ..),lt_of_lt_of_le (show 8*(d/9)<d from (by linarith)) (min_le_right ..)⟩
theorem springtide (J:P.Ellis 3 x)(h:Cracks P B D p q)(e:crystal P x B D p q≠0):∃ z:Vantage×Vantage, ∀ᶠ n:ℕ in atTop, ∃ δ:ℝ, Hallmark P x B D (nib z.1 n) (nib z.2 n) δ:=by
    obtain ⟨⟨y,v⟩,u,a,c⟩:= (afloat P x B D h J e).exists
    refine ⟨(y,v),?_⟩
    let F:=nib y; let U':=nib v
    have hx(p:Vantage)(v:Vantage→G)(t:Continuous v) := (nib_to p).reply t
    have ht:∀ᶠ n:ℕ in atTop,Gingham.discrepancy (EuCosts P x B D (F n) (U' n))≠0:=(((hx _ _ (frost_cont P x B)).inner (hx _ _ (flush_cont P x D))).sub tendsto_const_nhds).eventually_ne a
    have hu:∀ᶠ n:ℕ in atTop, inner ℂ (flash P x B 0 (F n)) (strike P x D 0 (U' n))-native P x B*native P x D ≠ 0 := (((hx _ _ (move_cont P x _)).inner (hx _ _ (move_cont P x _))).sub tendsto_const_nhds).eventually_ne c -- cannot infer v
    filter_upwards [ht,hu,late_canvas P B D y v u] with n p q pA
    have p':(F n).Normalized:= (nib_to _).1 _; have v':(U' n).Normalized:=(nib_to _).1 _
    have he:Gingham.discrepancy (RealCosts P x B D (F n) (U' n) 0)≠0:=by
       unfold Gingham.discrepancy RealCosts; dsimp only [Prod.snd,Prod.fst]; rw [(PaidOne P x B (F n) 0 p' J).1,(PaidOne P x D (U' n) 0 v' J).2]; exact q
    obtain ⟨δ,d,t,w⟩:=chits p he
    let C:=EuCosts P x B D (F n) (U' n); let V':=RealCosts P x B D (F n) (U' n) 0
    have g: SpanSeam P B D (F n) (U' n):=by
       obtain ⟨M₁,M₂,-,-,-,-,a₁,a₂,b'⟩:=pA; let e(v:Vantage)(t:v∈tsupport (F n).val):= subset_closure (a₁ t); let h(p':Vantage)(t:p'∈tsupport (U' n).val):=subset_closure (a₂ t)
       obtain ⟨v₁,l⟩:= Gingham.hitting p'; obtain ⟨v₂,l'⟩:= Gingham.hitting v'
       exact ⟨fun x w=>(b' x (e x w) v₂ (h v₂ l')).1,fun x w=>(b' v₁ (e v₁ l) x (h x w)).2.1,fun x y w v=> (b' x (e x w) y (h y v)).2.2.1, p',v'⟩
    refine ⟨δ,g,pA,d,t,w,(seam_income P x B D _ _ J g).eventually (Gingham.likelier C C (Gingham.Topaz.refl C d)), (real_unpad P x B D _ _).eventually (Gingham.likelier V' V' (Gingham.Topaz.refl V' d))⟩
#print axioms springtide
