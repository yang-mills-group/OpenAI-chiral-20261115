import GaugeFieldConstruction.CodaMars
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Set Filter MeasureTheory Measure Complex Analysis Points Bulb
open scoped ContDiff Topology BigOperators
variable {n:ℕ}
lemma paleM (S:Set (Points n))(F G:Points n→ℂ)(f:ContinuousOn F S)(t:Test n)(v:tsupport t ⊆ S)(u:IsOpen S) : Integrable (fun x=> t x*F x):=by
 have h:Continuous (fun x=>t x*F x):=continuous_iff_continuousAt.mpr fun x=>by
    by_cases p:x∈tsupport t
    · exact t.continuous.continuousAt.mul ((f x (v p)).continuousAt (u.mem_nhds (v p)))
    refine (continuousAt_const (y:=(0:ℂ))).congr ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp p] with i p; simp [p]
 exact h.integrable_of_hasCompactSupport t.hasCompactSupport.mul_right
lemma echelonsM (S:Set (Points n))(w:S⊆conf n)(u:IsOpen S)(F G:Points n→ℂ)(f:ContinuousOn F S)(g:ContinuousOn G S)
    (h:∀ t: Test n, tsupport t⊆ S → t.applyTo F=t.applyTo G) : EqOn F G S:=by
 let W:= F-G
 have hV:ContinuousOn W S:= f.sub g
 have hv: W =ᵐ[volume.restrict S] 0:= (ae_restrict_iff' u.measurableSet).mpr (u.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume) (hV.locallyIntegrableOn u.measurableSet) (fun v p k Y=> by
    let T (x):=Complex.ofRealCLM (v x)
    have hW:tsupport T=tsupport v:=by unfold tsupport; rw[show support T=support v from ?_]; ext; simp[T]
    let t:Test n:= ⟨T,Complex.ofRealCLM.contDiff.comp p,(by rw[HasCompactSupport,hW]; exact k), hW ▸ (Y.trans w)⟩
    have hp:tsupport t⊆S:=hW ▸ Y
    have he:t.applyTo W=0:=by
        change (∫ x,t x*(F x - G x))=0
        simp_rw[mul_sub]; rw [integral_sub (paleM S F G f t hp u) (paleM S G F g t hp u)]; exact sub_eq_zero.mpr (h t hp)
    rw [←he]; congr 1)) -- tune
 intro i hi; exact sub_eq_zero.mp (show _ from Measure.eqOn_open_of_ae_eq hv u hV continuousOn_const hi)
lemma fusionMars (n:ℕ): MeasurePreserving (fuse (n:=n)) volume volume:= (WithLp.volume_preserving_ofLp _ _).comp (LinearIsometryEquiv.measurePreserving (peel (n:=n)))
-- euclidean flux with multiplier from compact cutoff plus payroll
variable (A:Points (n+1)→ℂ)(P:ContDiffOn ℝ ∞ A (conf (n+1))) (K: Payroll n)
variable (b:Bulb)(a j:Axis)
noncomputable def SoilMars (z:E4 × Points n):ℂ:= ((LED b a).f z.1 * K.K j (fuse.symm z)) • A (fuse.symm z)
noncomputable def RyeMars:=WrapMars (SoilMars A K b a j)
lemma SoilAreaMars (y:E4)(u:y∉run (LED b a))(x:Points n): SoilMars A K b a j (y,x)=0:=by rw[SoilMars]; dsimp only; rw[image_eq_zero_of_notMem_tsupport u,zero_mul,zero_smul]
include P
lemma SoilCapMars (x:Points n)(k : Fin n)(h:BreatherMars b k x)(y:E4):ContDiffAt ℝ ∞ (SoilMars A K b a j) (y,x):=by
 let F:= SoilMars A K b a j
 by_cases c:y∈run (LED b a)
 · have e: fuse.symm (y,x)∈conf _:=RoomMars b k x h y (cone b a c)
   exact (((LED b a).d.comp contDiff_fst).contDiffAt.mul ((K.sm j).comp fuse.symm.contDiff).contDiffAt).smul (((P _ e).contDiffAt ((conf_open _).mem_nhds e)).comp _ fuse.symm.contDiff.contDiffAt)
 refine (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq ?_
 filter_upwards [((isClosed_tsupport (LED b a).f).isOpen_compl.prod isOpen_univ).mem_nhds (show (y,x)∈(run (LED b a))ᶜ ×ˢ univ from ⟨c,mem_univ _⟩)] with z u; exact SoilAreaMars A K b a j z.1 u.1 z.2 -- tune syntax
lemma SoilCanMars (k:Fin n):ContinuousOn (RyeMars A K b a j) {x|BreatherMars b k x}:=fun x hx=>by
 exact ((inventoryMars (SoilMars A K b a j) _ (BreathingMars b k) (run (LED b a)) (LED b a).c (fun x hx y=>SoilCapMars _ P K b a j x k hx y) (fun x _ y hy=>SoilAreaMars A K b a j y hy x) x hx).continuousAt).continuousWithinAt
lemma SoilEarnMars (k:Fin n)(t:Test n)(h:b.Works t k): t.applyTo (RyeMars A K b a j)=(testcut K t b h.cared a j).applyTo A:=by
 let v:=testcut K t b h.cared a j; let V(x:Points (n+1)):= v x*A x
 let T:=SoilMars A K b a j
 let c:= (fuse (n:=n)).toHomeomorph.toMeasurableEquiv
 have he:MeasurePreserving c.symm volume volume:= MeasurePreserving.symm (e:=c) (fusionMars n)
 have hI:Integrable V:= v.smearing P.continuousOn
 have hC:Integrable (fun x=> V (fuse.symm x)):= he.integrable_comp_of_integrable hI
 unfold YM.Test.applyTo; rw [show (∫ x, testcut K t b h.cared a j x*A x)=(∫ y:E4×Points n,V (fuse.symm y)) from (he.integral_comp c.symm.measurableEmbedding _).symm]; refine Eq.trans ?_ (integral_prod_symm _ hC).symm; apply integral_congr_ae; apply Eventually.of_forall; intro x
 change t x * (∫ y:E4,T (y,x))= _ -- parentheses
 rw [←integral_const_mul]; apply integral_congr_ae; apply Eventually.of_forall; intro y
 unfold V v; simp_rw[testcut_v]
 change t x* (((LED b a).f y*K.K j (fuse.symm (y,x))) • A (fuse.symm (y,x)))=_; simp only [Complex.real_smul]; rw [show helm (fuse.symm (y,x))=y from rfl, show riders (fuse.symm (y,x))=x from rfl, show (LED b a).f y=D (basis a) b.f y from rfl]; ring -- tune defeq
#print axioms SoilEarnMars
end YM.GaugeFieldConstruction.Fathom
