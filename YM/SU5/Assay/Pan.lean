import YM.SU5.Assay.SInt
-- possibly add C* etc
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Metric Filter
open scoped Topology
open CF.Buffered.Afterglow.Tower.Aria (firmly)
variable {H:Hilbert}{I:Type*}{l:Filter I}{a b:I→H.Op}{x y:H.Op}
open MeasureTheory
open scoped InnerProductSpace
variable {G:Type*}[MeasurableSpace G] {μ:Measure G}{M N:G→H.Op}
/-! Integrate pose fields. Real center tests with compact support. No operator
norm measurability required. At the support, need local (nhds) BSOT
qualification and uniform charges. -/
variable {F:G→ℝ}
abbrev Pan (F:G→ℝ)(M:G→H.Op) := fun g=>(F g :ℂ)•M g
abbrev mixedCup (μ:Measure G)(F:G→ℝ)(M:G→H.Op):=SInt μ (Pan F M)
variable [TopologicalSpace G]
variable (h:Continuous F)(D:HasCompactSupport F)
section E
omit [MeasurableSpace G]
section S
omit [TopologicalSpace G]
lemma star_pan (g:G):star (Pan F M g)= (F g:ℂ)•star (M g):=by rw [Pan,star_smul,Complex.star_def,Complex.conj_ofReal]
lemma pan_dry (g:G)(h:F g=0):Pan F M g=0:=by rw [Pan,h,Complex.ofReal_zero,zero_smul]
end S
def AtPan (F:G→ℝ)(M:G→H.Op) : Prop:= ∀g∈tsupport F,BSOT M (𝓝 g) (M g)
-- separate predicate to allow sequence qualification
abbrev PanC (F:G→ℝ)(M:G→H.Op)(C:ℝ):Prop:=∀g∈tsupport F,‖M g‖≤ C
include h in
lemma AtPan.contour (w:AtPan F M)(g:G): BSOT (Pan F M) (𝓝 g) (Pan F M g):=by
 by_cases p:g∈tsupport F
 · exact (w g p).scale ((Complex.continuous_ofReal.comp h).tendsto g)
 rw [pan_dry g (image_eq_zero_of_notMem_tsupport p)]
 refine (BSOT.stay _).congr' ?_
 exact (notMem_tsupport_iff_eventuallyEq.mp p).mono fun i v=>(pan_dry i v).symm
lemma pan_paid {C:ℝ}(v:PanC F M C)(g:G): ‖Pan F M g‖≤ ‖F g‖*C:=by
 by_cases p:g∈tsupport F
 · rw [Pan,norm_smul,Complex.norm_real];gcongr;exact v g p
 have u:= image_eq_zero_of_notMem_tsupport p
 rw [pan_dry g u,u,norm_zero,norm_zero,zero_mul]

end E
variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
include h D
lemma AtPan.booth {C:ℝ}(p:AtPan F M)(v:PanC F M C) : SInk μ (Pan F M):=by
 refine ⟨fun u=>?_,fun u=>?_,⟨_,(h.norm.integrable_of_hasCompactSupport D.norm).mul_const _,Eventually.of_forall (pan_paid v)⟩⟩
 · have ht:Continuous fun g=> Pan F M g u:=continuous_iff_continuousAt.mpr fun g=>(p.contour h g).showAt u
   refine ht.integrable_of_hasCompactSupport (D.mono fun i n z=> n ?_)
   change Pan F M i u=_; rw [pan_dry i z];rfl
 have ht: Continuous fun g=>star (Pan F M g) u:=continuous_iff_continuousAt.mpr fun g=>(p.contour h g).starAt u
 refine ht.integrable_of_hasCompactSupport (D.mono fun i n z=> n ?_)
 change star (Pan F M i) u=_; rw [pan_dry i z,star_zero]; rfl

lemma PanC.cupRead (p:AtPan F M){C:ℝ}(v:PanC F M C)(u:H):
 (mixedCup μ F M) u=∫g,(F g :ℂ)•(M g u)∂μ:= (p.booth h D v).click _
lemma PanC.cupTurn (p:AtPan F M){C:ℝ}(v:PanC F M C)(u:H):
 star (mixedCup μ F M) u=∫g,(F g:ℂ)•((star (M g)) u) ∂μ:=by
 unfold mixedCup; rw [SInk.turn (p.booth h D v)]
 exact integral_congr_ae (Eventually.of_forall fun g=> congrArg (fun x:H.Op=>x u) (star_pan g))
lemma PanC.cupPrice (p:AtPan F M){C:ℝ}(v:PanC F M C): ‖mixedCup μ F M‖ ≤ (∫g, ‖F g‖ ∂μ)*C:=by
 rw [←integral_mul_const]; exact (p.booth h D v).castLe ((h.norm.integrable_of_hasCompactSupport D.norm).mul_const _) (Eventually.of_forall (pan_paid v))

variable [IsCountablyGenerated l]{A:I→G→H.Op}{C:ℝ}
lemma PanC.cupLimit [NeBot l](p:AtPan F M)(s:∀ᶠ i in l,AtPan F (A i) ∧ PanC F (A i) C)
 (v:0≤C)(w:∀g∈tsupport F, BSOT (fun i=>A i g) l (M g)):
 BSOT (fun i=>mixedCup μ F (A i)) l (mixedCup μ F M):= by
 have z:PanC F M C:=fun g u=>(w g u).consult v (s.mono fun i t=>t.2 g u)
 refine (p.booth h D z).passage (s.mono fun i u=>u.1.booth h D u.2) ((h.norm.integrable_of_hasCompactSupport D.norm).mul_const C)
    (s.mono fun i u=>Eventually.of_forall (pan_paid u.2)) (Eventually.of_forall fun g=>?_)
 by_cases u:g∈tsupport F
 · exact (w g u).scale tendsto_const_nhds
 have r:=image_eq_zero_of_notMem_tsupport u
 rw [pan_dry g r];exact (BSOT.stay _).congr' (Eventually.of_forall fun _=>(pan_dry g r).symm)
end YM
