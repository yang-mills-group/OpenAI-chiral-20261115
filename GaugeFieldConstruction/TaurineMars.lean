import GaugeFieldConstruction.PetalMars
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff FourierTransform InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
abbrev ΧiMars := UV four
variable {n:ℕ} (k:Fin n) (a:Axis)
abbrev WallMars (F:Fin n→ ΧiMars):Points n→ℂ:= Y.fee n (Calibration.lift four ∘ F)
variable (F:Fin n→ΧiMars)
lemma CableMars (i:Axis)(k:Fin n)(f:Test n)(b:Bulb)(h:Works b f k):
    - (Dash.down f k i).applyTo (WallMars Y F)= ∑ j:Axis,(lace f (LED b j) (h.cared j)).applyTo (WallMars Y (Fathom.add (p.J j i) F)) :=by
 let W:=Calibration.lift four ∘ F
 have T : tilt (direction k i) f=Dash.down f k i:=by ext1; rw[tilt_pays,Dash.desc]
 have hU : W k=Calibration.lift four (F k):=rfl
 have H:update W k (Calibration.lift four (F k)) = W:=by rw[←hU,update_eq_self]
 have v:=p.price i (F k) W k f b h
 simp_rw [spot_cost,H,Fathom.pays,T,tagged_cost, Y.price] at v
 refine v.trans (Finset.sum_congr rfl fun j _=>?_)
 rw [show Fathom.add (Calibration.lift four (p.J j i)) W=(Calibration.lift four ∘ Fathom.add (p.J j i) F) from ?_]
 ext1 z; refine Fin.cases ?_ (fun u=>rfl) z; rfl
lemma headingMars (K:Points n→ℂ)(t:Test n)(x:Points n)(v:Test n)(h: ∀ i, v i= Dash.wave x i*t i):
    𝓕 (fun y=>t y*K y) x=v.applyTo K:=by
 rw [Dash.scanned,YM.Test.applyTo]; exact integral_congr_ae (Eventually.of_forall fun y=>by dsimp only; rw[h,mul_assoc])
lemma CabWaveMars (x:Points n)(i:Points (n+1)): Dash.wave (Points.cons 0 x) i=Dash.wave x (riders i):=by
 have h:inner ℝ i (Points.cons 0 x)= inner ℝ (riders i) x:=by
    simp only[PiLp.inner_apply]; rw [Fin.sum_univ_succ]; simp [Points.cons]; rfl
 unfold Dash.wave; rw[h]
lemma PlasmaMars (x:Points n)(f: Test n)(b:Bulb)(h:Works b f k):
    (I*↑Probe.q*↑(x k a)) * 𝓕 (fun y=>f y*WallMars Y F y) x = 𝓕 (fun y=> (Dash.down f k a) y * WallMars Y F y) x + ∑ j:Axis,
        𝓕 (fun y=> (lace f (LED b j) (h.cared j)) y* WallMars Y (Fathom.add (p.J j a) F) y) (Points.cons 0 x):=by
 obtain ⟨y,hy⟩:=Dash.extend f (Dash.enough x); obtain ⟨z,hz⟩:=Dash.extend (Dash.down f k a) (Dash.enough x)
 have hl:Works b y k:=h.via y (closure_mono (fun i hi hp=> hi (by change y i=0; rw[hy]; dsimp only; rw[show f i=0 from hp,mul_zero])))
 let G:=I*↑Probe.q*↑(x k a)
 have ht:Dash.down y k a=z-G • y:=by
    ext1 u; rw [Dash.desc,hy]; unfold D; rw [fderiv_fun_mul]; rotate_left
    · exact ((Dash.enough x).differentiable (by simp)) u
    · exact f.contDiff.differentiable (by exact_mod_cast (show (⊤ : ℕ∞) ≠ 0 by simp)) _
    change _ = z u-G*y u; rw [hy,hz]
    have hv:= Dash.rate x k a u; dsimp only; rw [Dash.desc]; unfold Analysis.D at *; simp only[_root_.add_apply, _root_.smul_apply, smul_eq_mul]; rw [hv]; unfold G; ring
 have hc:(∑ j:Axis, 𝓕 (fun y=> (lace f (LED b j) (h.cared j)) y* WallMars Y (Fathom.add (p.J j a) F) y) (Points.cons 0 x))=∑ j:Axis, (lace y (LED b j) (hl.cared j)).applyTo (WallMars Y (Fathom.add (p.J j a) F)):= by
    apply Finset.sum_congr rfl; intro j hj; refine headingMars _ _ _ _ (fun i=>?_)
    rw [CabWaveMars]; change (b.LED j).f (helm i) • y (riders i)=_ *((b.LED j).f (helm i) • f (riders i))
    rw [hy, mul_smul_comm]
 rw [hc, ←CableMars p Y F a k y b hl,ht, headingMars _ _ _ y (congr_fun hy),headingMars _ _ _ z (congr_fun hz)]
 unfold WallMars; simp_rw [←Y.price]; rw[map_sub,map_smul]; change _=_+ -(_-G*_); ring

#print axioms PlasmaMars
end YM.GaugeFieldConstruction.Ember.Volumetric
