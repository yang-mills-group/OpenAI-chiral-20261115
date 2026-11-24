import GaugeFieldConstruction.MorvenRT
/-!
 # NO charges. Sold day and lunar charts. pop analytic gap extends to arbitrary common spectator norm-tunnel later.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
lemma κPathCalcRt (o:Full n)(Q:ZSideRt n→ℂ)(s:ℝ)(h:AnalyticAt ℂ Q (PαXRT s o)): HasDerivAt (fun t=> Q (PαXRT t o)) (I*SunStrRt Q (PαXRT s o)) s:=by
 let F:= fderiv ℂ Q (PαXRT s o); have he:HasDerivAt (fun s:ℝ=> PαXRT s o) (I • basisTRt n) s:=by
    unfold basisTRt; rw [Prod.smul_def,smul_eq_mul,mul_one, smul_zero] -- tune mul_one'
    refine HasDerivAt.prodMk ?_ (hasDerivAt_const s _); convert (ofRealCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_id s)).mul_const I using 1 <;> first|rfl|simp -- tune
 have hp:= (h.differentiableAt.hasFDerivAt|>.restrictScalars ℝ).comp_hasDerivAt s he; change HasDerivAt _ (F (I • basisTRt n)) _ at hp; rwa [map_smul] at hp
lemma κMeterBirthRT (d:ℝ)(p:0<d)(Q:ℝ→ℂ)(A B:ℝ→ℂ)(hA: ContinuousOn A (Icc (-d) 0))(hB:ContinuousOn B (Icc 0 d))(eA:A (-d)=0)(eB:B d=0)(h:Integrable Q)(hv:∀ x,x ∉ Icc (-d) d→ Q x=0)(o:∀ x∈Ioo (-d) 0,HasDerivAt A (Q x) x)(t:∀ x∈Ioo 0 d,HasDerivAt B (Q x) x): (∫ x:ℝ,Q x)=A 0-B 0:=by
 have he:(∫ x:ℝ,Q x)=∫ x in -d..d,Q x:=by
    rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero hv] -- tune
 rw [he,← intervalIntegral.integral_add_adjacent_intervals (b:=(0:ℝ)) h.intervalIntegrable h.intervalIntegrable,(intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hA o h.intervalIntegrable),(intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le p.le hB t h.intervalIntegrable), eA, eB]; ring
#print axioms κMeterBirthRT
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 Metric PortRT
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hu:F.NonTangentialFree Y)(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "Φ_H"=> H.TinCanL ∘ V
local notation "Τh" => TouchMΛ H (N:=N)
local notation "Ξ"=> CoffΜΛ H p
variable (k:Fin n)(a:Axis)(B:ContDiffBump (0:ℝ))(f:ContDiffBump (0:Space3))(x:Points n)
variable (w:BreatherMars (UpShadeRt B f (x k)) k x)(m:x∈NSF.Work.C20.ordered n)
local notation "Τbill"=> ΛPaidRT p H (N:=N) V k a B f x
local notation "Ψ"=> φInXRt f
local notation "zₓ"=> wickSlice n x
noncomputable abbrev HandSlopeRT (J:Bool→ ZSideRt n→ℂ)(g:Bool)(s:ℝ):= ΛSignXRt a * ((B s:ℂ) * J g (PαXRT s (wickSlice n x)))
abbrev YardErosRT (J:Bool→ ZSideRt n→ℂ)(g:Bool)(z:ZSideRt n):= AnalyticAt ℂ (J g) z ∧ (z.1∈HalfRT g → (∀ v,QchIRt k g z v∈tube (n+1)) ∧ J g z = PanProjRT (X:=N) k (CoffΜΛ H p) (H.TinCanL ∘ V) a (φInXRt f) timeAxis g z ∧ SunStrRt (J g) z= DawnSideRt (X:=N) k (CoffΜΛ H p) (H.TinCanL ∘ V) a (φInXRt f) g z)
variable (J:Bool→ ZSideRt n→ℂ)
local notation "Yd"=> YardErosRT p H (N:=N) V k a f J
lemma FloodGenRT(g:Bool)(s:ℝ)(U:Yd g (PαXRT s zₓ)):ContinuousAt (HandSlopeRT a B x J g) s :=by
 exact continuousAt_const.mul ((continuous_ofReal.continuousAt.comp B.continuous.continuousAt).mul (κPathCalcRt _ _ _ U.1).continuousAt) -- tune
include G hz hv
lemma FloodRiseRT (g:Bool)(s:ℝ)(U:Yd g (PαXRT s zₓ))(t:(PαXRT s zₓ).1∈HalfRT g):HasDerivAt (HandSlopeRT a B x J g) (Τbill s) s:=by
 let z:=PαXRT s zₓ; obtain ⟨he,h,e⟩:=U.2 t; rw [ΨAetnaRt p H G hz hv V k a B f _ s g he,← h,← e]
 have hB: HasDerivAt (fun t:ℝ => (B t:ℂ)) (Complex.ofRealCLM (_root_.deriv B s)) s:= ofRealCLM.hasFDerivAt.comp_hasDerivAt s ((B.contDiff.differentiable (n:=∞) (by simp) _).hasDerivAt)
 convert ((hB.mul (κPathCalcRt _ _ _ U.1)).const_mul (ΛSignXRt a)) using 1 <;> first|rfl|simp [mul_assoc] -- tune
variable (d:ℝ)(t:B.rOut<d)(hp:∀ (g:Bool) (s:ℝ),s∈ Set.Icc (-d) d → YardErosRT p H (N:=N) V k a f J g (PαXRT s (wickSlice n x)))
include hp t m w e
lemma FloodTrueRT: TouchMΛ H (N:=N) V k a (wickSlice n x)= ΛSignXRt a * (J false (0,(wickSlice n x)) - J true (0,(wickSlice n x))):=by
 rw [handValueRt p H G hz hv e V k a B f _ w m]
 let U:= HandSlopeRT a B x J
 have v:= B.rOut_pos.trans t
 have h1:Icc (-d) (0:ℝ)⊆ Icc (-d) d:=Icc_subset_Icc_right v.le; have h2:Icc (0:ℝ) d⊆Icc (-d) d:= Icc_subset_Icc_left (neg_nonpos.mpr v.le)
 have vT(g:Bool)(s:ℝ)(r:d≤|s|): U g s=0:=by
    have he:s∉closedBall (0:ℝ) B.rOut:=by intro h; exact (not_lt.mpr (r.trans (show |s| ≤ _ by simpa using h))) t
    rw [← B.tsupport_eq] at he; simp only [U,HandSlopeRT, image_eq_zero_of_notMem_tsupport he, ofReal_zero,zero_mul,mul_zero]
 rw [κMeterBirthRT d v _ (U false) (U true) (?_) (?_) (vT false _ (by simp [abs_of_pos v])) (vT true _ (by simp [abs_of_pos v])) (AnsonTaxRT p H G hz hv e V k a B f x w) (?_) (?_) (?_)]
 · unfold U HandSlopeRT; have hZ:B (0:ℝ)=1:= B.eventuallyEq_one.eq_of_nhds; simp [hZ,PαXRT,mul_sub]
 · exact fun y h=>(FloodGenRT p H V k a B f x J _ y (hp false y (h1 h))).continuousWithinAt
 · exact fun y h=>(FloodGenRT p H V k a B f x J _ y (hp true y (h2 h))).continuousWithinAt
 · intro i t'; exact AnsonOutRT _ H V k a B f x i (fun a=>t' (abs_le.mp (le_trans (show |i|≤B.rOut by simpa using a) t.le)))
 · intro i w; exact FloodRiseRT p H G hz hv V k a B f _ J false i (hp false _ (h1 (Ioo_subset_Icc_self w))) (by simp [HalfRT,w.2])
 intro i w; exact FloodRiseRT p H G hz hv V k a B f _ J true i (hp true _ (h2 (Ioo_subset_Icc_self w))) (by simp [HalfRT,w.1])
#print axioms FloodTrueRT
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
