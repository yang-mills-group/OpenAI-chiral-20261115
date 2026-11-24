import YM.CF.BPress.House.Shirt
import YM.CF.BPress.Wealth.Mark
/-! museum transfer. Includes Pose.Books integrated outside phases. $compare (∫Rod ∫Act)$ is pointwise including unnormalized gauge prefactor and valid σ weight. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.House
open Precision Pressure Next.SectorChange RG Wilson Push.SectorMeasure MeasureTheory Measure LocalH Lattice Cube Bands Locale Wealth Net Grid Finset Function SU Mag Branch Port Weave Vesper Skye Hazel Reserve Filter Env
open scoped Classical Topology BigOperators YM.CF.BPress.Vesper
variable {N:Side}{B:BandWidth}(A:Bands (More N) B)(R:Hangar (More N)) (T:Sheet.Atlas)(y κ:ℝ)(J:ChartRatio SU.group)(F:Fare A)
variable (g:A.Slates→Orbit N→ℂ) (b:mState N A→ℂ)
-- $t$_ flags for core.S^
def holdsT (x:Old A)(v:Quarters A) : Prop := aware A κ y F x.1 v ∧ flash A x.2∈ A.permit T y (A.atmospheric (centerSky A F x.1 v y))
abbrev Role(w:mState N A) : Prop := Precinct A y w∧ holdsT A T y κ F w.1 w.2.1
variable {T y} {c d L :ℝ}{a:ℕ}(Z:Net (More N) T L y c d a) (P:Weave.Budget)
-- unnormalized function compare
abbrev jstamp (x:Old A)(v:Quarters A) := detM A (F x.1)* taxG A J y F x.1 v.1
structure Theater :Prop where
 envelope0 (w:A.Slates): Envelope (g w)
 envelope1: Envelope b
 fromWarp(x:Old A)(W: Quarters A)(U:Micro (More N))(θ:Ids N): ToneNoise y U → Barrel A y W.1 →
    (∫ v: Rod N,(∫ w:ActY N, b (x,W,U,θ,v,w) ∂ Wheel.coin (Site N))∂ Wheel.coin (Site (More N)))= if holdsT A T y κ F x W then jstamp (y:=y) A J F x W • g (flash A x.2) (Hazel.field A Z F x.1 W (flash A x.2) U, θ) else 0
section pre
abbrev climb (x:A.Slates)(Y:A.Sky) (U:Micro (More N)) : ℂ:= ∫ v:Ids N,g x (Z.roll A x Y U,v)∂ Skye.depot N
def climbX (x:A.Slates)(Y:A.Sky):ℂ:=∫ U:Micro (More N), climb A g Z x Y U ∂ Rivet N y
def spot (w:A.Slates)(Y:A.Sky):ℂ:=if w∈ A.permit T y (A.atmospheric Y) then climbX A g Z w Y else 0
variable (H:∀ w,Envelope (g w))(f: Fast y)
include H f
lemma seat_g (w) : Envelope (spot A g Z w):=by
 haveI:= f.noise; apply Law.switchP ((atmospheric_meas ..) (A.permit_meas T y w)) ?_ (Law.fixedP (0:ℂ)); refine Law.marginalP (f:=fun x:A.Sky × Micro (More N)=> climb A g Z w x.1 x.2) ?_ (Rivet N y); -- tune implicit
 exact Law.marginalP (Env.along (H w) (g:=fun x:(A.Sky×Micro (More N))×Ids N=> (Z.roll A w x.1.1 x.1.2,x.2)) (((roll_joint A Z w).comp measurable_fst).prodMk measurable_snd)) _ -- tune
abbrev horizon : ℂ:= ∫ x:A.Sky,(∑ i∈ A.permit T y (A.atmospheric x), climbX A g Z i x)∂A.Rain
abbrev setting (i:A.Hcols→Fin 5) (w: Offers A) := spot A g Z (flash A i) (Aback A w)
lemma seat_pose (i:A.Hcols→Fin 5) : Envelope (setting A g Z i):= Env.along (seat_g A g Z H f (flash A i)) (heart A).symm.measurable
lemma basis_sum : horizon A g Z=∑ i:A.Hcols→Fin 5,∫ x, setting A g Z i x ∂ Rains A:=by
 have he: MeasurePreserving (heart A) A.Rain (Rains A):= heart_mp ..; unfold horizon; rw [←he.symm.integral_comp']; let U(w)(i):= climbX A g Z i w; have hp(w:A.Sky): (∑ i∈ A.permit T y (A.atmospheric w), climbX A g Z i w)=∑ i:A.Hcols→Fin 5,spot A g Z (flash A i) w:=bank_sum ..
 simp_rw [hp]; exact integral_finsetSum _ (fun i _=> integrableX (seat_pose A g Z H f i) _) -- tune
end pre
variable {A b κ J F P Z R g}
variable (K:Theater A κ J F g b Z)(t:Afford J T P B.D κ y) (j:LocalRatio J)(s:Summer A F P.upper (P.low y) (P.reach y) (P.chunks y))(ℓ:∀ S,Whole A S (F S) 1)(h:Fast y)
namespace Theater
include h K
lemma public_t (i:A.Hcols→ Fin 5)(S:Seal A.Hcols)(v:Quarters A)(P:Barrel A y v.1) : (∫ x:Hat N, b ((S,i),v,x)∂paleB y N)=tollD A J κ y F S (setting A g Z i) v:=by
 let z:= ((S,i): Old A); let Y:=centerSky A F S v y; let w:= flash A i; let Y':= bodyBase A y F S v; let Z':=pick A κ y Y'; let a:=jstamp (y:=y) A J F z v; have he(U:Micro (More N))(θ:Ids N):ToneNoise y U→
    ∫ p:Rod N × ActY N, b ((S,i),v,U,θ,p)∂(Wheel.coin (Site (More N))).prod (Wheel.coin (Site N)) = if holdsT A T y κ F z v then a • g w (Z.roll A w Y U, θ) else 0:=by
    intro t; rw [integral_prod]; · exact K.fromWarp z v U θ t P
    exact integrableX (Env.along K.envelope1 (g:=fun p:Rod N × ActY N=> ((S,i),v,U,θ,p)) (by fun_prop)) _
 unfold paleB; rw [integral_prod]; swap; · exact integrableX (Env.along K.envelope1 (g:=fun x:Hat N=> ((S,i),v,x)) (by fun_prop)) _
 have hp(U:Micro (More N))(H:ToneNoise y U):
    (∫ v':Ids N × (Rod N × ActY N), b ((S,i),v,U,v')∂(Skye.depot N).prod ((Wheel.coin (Site (More N))).prod (Wheel.coin (Site N))))= if holdsT A T y κ F z v then a • climb A g Z w Y U else 0:=by
    rw [integral_prod]; swap; · exact integrableX (Env.along K.envelope1 (g:=fun p:Ids N × (Rod N × ActY N)=> ((S,i),v,U,p)) (by fun_prop)) _
    simp_rw [he U _ H]; split_ifs; · rw [integral_smul]
    exact integral_zero .. -- tune split_ifs
 haveI:= h.noise; have ht: (∀ᵐ x∂ Rivet N y, ToneNoise y x):= ae_all_iff.mpr fun i=> (Measure.tendsto_eval_ae_ae (μ:=fun _ : Link (More N)=> Law.noise group (xi y)) (α:= fun _=>SU.E) (i:=i)).eventually (Law.noise_ae (G:=group) _) -- tune
 refine (integral_congr_ae (ht.mono (fun _ e' => hp _ e'))).trans ?_; change (∫ U: Micro (More N), (if holdsT A T y κ F z v then a • _ else 0) ∂ Rivet N y)= detM A (F S) • taxG A J y F S v.1 • callx A κ y S (setting A g Z i) Y'; by_cases e:S=Z'; swap; · have p₁:¬holdsT A T y κ F z v:=fun h=> e (Eq.symm h.1); simp [p₁,callx, show ¬S=pick A κ y Y' from e]
 have g1: holdsT A T y κ F z v ↔ w∈ A.permit T y (A.atmospheric Y):=⟨ And.right,fun p=>⟨Eq.symm e,p⟩⟩; rw [callx,if_pos (show _ from e)]; unfold setting; change _ = _ • _ • spot A g Z w Y; simp only [g1]; unfold spot; split; next p' => rw [ integral_smul]; rw [smul_smul]; rfl
 next p' => simp
include t s j ℓ
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 650000 in
lemma Museum : horizon A g Z=∫ v,b v∂museum A y:=by
 let Q:= K.envelope1; haveI:IsProbabilityMeasure (knell A y):=inferInstance; haveI :SigmaFinite (knell A y):= inferInstance; haveI : SFinite (knell A y):=inferInstance; haveI : SFinite ((knell A y).prod (paleB y N)):= inferInstance; unfold museum; rw [integral_prod,integral_count]; swap; · exact integrableX Q _
 rw [show (∑ i:Old A,_)= _ from Fintype.sum_prod_type _]; -- maybe use directly
 have he:= K.envelope0; let f:=setting A g Z; have hp(i:A.Hcols→Fin 5)(S:Seal A.Hcols): ∫ x:Quarters A × Hat N, b ((S,i),x)∂(knell A y).prod (paleB y N)=∫ v,tollD A J κ y F S (setting A g Z i) v∂ knell A y:= by
    rw [integral_prod]; swap; · exact integrableX (Env.along Q (g:=fun x:Quarters A × Hat N=> ((S,i),x)) (by fun_prop)) _
    exact integral_congr_ae ((barrel_ae A y).mono (fun v F=> K.public_t h i S v F))
 simp_rw [hp]; rw [Finset.sum_comm,basis_sum A g Z he h]; apply sum_congr rfl; intro i _; exact seaTotals (setting A g Z i) t j s ℓ (integrableX (seat_pose A g Z he h i) _) ((seat_pose A g Z he h i).meas.stronglyMeasurable) -- tune
lemma threshold (R:Hangar (More N))(f:0<paysP (B:=B) R y): horizon A g Z=wool A R y • ∑ E, ∫ v,b (read A R v)∂ Century A R y E:= (K.Museum t j s ℓ h).trans ((Law.restore _ _ _ (recipe A R h) b (integrableX K.envelope1 _)).trans (regions A R y _ (Env.along K.envelope1 (recipe A R h).measurable) f)) -- tune
end Theater
end YM.CF.BPress.House
