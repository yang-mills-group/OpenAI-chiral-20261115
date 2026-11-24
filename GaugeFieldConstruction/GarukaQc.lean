import GaugeFieldConstruction.KashiaQc
/-!
# Adjoint-real conjugator and flavor accounting
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8400
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius ComplexConjugate
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S) (s:Flavor) (v:UpAngleQc Y)
noncomputable abbrev GrayMapQc :ℂ→L[ℝ]ℂ:= Complex.conjCLE.toContinuousLinearMap
lemma BringQc (p:Test n): tsupport (GrayMapQc ∘ p)=tsupport p:= by unfold tsupport; rw [show support (GrayMapQc ∘ p)=support p from (by ext x; change GrayMapQc (p x)≠0↔_; exact not_congr (LinearEquiv.map_eq_zero_iff Complex.conjCLE.toLinearEquiv))] -- tune
noncomputable def GrayTestQc (p:Test n):Test n:= ⟨GrayMapQc ∘ p,GrayMapQc.contDiff.comp p.contDiff, by rw [HasCompactSupport,BringQc]; exact p.hasCompactSupport, (BringQc p).symm ▸ (show _ from p.tsupport_subset)⟩
lemma grayAtQc (p:Test n)(x):GrayTestQc p x=GrayMapQc (p x):=rfl
lemma GrayTQc (p:Test n)(x:Points n):GrayTestQc (tilt x p)=tilt x (GrayTestQc p):=by
 ext1 z; rw [grayAtQc,tilt_pays,tilt_pays]; change _=fderiv ℝ (GrayMapQc ∘ p) z x; rw [fderiv_comp _ GrayMapQc.differentiableAt (diffT p z),GrayMapQc.fderiv]; rfl
lemma GrayCutsQc {K:Payroll n}(b:Bulb){i}(p:Test n)(r:Works b p i)(a c): GrayTestQc (testcut K p b r.cared a c)=testcut K (GrayTestQc p) b (r.via _ (BringQc p).le).cared a c:=by
 ext1 z; rw[grayAtQc,testcut_v,testcut_v,grayAtQc,map_smul]
include v
local notation "gs"=> shade five
lemma GrayCostQc (p:Test n)(X:Fin n→l): S.fee n (fun i=>(gs) (X i)) p=GrayMapQc (S.fee n X (GrayTestQc p)):=by
 rw[Y.price,Y.price]; unfold Test.applyTo; rw[← ContinuousLinearMap.integral_comp_comm _ (BondCostQc (GrayTestQc p) (Y.fee n X) (Y.reg ..))]; apply integral_congr_ae; filter_upwards [rooted_genericQc n] with x z; simp only [v.paper _ X x z,grayAtQc]; change _= Cauchy.Conj.bar (Cauchy.Conj.bar (p x)*_); rw[map_mul,show Cauchy.Conj.bar (Cauchy.Conj.bar (p x))= p x from Complex.conj_conj _] -- tune
lemma GraySpotQc (p:Test n)(X:Fin n→l)(b:l)(i): S.spot (fun j=> gs (X j)) i (gs b) p=GrayMapQc (S.spot X i b (GrayTestQc p)):=by
 rw [spot_cost,spot_cost,← GrayCostQc Y v]; congr 2; ext1 t; by_cases h:t=i <;> simp [h]
lemma GrayPierQc (i:Axis)(b c:l)(h:PierQc (S:=S) i b c): PierQc (S:=S) i (gs b) (gs c):=by
 intro n L k; let X (i:Fin n):= shade five (L i); have hv:(fun i=> gs (X i))=L:=funext fun i=> Calibration.clear ..
 ext1 p; rw[← hv,pays,GraySpotQc Y v,GraySpotQc Y v,h _ _ _,pays,GrayTQc,map_neg]
omit v in
lemma shadeLiftQc (d)(x:UV d): Calibration.lift d (shade d x)=shade five (Calibration.lift d x):= rfl -- bank proof irr
lemma GrayPathQc (a:SymT)(T:Bills)(b c:l)(h:Reaches S (prints a) T b c): Reaches S (prints (tbar a)) T (gs b) (gs c):=by
 intro n L k p t u; let X (i:Fin n):= shade five (L i); have hv:(fun i=> gs (X i))=L:=funext fun i=> Calibration.clear ..
 have r:= u.via (GrayTestQc p) (BringQc p).le
 let B':=update X k b; let L':= update L k (gs b); have he(i j):(fun x=>gs ( (Fathom.add (prints a i j) B') x))=Fathom.add (prints (tbar a) i j) L':=by
    ext1 x; refine Fin.cases ?_ ?_ x
    · exact (shadeLiftQc four _).symm
    intro y; change gs (update X k b y)=L' y; unfold L'; by_cases h':y=k <;> first|subst k; simp only [update_self]| simp only [update_of_ne h']; exact Calibration.clear (L y)
 have hx (i j): GrayMapQc (S.armed (prints a) B' i j (testcut (T n k) (GrayTestQc p) t r.cared i j))= S.armed (prints (tbar a)) L' i j (testcut (T n k) p t u.cared i j):=by
    unfold armed; rw [tagged_cost,tagged_cost, ← GrayCutsQc _ _ u,←he,GrayCostQc Y v]
 calc
    _ = GrayMapQc (S.spot X k c (GrayTestQc p)):=by nth_rw 1 [← hv]; exact GraySpotQc Y v p X c k
    _ = _ := by rw[h n X k (GrayTestQc p) t r, delta,delta,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_sum]; exact Finset.sum_congr rfl fun j _=> hx i j
omit v in
lemma ColorLiftQc (d)(x:UV d): Calibration.lift d (flavors d s x)=flavors five s (Calibration.lift d x):=by
 apply Prod.ext; rfl
 apply Prod.ext; rfl; apply Prod.ext
 · ext1 i; apply Subtype.ext; change (pay (Flavor.bit s⁻¹ i) _: UF d).val=(pay (Flavor.bit s⁻¹ i) _: UF five).val; cases Flavor.bit s⁻¹ i <;> rfl
 ext1 i; apply Subtype.ext; change (pay (Flavor.bit s⁻¹ i) _: UX d).val=(pay (Flavor.bit s⁻¹ i) _: UX five).val; cases Flavor.bit s⁻¹ i <;> rfl
local notation "Fs"=> flavors five s
lemma FlavorQc (p:Test n)(X:Fin n→l): S.fee n (fun i=> (Fs) (X i)) p=S.fee n X p:=by rw[Y.price,Y.price]; apply integral_congr_ae; filter_upwards [rooted_genericQc n] with x z; simp only [v.flavor n s _ x z]
lemma DyeSpotQc (p:Test n)(X:Fin n→l)(b:l)(i): S.spot (fun j=> Fs (X j)) i (Fs b) p=S.spot X i b p:=by
 rw [spot_cost,spot_cost,← FlavorQc Y s v p (update X i b)]; congr 2; ext1 t; by_cases h:t=i <;> simp [h]
omit v in
lemma DyeWakeQc (x:l): Fs (flavors five s⁻¹ x)=x:=by rw [← Module.End.mul_apply,← map_mul, mul_inv_cancel,map_one,Module.End.one_apply]
lemma DyePierQc (i:Axis)(b c:l)(h:PierQc (S:=S) i b c): PierQc (S:=S) i (Fs b) (Fs c):=by
 intro n L k; let X (i:Fin n):=flavors five s⁻¹ (L i); have hv:(fun i=> Fs (X i))=L:=funext fun i=> DyeWakeQc s (L i)
 ext1 p; rw[← hv,pays,DyeSpotQc Y s v,DyeSpotQc Y s v,h _ _ _,pays]
lemma DyeReachQc (a:SymT)(T:Bills)(b c:l)(h:Reaches S (prints a) T b c): Reaches S (prints a) T (Fs b) (Fs c):=by
 intro n L k p t u; let X (i:Fin n):= flavors five s⁻¹ (L i); have hv:(fun i=> Fs (X i))=L:=funext fun i=> DyeWakeQc ..
 let B':=update X k b; let L':= update L k (Fs b); have he(i j):(fun x=>Fs ((Fathom.add (prints a i j) B') x))=Fathom.add (prints a i j) L':=by
    ext1 x; refine Fin.cases ?_ ?_ x
    · simp only [Fathom.add,Fin.cons_zero]; unfold prints pens; rw [←ColorLiftQc,(a.property.1 (ordered i j)).2]
    intro y; change Fs (update X k b y)=L' y; unfold L'; by_cases h':y=k <;> first|subst k; simp| simp only [update_of_ne h']; exact DyeWakeQc s (L y)
 calc
    _ = S.spot X k c p:=by nth_rw 1 [← hv]; exact DyeSpotQc Y s v p X _ _
    _ = _ := by
       rw[h n X k p t u]; unfold delta; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
       change S.tagged B' _ _= S.tagged L' _ _; rw [tagged_cost,tagged_cost,←he,FlavorQc Y s v]
#print axioms GrayPathQc
#print axioms DyeReachQc
end YM.GaugeFieldConstruction.Ember.Hulse
