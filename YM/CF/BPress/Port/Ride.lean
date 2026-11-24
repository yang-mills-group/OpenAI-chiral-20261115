import YM.CF.BPress.Port.Leave
/-! Exact transport starting with input integral over Offers X. Keep original dummy Haar; never sum gauges inside phase cancellation. All W-space/scaling product densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(κ y:ℝ)(S:Seal X.Hcols)

abbrev Quarters := Fills X × Offers X
abbrev demand {I E:Type*}[Fintype I][MeasurableSpace E](μ : I→Measure E)(C:I→E→ℝ):=Measure.pi fun i=>(μ i).withDensity (ENNReal.ofReal ∘ C i)
-- total weights special
abbrev coordinate (x:Fills X)(f:X.Hcols→Pack B.D→ℝ) := ∏ i,f i (x i)
def harbour : Measure (Quarters X):= volume.prod (Rains X)
instance : SigmaFinite (harbour X):=by
 unfold harbour; change SigmaFinite ((volume:Measure (Fills X)).prod (Rains X)); haveI : SigmaFinite (volume : Measure (Fills X)):= by rw [volume_pi]; infer_instance
 infer_instance
def knell := (Measure.pi fun _:X.Hcols=> volts B.D y).prod (Rains X)
instance : IsProbabilityMeasure (knell X y):=by unfold knell; infer_instance

def ratev (u:X.Hcols) : Pack B.D→ℝ := if u∈S then vcost B.D y else billH B.D J y
def carriage := (demand (fun _:X.Hcols=>volume) (ratev X J y S)).prod (Rains X)
def sail (i:X.Hcols) := if i∈ S then (Set.univ : Set (Market B.D)) else pullCover B.D J y
def court := Set.univ.pi (sail X J y S)
variable (p:0<y)(r:LocalRatio J)
include r in
lemma courts_meas : MeasurableSet (court X J y S):= MeasurableSet.univ_pi (fun i=>by unfold sail; split; exact MeasurableSet.univ; exact pull_cover B.D J y r) -- incl
include p r in
lemma rose_finite : IsFiniteMeasure (volume.withDensity (ENNReal.ofReal ∘ billH D J y)) := by
 let T:=rose_mp D J y r p; apply (Measure.isFiniteMeasure_map_iff (T.aemeasurable)).mp; rw [T.map_eq]; infer_instance
include r p
lemma voyage_mp : MeasurePreserving (uncurry (issueT X y S)) (carriage X J y S) ((Rains X).restrict (court X J y S)):=by
 let ν:=Rainy B.D; let h(i:X.Hcols):=volume.withDensity (ENNReal.ofReal ∘ ratev X J y S i); let g(i:X.Hcols)(x:Pack B.D×Market B.D):=if i∈ S then x.2 else rose B.D y x.1; haveI hi(i): SigmaFinite (h i):= by unfold h ratev; split; change SigmaFinite (volts B.D y); infer_instance; haveI:=rose_finite B.D J y p r; infer_instance
 have H(i:X.Hcols): MeasurePreserving (g i) ((h i).prod ν) (ν.restrict (sail X J y S i)):=by by_cases p':i∈ S; unfold g h sail ratev; simp only [p',if_true]; rw [Measure.restrict_univ]; exact (show MeasurePreserving Prod.snd ((volts B.D y).prod ν) ν from measurePreserving_snd); unfold g h sail ratev; simp only [p', if_false]; refine (rose_mp B.D J y r p).comp ?_; haveI:=rose_finite B.D J y p r; exact measurePreserving_fst
 let V := MeasurableEquiv.arrowProdEquivProdArrow (Pack B.D) (Market B.D) X.Hcols; have hi:= (measurePreserving_pi _ _ H).comp (measurePreserving_arrowProdEquivProdArrow _ _ _ h (fun _=>ν)).symm; unfold Rains court; rw [Measure.restrict_pi_pi]; exact hi -- tune
omit r p
section pi
lemma treasury (F:X.Hcols→Pack B.D→ℝ) (p:∀ i, Measurable (F i))(v:∀ i j,0 ≤ F i j): (demand (fun _:X.Hcols=> volume) F).prod (Rains X) = (harbour X).withDensity (fun u=>ENNReal.ofReal (coordinate X u.1 F)):=by
 let q (i):= ENNReal.ofReal ∘ F i; haveI ht(i:X.Hcols) : SigmaFinite (volume.withDensity (q i)):= SigmaFinite.withDensity_ofReal (F i) -- tune
 have he : (volume:Measure (Fills X)).withDensity (fun x=> ∏ i, q i (x i))=demand (fun _=>volume) F:= Work.F05.piDensity _ _ (fun i=>(p i).ennreal_ofReal); rw [←he, prod_withDensity_left]; unfold harbour coordinate; apply congrArg (Measure.withDensity _); ext x; exact (ENNReal.ofReal_prod_of_nonneg (fun i _=>v i (x.1 i))).symm; exact Finset.measurable_fun_prod _ (fun i _=> ((p i).ennreal_ofReal.comp (measurable_pi_apply i))) -- tune
end pi

lemma km : knell X y= (harbour X).withDensity (fun u=> ENNReal.ofReal (coordinate X u.1 (fun _=> vcost B.D y))) := treasury X _ (fun _=>v_meas ..) (fun _ j=> v_nonneg B.D y j)
lemma rate_nn (p:0<y)(r:LocalRatio J) (i:X.Hcols)(v:Pack B.D): 0≤ ratev X J y S i v:=by unfold ratev; split; exact v_nonneg ..; exact positive_bill B.D J y r p v
include r p
lemma cm : carriage X J y S= (harbour X).withDensity (fun u=> ENNReal.ofReal (coordinate X u.1 (ratev X J y S))) := treasury X _ (fun i=>by unfold ratev; split; exact v_meas ..; exact billH_meas B.D J y r) (rate_nn X J y S p r)
end YM.CF.BPress.Port
