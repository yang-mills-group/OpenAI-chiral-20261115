import YM.CF.BPress.Weave.Turf
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Haar
/-! canonical measures with independent draws per column. π over one Hcols also in Gaussian sectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
-- port budget and νv dimensions fixed by B.D. n_ang B.D, =3*D*finrank ℝ su(5).
variable {s: Side}{B:BandWidth}(X:Bands s B)
abbrev Hub (D:ℕ):= Fin D × SpatialDir
abbrev Stack (D:ℕ):= Hub D × group.ColorIndex
abbrev Pack (D:ℕ):=EuclideanSpace ℝ (Stack D)
abbrev Market (D:ℕ):= Hub D→ SU.E
abbrev Strings (D:ℕ):= Hub D→ink
abbrev Fills := X.Hcols→Pack B.D
abbrev Offers := X.Hcols→ Market B.D
lemma ticket_stack (D:ℕ): Fintype.card (Stack D)= n_ang D:=by simp [Stack,Hub,SpatialDir,ColorIndex]
lemma pack_n (D:ℕ) : Module.finrank ℝ (Pack D)= n_ang D:= by simp [Pack, ticket_stack]
def stem : Axon X≃ (X.Hcols × Stack B.D):= Equiv.prodAssoc ..
lemma stem_expr (x:Axon X): stem X x=(zSite X x,(x.1.2,x.2)):=rfl
def Rainy (D:ℕ):Measure (Market D):= Next.SectorChange.piHaar group _
instance (D:ℕ): IsProbabilityMeasure (Rainy D):= by unfold Rainy; infer_instance
def Rains : Measure (Offers X):= Measure.pi fun _=> Rainy B.D
instance : IsProbabilityMeasure (Rains X):= by unfold Rains; infer_instance

def heart : Bills X SU.E ≃ᵐ Offers X:= MeasurableEquiv.curry ..
section generic
variable (I J : Type)[Fintype I][Fintype J]{α: Type}[MeasurableSpace α]
-- expand YM.Conn...
lemma currMP (p : Measure α)[SigmaFinite p] : MeasurePreserving (MeasurableEquiv.curry I J α).symm (Measure.pi (fun _ : I=> Measure.pi (fun _ : J=> p))) (Measure.pi (fun _:I×J=>p)):= by
 let e:= MeasurableEquiv.curry I J α; refine ⟨e.symm.measurable,(Measure.pi_eq ?_).symm⟩; intro s hs; let X:= Set.univ.pi s; let U i := Set.univ.pi (fun j:J=> s (i,j)); have he:e.symm ⁻¹' X=Set.univ.pi U:=by ext x; exact ⟨fun h i _ j _=> h (i,j) (Set.mem_univ _),fun h i _=> h i.1 (Set.mem_univ _) i.2 (Set.mem_univ _)⟩
 rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs),show e.symm ⁻¹' (Set.univ.pi s)= Set.univ.pi U from he] -- e not expression
 rw [Measure.pi_pi,Fintype.prod_prod_type]; refine prod_congr rfl fun i _=> Measure.pi_pi ..

def slides : EuclideanSpace ℝ (I×J) ≃ᵐ (I → EuclideanSpace ℝ J):= (((MeasurableEquiv.toLp 2 _).symm).trans (MeasurableEquiv.curry ..)).trans (MeasurableEquiv.piCongrRight fun _=> MeasurableEquiv.toLp 2 _)
lemma sliding : MeasurePreserving (slides I J):=by
 have he: MeasurePreserving (MeasurableEquiv.piCongrRight fun _:I => MeasurableEquiv.toLp 2 (J→ℝ)) := measurePreserving_pi _ _ (fun _:I => (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp J).symm)
 exact he.comp ((currMP I J (volume (α:=ℝ))).symm.comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (I×J)))
end generic
-- note X.Rain simple piHaar defeq pi invariant even if Bills excluded.
lemma heart_mp : MeasurePreserving (heart X) (Next.SectorChange.piHaar group X.Air) (Rains X):= (currMP X.Hcols (Hub B.D) group.probHaar).symm

def offer : RaySpace X ≃ᵐ Fills X:= (((MeasurableEquiv.toLp 2 _).symm.trans (MeasurableEquiv.piCongrLeft (fun _=>ℝ) (stem X))).trans (MeasurableEquiv.toLp 2 _)).trans (slides X.Hcols (Stack B.D))
lemma offer_hit (v:RaySpace X)(i:Axon X): offer X v (zSite X i) (fiberZ X i)=v i:=by
 change (MeasurableEquiv.piCongrLeft (fun _=>ℝ) (stem X)) _ (stem X i)=_; rw [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_apply]
lemma offer_symm (v:Fills X)(i: Axon X) : (offer X).symm v i=v (zSite X i) (fiberZ X i):= by rw [← offer_hit,(offer X).apply_symm_apply]
lemma offers : MeasurePreserving (offer X):= (sliding ..).comp ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm.comp ((volume_measurePreserving_piCongrLeft (fun _=>ℝ) (stem X)).comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Axon X))))

variable (D:ℕ)
def colorsT : Pack D≃ᵐ Strings D:=slides (Hub D) group.ColorIndex
lemma slidesT : MeasurePreserving (colorsT D):= sliding ..
@[simp] lemma colorL (x:Pack D)(i:Hub D)(j:group.ColorIndex): colorsT D x i j=x (i,j):=rfl
lemma chart_ray (x:RaySpace X)(i:X.Air): lead X x i=colorsT B.D (offer X x i.1) i.2:=PiLp.ext fun j=> (offer_hit X x (i,j)).symm
lemma color_n (x:Pack D): ‖x‖^2=∑ i:Hub D, ‖colorsT D x i‖^2:=by rw [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]; exact sum_congr rfl fun i _=> (EuclideanSpace.norm_sq_eq (colorsT D x i)).symm
lemma c_bound (x:Pack D)(i:Hub D): ‖colorsT D x i‖≤ ‖x‖:= (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [color_n D]; exact single_le_sum (f:= fun i=> ‖colorsT D x i‖^2) (fun i _=> sq_nonneg _) (mem_univ i))
lemma ray_offer (v:RaySpace X) : ‖v‖^2= ∑ i, ‖offer X v i‖^2:=by rw [ray_price,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [color_n B.D]; refine sum_congr rfl fun j _=>?_ ; rw [chart_ray]
lemma ray_part (S:Finset X.Hcols)(v:RaySpace X)(i:X.Hcols) : offer X (keepOnly X S v) i= if i∈ S then offer X v i else 0:=by
 ext1 j; by_cases p:i∈ S <;> split_ifs; · rw [show offer X (keepOnly X S v) i j=_ from offer_hit X (keepOnly X S v) ((i,j.1),j.2), show offer X v i j=_ from offer_hit X v ((i,j.1),j.2)]; exact if_pos p -- tune
 rw [show offer X (keepOnly X S v) i j=_ from offer_hit X (keepOnly X S v) ((i,j.1),j.2)]; exact if_neg p
lemma sect_norm (S:Finset X.Hcols)(v:RaySpace X): ‖keepOnly X S v‖^2 = ∑ i∈S, ‖offer X v i‖^2:=by
 rw [ray_offer]; simp_rw [ray_part]; calc ∑ i:X.Hcols, (‖if i∈ S then offer X v i else 0‖)^2 = ∑ i:X.Hcols,(if i∈ S then ‖offer X v i‖^2 else 0):=sum_congr rfl fun i _=>by split; rfl; simp -- tune
                                          _ = _:=by rw [← sum_filter]; simp
end YM.CF.BPress.Port
