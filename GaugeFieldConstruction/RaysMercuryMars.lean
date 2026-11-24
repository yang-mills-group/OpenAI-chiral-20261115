import GaugeFieldConstruction.LotusTensorMars
/-!
 # rotate shell with this stress. definition preserving convention. point 
 identity with all exterior fields in ΧiMars. Divergence similarly
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable {p:Ticket u C}{Y:AreaQc S}
namespace FirstPackMars
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y))
open Loft
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg



variable (g:SO)(k:Fin n)(F:Fin n→ΧiMars)(x:Points n)(hx:x∈conf n)
abbrev VenusInvMars (g:SO):= (HueTurnsMars (1:Ortho)) g⁻¹ -- convenient? unused
abbrev mercuryMars (g:SO):=Ortho.motion g.val
def VoyageMars (g: SO): Points n→L[ℝ] Points n:= LinearMap.toContinuousLinearMap {
 toFun:=motionMoonMars g
 map_add' a b:= PiLp.ext fun i=>(mercuryMars g).map_add (a i) (b i)
 map_smul' c a:=PiLp.ext fun i=> (mercuryMars g).map_smul c (a i) }
lemma LunarwayMars (x:Points n): motionMoonMars g⁻¹ (motionMoonMars g x)=x:= (WindyMissionMars g⁻¹ g x).symm.trans ((congrArg (fun g=>motionMoonMars g x) (inv_mul_cancel _)).trans (calend_oneMars _))
lemma mrVelMars (a:Axis) : mercuryMars g (YM.basis a)=∑ j:Axis,g.val.val j a • YM.basis j:=by
 ext1 i; change M4.move _ (YM.basis a) i= _; simp -- tune
lemma mrColumnMars (a:Axis): VoyageMars g (direction k a)=∑ j:Axis,g.val.val j a • direction k j :=by
 ext1 i; change mercuryMars g ((direction k a) i)=_
 by_cases h:i=k
 · subst k; rw [Points.direction,PiLp.single_eq_same,mrVelMars]; simp[Points.direction]
 rw [Points.direction,PiLp.single_eq_of_ne _ h,map_zero]; simp[Points.direction,h] -- tune names
include H G hx
lemma OrbitTrackMars (i:Axis): Analysis.D (direction k i) (TerraMars p Y F) x= ∑ a:Axis,g.val.val a i • Analysis.D (direction k a) (TerraMars p Y (compassPiMars p g ∘ F)) (motionMoonMars g x) :=by
 let L:=VoyageMars (n:=n) g; let R:= TerraMars p Y (compassPiMars p g ∘ F); rw[GermD _ (show TerraMars p Y F=ᶠ[𝓝 x](R ∘ L) from ((conf_open _).eventually_mem hx).mono (fun i t=>(VitaPiiotMars H G g _ F i t).symm))]; unfold D; rw [fderiv_comp x (show DifferentiableAt ℝ R (L x) from (TerraAt p Y _ _ (NSF.Points.move_in _ hx)).differentiableAt (by simp)) L.differentiableAt,ContinuousLinearMap.comp_apply,L.fderiv]; unfold L; rw [mrColumnMars,map_sum]; simp_rw [map_smul]; rfl
omit H G hx
variable {g}
variable (b:Bulb)(h:BreatherMars b k x)
def FlameMoonMars (g:SO): Bulb:=
 { f:= b.f ∘ (mercuryMars g)
   d:= b.d.comp (mercuryMars g).toContinuousLinearEquiv.contDiff
   c:= b.c.comp_homeomorph (mercuryMars g).toHomeomorph }
abbrev grainRayMars (v:Ortho)(a i:Axis):ℝ:=v.val a i
lemma burnRateMars (i:Axis)(g:SO)(p:E4): D (YM.basis i) (FlameMoonMars b g).f p=∑ a:Axis,grainRayMars g.val a i • D (YM.basis a) b.f (mercuryMars g p):=by
 let T: E4 →L[ℝ] E4:= (mercuryMars g).toLinearIsometry.toContinuousLinearMap
 change fderiv ℝ (b.f ∘ T) p (basis i)=_; unfold D; rw [fderiv_comp _ (b.d.differentiable (by simp) _) T.differentiableAt,T.fderiv,ContinuousLinearMap.comp_apply]; change fderiv ℝ b.f (mercuryMars g p) (mercuryMars g (basis i))=_; rw[mrVelMars,map_sum]; simp_rw [map_smul]; -- tune
variable (g)
include h
lemma sparkTiltMars : BreatherMars (FlameMoonMars b g) k (motionMoonMars g⁻¹ x):=by
 have v(i:Fin n): mercuryMars g ((motionMoonMars g⁻¹ x) i)=x i:=Ortho.move_inv g.val (x i)
 have ht(i:Fin n):Tendsto (mercuryMars g) (𝓝 ((motionMoonMars g⁻¹ x) i)) (𝓝 (x i)):= (v i ▸ (mercuryMars g).continuous.continuousAt) -- tune
 refine ⟨NSF.Points.move_in _ h.bounds,h.home.comp_tendsto (ht k),fun i v=>?_⟩
 exact notMem_tsupport_iff_eventuallyEq.mpr ((notMem_tsupport_iff_eventuallyEq.mp (h.apart i v)).comp_tendsto (ht i))
-- nicer Flux notation
omit h
variable (p Y)
abbrev WheyMars (i:Axis)(A:ΧiMars)(z:E4):ℂ:= D (basis i) b.f z • TerraMars p Y (Fin.cons A F) (Points.cons z x)
abbrev FlossMars (i:Axis)(A:ΧiMars):= ∫ y:E4, WheyMars p Y F x b i A y
include h
lemma WheyCanMars (i A): Integrable (WheyMars p Y F x b i A) := by
 let W:=SoilMars (TerraMars p Y (Fin.cons A F)) (Payroll.ticket i) b i i
 let U: Set (Points n):= {x| BreatherMars b k x}
 have he : Integrable (fun y:E4=> W (y,x)) := CohortMars W U _ (LED b i).c (fun _ z=> SoilCapMars _ (TerraSm p Y _) _ _ _ _ _ _ z) (fun x _ y hy=>SoilAreaMars _ _ _ i i y hy x) x h
 have H': WheyMars p Y F x b i A = fun y:E4=> W (y,x):=by
    ext1 y; change _=(D _ _ _ * basis i i) • _; rw [show basis i i=1 by simp,mul_one]; rfl
 rw [H']; exact he
lemma PoemMoonMars (i:Axis): Analysis.D (direction k i) (TerraMars p Y F) x=∑ a:Axis,FlossMars p Y F x b a (p.J a i):=by
 rw [EnrobeMars p Y k F x b h]; apply sum_congr rfl; intro a _; apply integral_congr_ae; refine Eventually.of_forall fun s=> ?_; change (D _ _ _ * basis i i) • _=_; rw [show basis i i=1 by simp,mul_one]; rfl
omit h
noncomputable def FlintMars(k:Fin n)(h:BreatherMars b k x)(i:Axis): ΧiMars→ₗ[ℂ]ℂ where
 toFun:=FlossMars p Y F x b i
 map_add' A B:=by
    rw[FlossMars,← integral_add (WheyCanMars p Y k F x b h i A) (WheyCanMars p Y k F x b h i B)]
    apply integral_congr_ae; refine Eventually.of_forall fun y=>?_ -- tune
    by_cases u:D (basis i) b.f y=0
    · simp [WheyMars,u]
    have w:= RoomMars b k x h y (cone b i (subset_tsupport _ (show (LED b i).f y≠0 from u)))
    let R:ΧiMars→ₗ[ℂ]ℂ:= (linearGownMoon p Y _ w).toLinearMap (Fin.cons 0 F) 0
    have H (x':ΧiMars): WheyMars p Y F x b i x' y=D (basis i) b.f y • R x' := by unfold WheyMars R; rw [MultilinearMap.toLinearMap_apply,Fin.update_cons_zero]; rfl
    dsimp only; rw[H,H,H,map_add, smul_add] -- tune
 map_smul' c A:=by
    unfold FlossMars; rw [RingHom.id_apply, ← integral_smul c]; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_
    by_cases u:D (basis i) b.f y=0
    · simp [WheyMars,u]
    have w:= RoomMars b k x h y (cone b i (subset_tsupport _ (show (LED b i).f y≠0 from u)))
    let R:ΧiMars→ₗ[ℂ]ℂ:= (linearGownMoon p Y _ w).toLinearMap (Fin.cons 0 F) 0
    have H (x':ΧiMars): WheyMars p Y F x b i x' y=D (basis i) b.f y • R x' := by unfold WheyMars R; rw[MultilinearMap.toLinearMap_apply,Fin.update_cons_zero]; rfl
    dsimp only; rw[H,H,map_smul]; exact smul_comm _ _ (_:ℂ)
#check FlintMars
#print axioms FlintMars
#print axioms OrbitTrackMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
