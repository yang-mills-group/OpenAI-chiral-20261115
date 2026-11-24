/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.YachtYikesMars
/-
 # Spatial/angular read. velocity argument adapts repository YM.Work.A14.lean.
 Defunctionalize UV to finite rank parameters, explicit norms below.
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

variable (p)
abbrev compassPiMars : SO→* Module.End ℂ ΧiMars:= p.path.portico.castP
lemma sailPiMars (A:ΧiMars) (Ω:Ortho.Skew)(t:ℝ): Sends (fun s=> compassPiMars p (Angles.rise Ω s) A) t (p.path.pi Ω four (compassPiMars p (Angles.rise Ω t) A)):= p.path.portico.map_spH Ω A t
lemma sailOneMars (A:ΧiMars) : compassPiMars p 1 A=A:=by rw [map_one]; rfl
lemma sailMulMars (A:ΧiMars)(r s:SO): compassPiMars p (r*s) A=compassPiMars p r (compassPiMars p s A):=by rw[map_mul]; rfl
abbrev grainMars := SpeckMars →ℂ
noncomputable def FreightMars : ΧiMars≃ₗ[ℂ] grainMars:= UrBMars.equivFun
lemma shipPioMars (A:ΧiMars)(Ω:Ortho.Skew)(t):HasDerivAt (fun s=> FreightMars (compassPiMars p (Angles.rise Ω s) A)) (FreightMars (p.path.pi Ω four (compassPiMars p (Angles.rise Ω t) A))) t := hasDerivAt_pi.mpr (fun i=>(sailPiMars p A Ω t) ((LinearMap.proj (φ:=fun _ : SpeckMars => ℂ) i:grainMars→ₗ[ℂ]ℂ) ∘ₗ FreightMars.toLinearMap))
variable {p}
private def wholeMoon (p:Ticket u C)(Y:AreaQc S)(x:Points n×(Fin n→grainMars)):= TerraMars p Y (FreightMars.symm ∘ x.2) x.1
private def writMoon (p:Ticket u C)(Y:AreaQc S)(x:Points n)(hx:x∈conf n): MultilinearMap ℂ (fun _ : Fin n=>grainMars) ℂ:= (linearGownMoon p Y x hx).compLinearMap (fun _ : Fin n=>FreightMars.symm.toLinearMap)
private lemma writtenMoon (V:Fin n→grainMars) {x:Points n}(hx:x∈conf n): writMoon p Y x hx V=wholeMoon p Y (x,V):=rfl
private lemma continuumMoon (V:Fin n→grainMars) {x:Points n}(hx:x∈conf n):ContDiffAt ℝ ∞ (wholeMoon p Y) (x,V):=by
 let B(i:SpeckMars):grainMars:= Pi.single i 1
 let v (ρ:Fin n→SpeckMars):Fin n→grainMars:= B ∘ ρ
 let X:=Points n × (Fin n→grainMars); let K (ρ:Fin n→SpeckMars)(y:X):=(∏ i:Fin n, y.2 i (ρ i)) * TerraMars p Y (FreightMars.symm ∘ v ρ) y.1
 have he (q:Fin n→SpeckMars):ContDiffAt ℝ ∞ (K q) (x,V):=by
    refine (contDiffAt_prod (fun i _=>?_)).mul ((TerraAt p Y _ _ hx).comp (x,V) contDiffAt_fst)
    let A: grainMars→L[ℝ]ℂ:= ContinuousLinearMap.proj (q i); let D:(Fin n→grainMars)→L[ℝ]grainMars:=ContinuousLinearMap.proj i
    exact ((A.comp D).contDiff.contDiffAt.comp (x,V) contDiffAt_snd)
 apply (ContDiffAt.sum (fun i (_:i∈(Finset.univ:Finset (Fin n→SpeckMars)))=>he i)).congr_of_eventuallyEq
 filter_upwards [(continuous_fst.continuousAt (x:=(x,V))).tendsto.eventually ((conf_open n).mem_nhds hx)] with w hw; obtain ⟨y,G'⟩:= w; change y∈conf n at hw
 let F(i:Fin n)(j:SpeckMars):grainMars:= G' i j • B j; have hf(i:Fin n): G' i=∑ j:SpeckMars,F i j:=by
    ext1 b; simp [F,B,Finset.sum_apply, Pi.single_apply] -- tune.
 rw [← writtenMoon G' hw]; change writMoon p Y y hw G'=_; conv_lhs=> rw[show G'=fun i=>∑ j:SpeckMars,F i j from funext hf]
 simp_rw[MultilinearMap.map_sum]; apply sum_congr rfl; intro i _; exact (writMoon p Y y hw).map_smul_univ (fun j=>G' j (i j)) (v i) -- tune
private lemma movingBills (t:ℝ)(W:ℝ→Fin n→grainMars)(D:Fin n→grainMars)(v:HasDerivAt W D t)(x:Points n)(hx:x∈conf n): HasDerivAt (fun s:ℝ=> wholeMoon p Y (x,W s)) (∑ i,wholeMoon p Y (x, update (W t) i (D i))) t:=by
 let Q:ContinuousMultilinearMap ℝ (fun _ : Fin n=> grainMars) ℂ:={
    toMultilinearMap:=(writMoon p Y x hx).restrictScalars ℝ
    cont:=continuous_iff_continuousAt.mpr fun w:Fin n→grainMars=> ((continuumMoon (p:=p) (Y:=Y) w hx).comp w (contDiffAt_const.prodMk contDiffAt_id)).continuousAt }
 have he: HasDerivAt (fun s=>wholeMoon p Y (x,W s)) (Q.linearDeriv (W t) D) t := (Q.hasFDerivAt _).comp_hasDerivAt t v
 rw [ContinuousMultilinearMap.linearDeriv_apply] at he; exact he
/-- Positions have velocity Kx (evaluated at the moving point). -/
private theorem velocity (K : Ortho.Skew) (x : Points n) (t : ℝ) :
    HasDerivAt (fun s => NSF.Points.move (Ortho.oneParameter K s) x)
      (points fun i => M4.move K.val ((NSF.Points.move (Ortho.oneParameter K t) x) i)) t := by
  let A : M4 →L[ℝ] Points n := LinearMap.toContinuousLinearMap {
    toFun m := points fun i => M4.move m (x i)
    map_add' m l := by
      ext1 i
      change (Matrix.toEuclideanLin (m+l)) (x i) =
        (Matrix.toEuclideanLin m) (x i) + (Matrix.toEuclideanLin l) (x i)
      rw [map_add, LinearMap.add_apply]
    map_smul' a m := by
      ext1 i
      change (Matrix.toEuclideanLin (a • m)) (x i) = a • (Matrix.toEuclideanLin m) (x i)
      rw [map_smul, LinearMap.smul_apply] }
  have he : HasDerivAt (fun s => NSF.Points.move (Ortho.oneParameter K s) x)
      (A (K.val * NormedSpace.exp (t • K.val))) t :=
    A.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' K.val t)
  have hm : A (K.val * NormedSpace.exp (t • K.val)) =
      points fun i => M4.move K.val ((NSF.Points.move (Ortho.oneParameter K t) x) i) :=
    PiLp.ext fun i => M4.move_mul K.val (NormedSpace.exp (t • K.val)) (x i)
  rw [hm] at he
  exact he


include H G
lemma VenusRiseMars (t:ℝ)(x:Points n)(hx:x∈conf n)(F:Fin n→ΧiMars)(K:Ortho.Skew): HasDerivAt (fun s:ℝ=>TerraMars p Y (compassPiMars p (Angles.rise K s) ∘ F) (NSF.Points.move (Ortho.oneParameter K s) x)) 0 t:=by
 let V (s:ℝ):Fin n→ΧiMars:= compassPiMars p (Angles.rise K s) ∘ F; let W (s:ℝ):Fin n→grainMars:=FreightMars ∘ V s; let y (s:ℝ):= NSF.Points.move (Ortho.oneParameter K s) x; let R:= velocityMars K (y t); let B(i:Fin n):=p.path.pi K four (V t i); let dv (i:Fin n):= FreightMars (B i);
 let f (s:ℝ):= TerraMars p Y (V s) (y s); let g(s:ℝ):=wholeMoon p Y (y s,W s); have he (u:ℝ)(w:Points n): wholeMoon p Y (w,W u)=TerraMars p Y (V u) w:=congrArg (fun v=>TerraMars p Y v w) (funext fun i=> FreightMars.symm_apply_apply _)
 change HasDerivAt f _ _; rw[show f=g from funext fun i=>(he i (y i)).symm]; have hx': y t∈conf n:=NSF.Points.move_in _ hx
 let D:= fderiv ℝ (wholeMoon p Y) (y t,W t); have hD: HasFDerivAt _ D (y t,W t):=((continuumMoon (p:=p) (Y:=Y) (W t) hx').differentiableAt (by simp)).hasFDerivAt
 have hv:HasDerivAt y R t:= velocity K x t; have hb:HasDerivAt W dv t := hasDerivAt_pi.mpr fun i=> shipPioMars p (F i) K t
 have ha: HasDerivAt g (D (R,dv)) t:=HasFDerivAt.comp_hasDerivAt (l:=wholeMoon p Y) t hD (hv.prodMk hb)
 apply ha.congr_deriv
 rw [show D (R,dv)= D (R,0)+D (0,dv) from by rw [←map_add]; simp]
 have hm: HasDerivAt (fun s=> wholeMoon p Y (y t, W s)) (D (0,dv)) t:= HasFDerivAt.comp_hasDerivAt (l:=wholeMoon p Y) t hD ((hasDerivAt_const t (y t)).prodMk hb)
 rw[hm.unique (movingBills t W dv hb (y t) hx')]; have hy:HasDerivAt (fun s=> wholeMoon p Y (y s,W t)) (D (R,0)) t := HasFDerivAt.comp_hasDerivAt (l:=wholeMoon p Y) t hD (hv.prodMk (hasDerivAt_const t (W t)))
 simp_rw[he] at hy; rw[hy.unique (((TerraAt p Y (V t) (y t) hx').differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hv)]
 have hp:=portBillMars H G (V t) K (y t) hx'; change Analysis.D _ _ _ +_= _; rw [hp];
 apply neg_add_eq_zero.mpr; apply sum_congr rfl; intro i _; refine congrArg (fun v=>TerraMars p Y v (y t)) ?_
 funext j; by_cases h:j=i
 · subst j; simp only [update_self,comp_apply]; exact (FreightMars.symm_apply_apply _).symm -- tune
 simp only [update_of_ne h,comp_apply]; exact (FreightMars.symm_apply_apply _).symm
#print axioms VenusRiseMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
