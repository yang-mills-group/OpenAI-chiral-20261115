import WakeRoad.Canopy
import WakeRoad.Four
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
variable {q:Clip}{n:Side}{M:Bed}{Z:PathData SU.group}{η C σ θ w a : ℝ}
variable (B:Z.Bounds q θ w a)(P:Attached M Z)(D:Floor M q n η C)(U:M.covered σ C)(e:0<σ)(h:Even n.val)
local notation "I"=> SU.group.ColorIndex
include D U e h
lemma limb_component (F E:Face (Per n))(i j:I)(u:ℝ):
    (↑(inner ℝ (plar B P (F.1,plaquette F.2) u i) (plar B P (E.1,plaquette E.2) u j)):ℂ)=(u:ℂ)^2*sch (G:=SU.group) i j * rimble n M (F.1,plaquette F.2) (E.1,plaquette E.2) := by
 let Q:= (F.1,plaquette F.2); let S:= (E.1,plaquette E.2); have he:= chimes B P D U e i j Q S h; simp_rw [←joy,appraisal] at he; unfold plar; rw [real_inner_smul_left (trill B P i _) (u • trill B P j _) u,real_inner_smul_right (trill B P i _) (trill B P j _) u]; change (↑(u*(u*inner ℝ (trill B P i Q) (trill B P j S))):ℂ)=_; push_cast; rw [he]; ring
omit D U e h

def wickTranche (C:Fin 4→ Fin 4→ℂ):ℂ:= C 0 1*C 2 3+C 0 2*C 1 3+C 0 3*C 1 2
abbrev coupon (F:Face (Per n))(E:Face (Per n))(b d:I)(M:Bed):ℂ:= (sch (G:=SU.group) b d:ℂ)*rimble n M (F.1,plaquette F.2) (E.1,plaquette E.2)
lemma inBasin {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](W: swatches 4→ℂ)(x:Fin 4→I→ E):
    let X(u:E):=fun i:fibers 4=> inner ℝ (x i.1 i.2) u
    (∫ u:E, Hearth.brush W (X u) ∂ stdGaussian E)=
      ∑ c:swatches 4, wickTranche (fun t v=>(↑(inner ℝ (x t (c t)) (x v (c v))):ℂ))*W c:=by
 intro X; let μ:=stdGaussian E
 let G(c:swatches 4)(u:E):=∏ i:Fin 4,(↑(X u (i,c i)):ℂ)
 let V(c:swatches 4)(i:Fin 4)(u:E):=inner ℝ (x i (c i)) u
 have hp(c u): G c u = (↑(V c 0 u*V c 1 u*V c 2 u*V c 3 u):ℂ):=by unfold G V X; simp only [Fin.prod_univ_succ,Finset.univ_eq_empty (α:=Fin 0),Finset.prod_empty]; push_cast; -- successors
                                                                            ring
 let h(c:swatches 4):= moments (x 0 (c 0)) (x 1 (c 1)) (x 2 (c 2)) (x 3 (c 3))
 have he(c:swatches 4): Integrable (G c) μ:=by rw [show G c=(fun t=> (↑(V c 0 t*V c 1 t*V c 2 t*V c 3 t):ℂ)) from funext (hp c)]; exact (h c).1.ofReal (𝕜:=ℂ)
 have hc(c:swatches 4) : (∫ u,G c u∂ μ)= wickTranche (fun i j=>(↑(inner ℝ (x i (c i)) (x j (c j))):ℂ)):=by simp_rw [hp,integral_complex_ofReal]; rw [(h c).2]; unfold wickTranche; push_cast; rfl
 unfold Hearth.brush; change (∫ u:E, (∑ c:swatches 4, G c u*W c) ∂μ)=_; rw [integral_finsetSum _ (fun i _=>(he i).mul_const _)]; exact sum_congr rfl fun i _=> by rw [integral_mul_const,hc]
#print axioms inBasin
variable {m:Side}
lemma dry_clock (x:ℂ)(C:Fin 4→Fin 4→ℂ): wickTranche (fun i j=>x^2*C i j)=x^4*wickTranche C:=by unfold wickTranche; ring
lemma steer_four (G:Fin 4 → Staff)(ρ:ℝ) (W:swatches 4→ℂ)(D:Floor M q (More m) η C)(U:M.covered σ C)(e:0<σ) : let V:=stamen B P (More m); (∫ x:V, (propel G m).basin ρ (Hearth.brush W) q x.val ∂ stdGaussian V)=
    (ρ:ℂ)^4 * ∑ c:swatches 4, wickTranche (fun i j=> coupon ((G i).localFace m) ((G j).localFace m) (c i) (c j) M)*W c:=by
 intro V
 let v:= fun i=> (G i).localFace m
 let F:=propel G m; let Y(i:Fin 4)(j:I): V:=plar B P ((v i).1, plaquette (v i).2) ρ j
 have he(u:V): F.basin ρ (Hearth.brush W) q u.val= Hearth.brush W (fun i=> inner ℝ (Y i.1 i.2) u):=by
   let f:=tiler B P (n:=More m); obtain ⟨t,rfl⟩:= f.surjective_rangeRestrict u; change F.basin ρ (Hearth.brush W) q (tiler B P t) = _; rw [Vessel.belly B P F]; congr 1; funext i
   have hp: elbow B P ((v i.1).1,plaquette (v i.1).2) ρ (f.rangeRestrict t) = ρ • Regis.Head.Etch.river q ((v i.1).1,(v i.1).2) (f.rangeRestrict t).val := bare_elbow B P (f.rangeRestrict t); have hx:= congrArg (fun x:SU.group.Color=> x i.2) hp; rw [show Regis.Head.Etch.river q _ (f.rangeRestrict t).val= _ from Regis.Head.Etch.river_now q B P (v i.1) t] at hx; exact hx.symm
 change (∫ x:V,F.basin ρ (Hearth.brush W) q x.val∂stdGaussian V)=_; simp_rw [he]; rw [show (∫ y:V, _ ∂stdGaussian V)=_ from inBasin W Y,mul_sum]; refine sum_congr rfl fun i _=>?_ ; have h: Even (More m).val:=⟨m.val,by change m.val*2=_; omega⟩
 have ht(a b:Fin 4):(↑(inner ℝ (Y a (i a)) (Y b (i b))):ℂ)=(ρ:ℂ)^2*coupon (v a) (v b) (i a) (i b) M:=by unfold Y coupon; rw [limb_component B P D U e h (v a) (v b)]; ring
 simp_rw [ht,dry_clock]; rw [mul_assoc]

lemma steer_two {m:Side}(G:Fin 2 → Staff)(W:swatches 2→ ℂ)(ρ:ℝ)(D:Floor M q (More m) η C)(U:M.covered σ C)(e:0<σ) : let V:=stamen B P (More m); (∫ x:V,(propel G m).basin ρ (Hearth.brush W) q x.val ∂stdGaussian V)=
    (ρ:ℂ)^2*∑ c:swatches 2,coupon ((G 0).localFace m) ((G 1).localFace m) (c 0) (c 1) M*W c:=by
 intro V
 let v:=fun i=> (G i).localFace m
 let F:=propel G m; let Y(i:Fin 2)(j:I): V:=plar B P ((v i).1, plaquette (v i).2) ρ j
 let μ:=stdGaussian V; let α(c:swatches 2)(u:V):= inner ℝ (Y 0 (c 0)) u * inner ℝ (Y 1 (c 1)) u
 have he(u:V): F.basin ρ (Hearth.brush W) q u.val= ∑ c:swatches 2,(α c u:ℂ)*W c:=by
   let f:=tiler B P (n:=More m); obtain ⟨t,rfl⟩:= f.surjective_rangeRestrict u; change F.basin ρ (Hearth.brush W) q (tiler B P t) = _; rw [Vessel.belly B P F]; have hp(i:fibers 2): ρ*Work.F03.faceCurl (F.ua i) t (F.lens i)=inner ℝ (Y i.1 i.2) (f.rangeRestrict t):=by
       have hp: elbow B P ((v i.1).1,plaquette (v i.1).2) ρ (f.rangeRestrict t) = ρ • Regis.Head.Etch.river q ((v i.1).1,(v i.1).2) (f.rangeRestrict t).val := bare_elbow B P (f.rangeRestrict t); have hx:= congrArg (fun x:SU.group.Color=> x i.2) hp; rw [show Regis.Head.Etch.river q _ (f.rangeRestrict t).val= _ from Regis.Head.Etch.river_now q B P (v i.1) t] at hx; exact hx.symm
   rw [funext hp]; unfold Hearth.brush; refine sum_congr rfl fun i _=>?_ ; unfold α; simp only [Fin.prod_univ_succ,Finset.univ_eq_empty (α:=Fin 0),Finset.prod_empty,mul_one]; push_cast; rfl
 have hx(p:V):MemLp (fun Z:V=> inner ℝ p Z) 2 μ:=by simpa using coats p 1
 change (∫ x:V,F.basin ρ (Hearth.brush W) q x.val∂μ)=_; simp_rw [he]; erw [integral_finsetSum _ (fun i _=> (((hx _).integrable_mul (hx _)).ofReal (𝕜:=ℂ)).mul_const _)];
 rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; let h: Even (More m).val:=⟨m.val,by change m.val*2=_; omega⟩
 simp only [Pi.mul_apply]; rw [integral_mul_const]; erw [integral_complex_ofReal,appraisal]; unfold coupon Y; rw [limb_component B P D U e h (v (0:Fin 2)) (v 1)]; change ((ρ:ℂ)^2 * _ * _) * W i= _; unfold v; ring
#print axioms steer_four
#print axioms steer_two

end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
