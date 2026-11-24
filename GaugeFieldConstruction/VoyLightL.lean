import GaugeFieldConstruction.CairnAngleL
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
variable {cost:ℕ→P.Test→ℂ} {j: Axis}(C:Porch P cost j)
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable {n:ℕ}{S: City} {P0:Axis→Empire.Across} {L:Sheds S P0} {Cu: Supplies L} {u:ℕ→Carat}
-- axis carried thru. CPI covariance proper. Suit has ALL axes declared, no H3 tilt for phase yet
variable (Cw:∀ j:Axis,Porch P cost j)
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P) (G:CloudsL) (t:Ticket u Cu)
open NSF.Boundary NSF.OS.Semigroup -- no OS namespace clash
open NSF.LD
-- (137)-->(138) variant: projection joint on actual POS. norm displacement criterion; everything commutes on same Hil. use E2 costs, no invocation of L1 for chosen x until after L3!
variable (a:Axis)(p: Points n)(v:eastL n a p)(F:Fin n→ ΧiMars)(J:StallLeadMars a p P)
variable (χ:P.Spectrum0 3)(U:CheckΩL R)
open Set Complex
-- no smoothness assumed. 
noncomputable abbrev AutoTagL (R:ΧiMars→ₗ[ℂ] ScreensJ P)(σ:Fin n→ PermWallJ P)(x:Fin n→Axis→ℝ)(l:List (Fin n))(p:Option ℝ)(v:Fin n→ΧiMars):=(ActorMars C.BrightHab C.groundHab p (billActMars C σ (BodyΘ P (fun i=> R (v i)) j σ) x l))
lemma stableTagL (σ:Fin n→PermWallJ P)(x:Fin n→Axis→ℝ)(l:List (Fin n))(p:Option ℝ)(v w:Fin n→ΧiMars)(h:∀ i∈l,v i=w i): AutoTagL C R σ x l p v=AutoTagL C R σ x l p w:=by
 unfold AutoTagL; apply congrArg (ActorMars _ _ _); unfold billActMars; apply List.map_congr_left; intro i e; unfold BodyΘ; dsimp only; rw [h i e]
lemma linearJWTL (σ:Fin n→ PermWallJ P)(x:Fin n→Axis→ℝ)(l:List (Fin n))(b:Option ℝ)(A:Fin n→ ΧiMars)(i:Fin n)(h:i∈ l)(v:l.Nodup)(r t:ℂ)(f k:ΧiMars) : AutoTagL C R σ x l b (Function.update A i (r • f+t • k))= r • AutoTagL C R σ x l b (Function.update A i f)+t • AutoTagL C R σ x l b (Function.update A i k):=by
 induction l generalizing b with
 | nil=> simp at h
 | cons d l ih=>
    let K:=(σ d); let y:= x d; let Q:= y j+StallJ P K; let TΘ (b:Option ℝ):=(C.BrightHab.E ((b.map (fun a=>(y j-StallJ P K-a).toNNReal)).getD 0)); let M:= AutoTagL C R σ x l (some Q)
    let X:ΧiMars→ₗ[ℂ]C.DegreeHab.Op:={
        toFun:=fun t=> StampActMars C y (R t j K K)
        map_add' v w:=by simp [StampActMars,LadderRackMars,add_mul,mul_add]
        map_smul' c t:=by simp [StampActMars,LadderRackMars] }
    have H(V): AutoTagL C R σ x (d::l) b V=(TΘ b) ((X (V d)) (M V)):=rfl
    obtain ⟨e,v⟩:=List.nodup_cons.mp v
    obtain z|z:=List.mem_cons.mp h
    · subst i; have p(u:ΧiMars): M (update A d u)=M A:=stableTagL C R σ x _ _ _ _ (fun i hi=>Function.update_of_ne (show i≠d from fun h=> e (h ▸ hi)) ..)
      rw [H,H,H,p,p,p,Function.update_self,Function.update_self,Function.update_self, map_add,map_smul,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply, map_add,map_smul,map_smul]
    simp_rw [H,Function.update_of_ne (show d≠i from fun h=>e (h.symm ▸ z))]; unfold M; rw [ih (some Q) z v,map_add,map_smul,map_smul,map_add,map_smul,map_smul]
include U
lemma CoralJWTL (p:Points n)(h:p∈blueL n)(F:Fin n→ΧiMars)(i: Fin n)(a b:ℂ)(x y:ΧiMars): CoralL Cw R (Function.update F i (a • x + b • y)) p= a • CoralL Cw R (Function.update F i x) p + b • CoralL Cw R (Function.update F i y) p :=by
 obtain ⟨j,h⟩:=Set.mem_iUnion.mp (show ΦplanR n p ∈ CardsR _ from h); obtain ⟨l,σ,g,t⟩:=WestOpensL R _ _ U h
 have H(v:Fin n→ΧiMars): CoralL Cw R v p=inner ℂ (Cw j).groundHab (AutoTagL (Cw j) R σ (ΦplanR n p) l none v):= (ηTenderR Cw l _ (fun i=>U.showL _) j _ _ g t).trans (EarningActorMars (Cw j) σ (BodyΘ P (fun i=>R (v i)) j σ) _ _) -- tune
 rw [H,H,H,linearJWTL _ R _ _ l _ F i (g.2 i) g.1,inner_add_right,inner_smul_right,inner_smul_right]; rfl
noncomputable def AtlasCoralL (n:ℕ)(p:Points n)(h:p∈blueL n): MultilinearMap ℂ (fun _:Fin n=> ΧiMars) ℂ where
 toFun v:= CoralL Cw R v p
 map_update_add' {d} F i a b:=by rw[show d=instDecidableEqFin _ from Subsingleton.elim ..]; simpa only [one_smul] using (CoralJWTL Cw R U p h F i 1 1 a b) -- tune R order
 map_update_smul' {d} F i a b:=by rw[show d=instDecidableEqFin _ from Subsingleton.elim ..]; simpa only [zero_smul,add_zero] using (CoralJWTL Cw R U p h F i a 0 b b)
-- Aware n option. 
private noncomputable def parcelL(p:Points n)(v:p∈blueL n): MultilinearMap ℂ (fun _ : Fin n=> grainMars) ℂ:= (AtlasCoralL Cw R U _ p v).compLinearMap (fun _ : Fin n=>FreightMars.symm.toLinearMap)
-- rebook representation
lemma AtollLightL (T:Fin n→ grainMars)(X:Points n)(v:X∈blueL n): ContinuousAt (fun p:Points n× (Fin n→ grainMars)=> CoralL Cw R (FreightMars.symm ∘ p.2) p.1) (X,T):=by
 let B(i:SpeckMars):grainMars:= Pi.single i 1
 let w(ρ:Fin n→ SpeckMars):Fin n→ grainMars:= B ∘ ρ
 let K(ρ:Fin n→SpeckMars)(y:Points n × (Fin n→ grainMars)):=(∏ i:Fin n, y.2 i (ρ i))* CoralL Cw R (FreightMars.symm ∘ w ρ) y.1
 have he(q: Fin n→SpeckMars): ContinuousAt (K q) (X,T):=by
    unfold K; apply ContinuousAt.mul
    · fun_prop
    exact ((BlueAtL Cw R _ (FreightMars.symm ∘ w q) U v).tendsto.comp (continuousAt_fst (p:=(X,T))).tendsto)
 refine (show ContinuousAt (fun x=> ∑ i:Fin n→SpeckMars,K i x) (X,T) from tendsto_finsetSum _ (fun i _=> (he i).tendsto)).congr ?_
 filter_upwards [(continuous_fst.continuousAt (x:=(X,T))).eventually ((clearL _).mem_nhds v)] with x hx
 obtain ⟨z,A⟩:= x; change z∈ blueL n at hx
 let F(i:Fin n)(j:SpeckMars):grainMars:= A i j • B j; have hf(i:Fin n): A i=∑ j:SpeckMars,F i j:=by ext1 b; simp [F,B,Finset.sum_apply,Pi.single_apply]
 change (∑ i:Fin n→ SpeckMars,K i (z,A)) = parcelL Cw R U z hx A
 symm; conv_lhs=> rw[show A=fun i=>∑ j:SpeckMars,F i j from funext hf]
 simp_rw[MultilinearMap.map_sum]; apply Finset.sum_congr rfl; intro i _; exact (parcelL Cw R U z hx).map_smul_univ (fun j=>A j (i j)) (w i) -- tune
#print axioms AtlasCoralL
#print axioms AtollLightL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
