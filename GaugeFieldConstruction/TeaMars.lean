import GaugeFieldConstruction.SolitaMars
import GaugeFieldConstruction.GarukaQc
/-!
 # factoring reference bill. head evaluation and derivative trails
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
variable (p:Ticket u C)(Y:AreaQc S)
lemma TeaWithMars (πJ: Ticket u C) (E: AreaQc S)(Z:UpAngleQc E)
 (cleanM:∀ (F: Fin 0→ΧiMars)(x: Points 0),WallMars E F x=1)
 (upM:∀ (n:ℕ) (s:E4)(v: Fin n→ ΧiMars)(x:Points n), x∈ generic n → WallMars E v (NSF.Points.across s x)=WallMars E v x): FirstPackMars πJ E:=by
 constructor
 · intro V x; exact (TerraWide πJ E V (show x∈generic _ from fun _ i=> Fin.elim0 i)).trans (cleanM ..)
 · intro n v x hx
   let K:NSF.Register Unit.unit:= ΡeaderMars
   let d:=Calibration.lift four ∘ v; let M':Points (n+1)→Points n:= Points.tail
   have he:Continuous M':=FirstPackMars.BrakeMars.continuous
   have hp:ContinuousOn (fun x:Points (n+1)=>TerraMars πJ E v (Points.tail x)) (conf (n+1)):=((TerraSm πJ E v).continuousOn).comp he.continuousOn (fun _ p=>fun j k q=>Fin.succ_injective n (p q))
   apply Dash.discl (conf_open _) (TerraMars _ _ _) _ (TerraSm πJ E _).continuousOn hp ?_ hx -- arguments
   intro y h; have q:=h.2; change y∈generic (n+1) at q; change TerraMars _ _ _ y= _; dsimp only
   rw [TerraWide πJ E _ q, TerraWide πJ E _ (show Points.tail y∈generic _ from fun i j k h=>Fin.succ_injective _ (q i h))]
   refine (congrArg (fun H=> E.fee _ H y) (show (Calibration.lift four ∘ Fathom.add _ v)= Fathom.add (Empire.one five) d from ?_)).trans (E.unit _ d _ q); funext i; refine Fin.cases ?_ (fun i=>rfl) i; rfl
 · intro n s v x hx
   let G:= NSF.Points.move (n:=n) s.ortho; have hv:G=CozioQc n s:=by rfl
   have ht:ContinuousOn (fun x=> TerraMars πJ E (spinFrame four s ∘ v) (G x)) (conf n):=by
     rw[hv]; exact ((TerraSm πJ E _).continuousOn).comp (CozioQc n s).continuous.continuousOn (fun _ p=> NSF.Points.move_in _ p)
   apply Dash.discl (conf_open _) _ (TerraMars _ _ _) ht (TerraSm _ _ _).continuousOn ?_ hx
   intro y h; dsimp only; rw [TerraWide _ _ _ h.2,TerraWide _ _ _ (show G y∈generic _ from ?_)]
   · refine (congrArg (fun F=> E.fee _ F (G y)) (funext (fun i=>Loft.spin_lift four s (v i)))).trans (Z.rotation s n _ y h.2) -- tune
   intro a i j hs; obtain ⟨b,rfl⟩:= s.perm.surjective a; simp [G,Signed.ortho_move] at hs; split at hs
   · exact h.2 b (neg_injective hs)
   exact h.2 b hs
 · intro n v y hy
   have hc: ContinuousOn (fun x=> Star.star (TerraMars πJ E v x)) (conf n):= continuous_star.continuousOn.comp ((TerraSm πJ E v).continuousOn) (Set.mapsTo_univ ..)
   apply Dash.discl (conf_open _) (TerraMars _ _ _) _ (TerraSm πJ E _).continuousOn hc ?_ hy
   intro x h; dsimp only; rw [TerraWide _ _ _ h.2,TerraWide _ _ _ h.2]; exact Z.paper n (Calibration.lift four ∘ v) x h.2
 · intro n s v x hx
   have hc:ContinuousOn (fun t=>TerraMars πJ E (v ∘ s) (NSF.Points.rearrange s t)) (conf n):=((TerraSm πJ E (v∘s)).continuousOn).comp (NSF.Points.arrangeL s).continuous.continuousOn (fun _ p=>NSF.Points.rearrange_in _ p)
   apply Dash.discl (conf_open _) _ (TerraMars _ _ _) hc (TerraSm _ _ _).continuousOn ?_ hx; intro y h; dsimp only; rw [TerraWide _ _ _ h.2,TerraWide _ _ _ (show NSF.Points.rearrange s y∈generic _ from fun i j k p=>s.injective (h.2 i p))]; exact E.rearr n s y h.2 (Calibration.lift four ∘ v) -- orientation
 intro n s v x hx
 have he:Continuous (NSF.Points.across (n:=n) s):=(show Continuous fun x:Points n=>x+points fun _: Fin n=>s from continuous_id.add continuous_const)
 apply Dash.discl (conf_open _) (fun x=>TerraMars πJ E v (NSF.Points.across s x)) _ (((TerraSm πJ E v).continuousOn).comp he.continuousOn fun _ p=>NSF.Points.across_in _ p) (TerraSm _ _ v).continuousOn ?_ hx; intro y h; dsimp only; rw [TerraWide _ _ _ h.2, TerraWide _ _ _ (show NSF.Points.across s y∈generic _ from fun i j k e=> h.2 i (add_right_cancel (show _ + s i = _ + s i from e)))]
 exact upM n s v y h.2
#print axioms TeaWithMars
end YM.GaugeFieldConstruction.Ember.Volumetric
