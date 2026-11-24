import GaugeFieldConstruction.SugarPhMars
/-!
 # slots evaluated with allocated stress. Tests smooth only on Euclidean Conf. Restrict exterior first, then need arbitrary-angular-all.
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
local notation "T"=> BellTableMars p Y
local notation "M"=> TerraMars p Y
namespace FirstPackMars
abbrev upMarkMars (d:ℕ)(v: (BellTableMars p Y).Field d):(T).Tag:=Sigma.mk d v
abbrev highQtyMars (p:Ticket u C)(Y:AreaQc S){d:NSF.Caps n}(v:LabelsMars d): Fin n→(BellTableMars p Y).Tag:= (BellTableMars p Y).classTokens ∘ TiesMars d v
abbrev TideLunaMars {a:ℕ} (A:(T).Field a)(W:Fin n→(T).Tag) (x:Points (n+1)):= (T).useAt T x (Fin.cons (upMarkMars a A) W)
abbrev PFoilMoon {a:ℕ} (A:(T).Field a)(W: Fin n→(T).Tag) (a b:Axis) := TideLunaMars (BegMars p Y 4 (p.J a b)) (Fin.cons (upMarkMars _ A) W)
noncomputable def RhythmMars {a:ℕ} (A:(T).Field a)(W:Fin n→(T).Tag)(x:Points (n+1))(χ:Bulb)(K:Payroll (n+1)) (a b:Axis):= RyeMars (PFoilMoon A W a b) K χ a b x
abbrev ΩMilesMars {a} (A:(T).Field a)(W:Fin n→(T).Tag)(x:Points (n+1))(χ:Bulb)(Ω:Ortho.Skew):= ∑ a:Axis,∑ b:Axis,RhythmMars A W x χ (Payroll.desk 0 Ω) a b
abbrev ΘMilesMars {a} (A:(T).Field a)(W:Fin n→(T).Tag)(x:Points (n+1))(χ:Bulb)(i:Axis):= ∑ a:Axis,RhythmMars A W x χ (Payroll.ticket i) a i
-- uniqueness requires every witness. for now exteriors basis
abbrev riseUpsMars {a:ℕ}(i:Axis)(A:(T).Field a):= arcTiltMars p Y a (i,false) A
def EpochLunaMars (a:ℕ)(A:(T).Field a):Prop:=∀ (n:ℕ)(D:NSF.Caps n)(w:LabelsMars D)(x:Points (n+1))(χ:Bulb), BreatherMars χ 0 x→ ∀ i,ΘMilesMars A (highQtyMars p Y w) x χ i=TideLunaMars (riseUpsMars i A) (highQtyMars p Y w) x
-- Fortune angular compute non-unital
abbrev FortuneMars (a:ℕ)(Ω:Ortho.Skew)(A B:(T).Field a):Prop:=∀ (n:ℕ)(D:NSF.Caps n)(w:LabelsMars D)(x:Points (n+1))(χ:Bulb), BreatherMars χ 0 x→ ΩMilesMars A (highQtyMars p Y w) x χ Ω=TideLunaMars B (highQtyMars p Y w) x
-- need exteriors.Any.B. Hil net scattering
variable (H:FirstPackMars p Y)
include H
-- transfer derivative thru mintCone. ΠHead with minted both insert exterior.For base x=MCoreMoon; B at Y rotation is arbitrary.
lemma readMintMars (Z:ΧiMars){x:Points (n+1)}(hx:x∈conf _)(a:ℕ)(R:TrailsMars a)(d:NSF.Caps n)(v: LabelsMars d): TideLunaMars (mintClassMars p Y a R Z) (highQtyMars p Y v) x=BillHeadMoon p Y v (unfoldTrailsMars R) Z x := (AcostMoon H hx a (mintUnoMars a R Z) _).trans (mintCoinMars _ _ _ hx d v a R Z)
lemma commonStemMars (A:MariaMars)(x:Points (n+2))(hx:x∈conf _)(a:ℕ)(D:NSF.Caps n)(v:LabelsMars D) (i j): PFoilMoon (BegMars p Y a (MCoreMars A)) (highQtyMars p Y v) i j x=
    PoolDMars (trailMars (((τGuideMars v).map CloverHMars).map guideDirMars)) (M (Fathom.add (p.J i j) (Fin.cons (MCoreMars A) (τCoreMars v)))) x :=by
 let X:=IndexMars a (A,TrailBlankMars a); let Z:LabelsMars (RaiseCapMars a D):= AffixMars X v; let V:= highQtyMars p Y v
 have hz: highQtyMars p Y Z= Fin.cons (upMarkMars a (BegMars p Y a (MCoreMars A))) V:=by
    unfold BegMars; rw [MonetArcMars H]; unfold highQtyMars Z; rw[TiesCutMars]; ext1 i; refine Fin.cases ?_ (fun t=>rfl) i; rfl
 unfold PFoilMoon; rw [← hz,readMintMars H _ hx 4 _ _ Z]; let r:= ((τGuideMars v).map CloverHMars).map guideDirMars
 have hE:ChaseMars a X=(A,TrailBlankMars a):=(IndexMars a).symm_apply_apply _
 have he:τCoreMars Z= Fin.cons (MCoreMars A) (τCoreMars v):=by unfold Z; rw[CoreCutMars,hE]
 change PoolDMars (((τGuideMars Z).map CloverHMars).map guideDirMars) (M (Fin.cons (p.J i j) (τCoreMars Z))) x=_
 rw [he]; unfold Z; rw[LinesHMars,hE]; change PoolDMars ((_ : List (GuideMars (n+2))).map guideDirMars) _ _= _; congr 1; let U:=(τGuideMars v).map CloverHMars; change (U.map CloverHMars).map guideDirMars=(U.map guideDirMars).map (Points.cons 0); conv_lhs=> rw [List.map_map]
 conv_rhs=> rw[List.map_map]
 exact congrArg (fun f : GuideMars (n+1) → Points (n+2)=>U.map f) (funext (fun x=> CorePlaneMars x))
lemma mindTempMars (w:List (GuideMars n)): ∀ i ∈ ((w.map CloverHMars).map guideDirMars), i (0:Fin (n+1))=0:=by
 intro i t; obtain ⟨y,hy,rfl⟩:=List.mem_map.mp t; obtain ⟨r,u,rfl⟩:=List.mem_map.mp hy; rw[CorePlaneMars]; rfl
lemma dialπMars (w: Fin n→(T).Tag) {a:ℕ}(A:(T).Field a)(x:Points (n+1))(e:x∈conf _)(i:Axis): TideLunaMars (riseUpsMars i A) w x= Analysis.D (direction 0 i) (TideLunaMars A w) x:= (DictTiltMars H).kernels a i A e _
-- equivalence payroll via Conf
lemma RulerMars (A G:Points (n+1)→ℂ)(e:EqOn A G (conf _))(W:Payroll n)(χ:Bulb)(a i:Axis)(x:Points n)(k:Fin n)(h:BreatherMars χ k x): RyeMars A W χ a i x= RyeMars G W χ a i x:=by
 apply integral_congr_ae; refine Eventually.of_forall (fun y=>?_) -- tune
 by_cases hy:y∈ run (LED χ a)
 · exact congrArg (_ • ·) (e (RoomMars χ k x h y (cone _ _ hy)))
 exact (SoilAreaMars A W χ a i y hy x).trans (SoilAreaMars G W χ a i y hy x).symm
-- actual input Epoch on Basis B seed, and angular seed represented by p.Cl.
lemma spinBegMoon (a:ℕ)(Ω:Ortho.Skew)(B:MariaMars): FortuneMars a Ω (BegMars p Y a (MCoreMars B)) (BegMars p Y a ((TrowMars p Ω) (MCoreMars B))):=by
 intro n D v x χ h
 let W:= ((τGuideMars v).map CloverHMars).map guideDirMars; let U':=τCoreMars v; let b:=MCoreMars B; let F:=Fin.cons (α:=fun _:Fin (n+1)=>ΧiMars) b U'
 let K:= Payroll.desk (0 : Fin (n+1)) Ω
 let G(i j:Axis): Points (n+2)→ℂ:=M (Fathom.add (p.J i j) F)
 let Ξ:= {x| BreatherMars χ (0:Fin (n+1)) x}; have hv:IsOpen Ξ:= BreathingMars ..
 have e(i j): RhythmMars (BegMars p Y a (MCoreMars B)) (highQtyMars p Y v) x χ K i j= PoolDMars W (RyeMars (G i j) K χ i j) x :=by
    unfold RhythmMars; rw[clockStopMars (G i j) (TerraSm p Y _) 0 Ω χ x h W i j (mindTempMars H _)]; exact RulerMars H _ _ (fun x hx=>commonStemMars H B x hx a _ v i j) _ χ i j x _ h
 rw [readMintMars H _ h.bounds]; unfold ΩMilesMars
 change (∑ i:Axis,∑ j:Axis,RhythmMars (BegMars p Y a (MCoreMars B)) _ x χ K i j)=PoolDMars W (M (Fin.cons (TrowMars p Ω b) U')) x; simp_rw [e]
 let H'(i j:Axis):=RyeMars (G i j) K χ i j; have he (i j:Axis):ContDiffOn ℝ ∞ (H' i j) Ξ:=PodDPMars (G i j) (TerraSm p Y _) χ _ _ _ _
 simp_rw [show ∀ i:Axis, (∑ j:Axis,PoolDMars W (RyeMars (G i j) K χ i j) x)=PoolDMars W (fun x=>∑ j:Axis,H' i j x) x from fun i=> (pool_sumMars W _ (H' i) Ξ hv (fun j _=>he i j) x h).symm]
 rw [← pool_sumMars W _ (fun i x=>∑ j:Axis,H' i j x) Ξ hv (fun i _=> ContDiffOn.sum (fun j _=>he i j)) x h]
 have ht : M (Fin.cons (TrowMars p Ω b) U')=ᶠ[𝓝 x] (fun y=>∑ i:Axis,∑ j:Axis,H' i j y):= (hv.eventually_mem (show x∈Ξ from h)).mono (fun i t=>by
    have hu:=EndorseMars p Y 0 F i χ t Ω; rw [show update F 0 _= _ from Fin.update_cons_zero ..] at hu; exact hu)
 exact ((pool_germMars x W _ _ ht).self_of_nhds).symm
lemma equityMars (a:ℕ)(B:MariaMars): EpochLunaMars a (BegMars p Y a (MCoreMars B)):=by
 intro n D v x χ h i
 let W:= ((τGuideMars v).map CloverHMars).map guideDirMars; let U':=τCoreMars v; let b:=MCoreMars B; let F:=Fin.cons (α:=fun _:Fin (n+1)=>ΧiMars) b U'
 let K:= Payroll.ticket (n:=n+1) i; let L:=highQtyMars p Y v
 let G(j:Axis): Points (n+2)→ℂ:=M (Fathom.add (p.J j i) F)
 let Ξ:= {x| BreatherMars χ (0:Fin (n+1)) x}; have hv:IsOpen Ξ:= BreathingMars ..
 have e(j): RhythmMars (BegMars p Y a (MCoreMars B)) L x χ K j i= PoolDMars W (RyeMars (G j) K χ j i) x := (RulerMars H _ _ (fun y hy=>commonStemMars H B y hy a D v j i) K χ j i x 0 h).trans (CordDMars χ 0 x h j i (G j) (TerraSm p Y _) W).symm
 change (∑ j:Axis,RhythmMars (BegMars p Y a (MCoreMars B)) L x χ K j i)=TideLunaMars (riseUpsMars i (BegMars p Y a (MCoreMars B))) L x
 rw [dialπMars H L _ x h.bounds]; simp_rw [e]; let X':= direction (0:Fin (n+1)) i
 have hT:TideLunaMars (BegMars p Y a (MCoreMars B)) L=ᶠ[𝓝 x] PoolDMars W (M F):=((conf_open _).eventually_mem h.bounds).mono (fun i t=> readMintMars H (MCoreMars B) t _ _ _ v)
 rw[GermD _ hT,PoolRotateMars H x h.bounds 0 W i (M F) (TerraSm p Y F),← pool_sumMars W univ (fun j => RyeMars (G j) K χ j i) Ξ hv (fun j _=>PodDPMars (G j) (TerraSm p Y _) χ _ _ _ _) x h]
 exact (((pool_germMars x W _ _ ((hv.eventually_mem (show x∈Ξ from h)).mono (fun y t=>EnrobeMars p Y 0 F y χ t i)) ).self_of_nhds)).symm
#print axioms equityMars
#print axioms spinBegMoon
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
