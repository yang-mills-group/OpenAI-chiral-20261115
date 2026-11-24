import GaugeFieldConstruction.PommeMars
/-!
# lawmakers
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
namespace FirstPackMars
variable (W:Fin n→ (BellTableMars p Y).Tag)(x:Points (n+1))(χ:Bulb)(h: BreatherMars χ 0 x)
variable (H:FirstPackMars p Y)
-- linearity on Tide & Rhythm. K direction linear. 
abbrev LegendMars (W:Fin n→(BellTableMars p Y).Tag): Fin n→ΡeaderMars.Token:= fun i=> ⟨(W i).1,(BellTableMars p Y).representative _ (W i).2⟩
lemma ReelFoilMoon (W: Fin n→ (BellTableMars p Y).Tag)(x:Points n): (BellTableMars p Y).useAt (BellTableMars p Y) x W=(BellTableMars p Y).read x (LegendMars W):=rfl
noncomputable def LunaMintMars (W:Fin n→(BellTableMars p Y).Tag)(x: Points (n+1))(a:ℕ): (BellTableMars p Y).Field a→ₗ[ℂ] ℂ:= ((BellTableMars p Y).injectFront (LegendMars W) x a).comp ((BellTableMars p Y).representative a)
lemma ClipLegendMars (a:ℕ)(A:(BellTableMars p Y).Field a): LegendMars (p:=p) (Y:=Y) (Fin.cons (upMarkMars (p:=p) (Y:=Y) a A) W)= Fin.cons (PostMars a ((BellTableMars p Y).representative a A)) (LegendMars W):=by
 ext1 j; refine Fin.cases rfl (fun i=>rfl) j
lemma LunaPriceMars (a:ℕ)(A:(BellTableMars p Y).Field a): LunaMintMars (p:=p) (Y:=Y) W x a A=TideLunaMars (p:=p) (Y:=Y) A W x:=by unfold TideLunaMars; rw [ReelFoilMoon,ClipLegendMars]; rfl
noncomputable def LunaFoilMars (W:Fin n→(BellTableMars p Y).Tag)(a:ℕ)(i j:Axis)(y:Points (n+2)): (BellTableMars p Y).Field a→ₗ[ℂ] ℂ:=by
 let B: Fin (n+2)→ΡeaderMars.Token:=LegendMars (Fin.cons (α:=fun _:Fin (n+2)=> (BellTableMars p Y).Tag) (upMarkMars 4 (BegMars p Y 4 (p.J i j))) (Fin.cons (upMarkMars a ((0:(BellTableMars p Y).Field a))) W))
 exact (((BellTableMars p Y).value (fun i=>(B i).1) y).toLinearMap (fun k=>(B k).2) ((0:Fin (n+1)).succ)).comp ((BellTableMars p Y).representative a)
lemma LFPriceMars (a:ℕ)(A:(BellTableMars p Y).Field a)(i j:Axis)(y:Points (n+2)): LunaFoilMars (p:=p) (Y:=Y) W a i j y A= PFoilMoon (p:=p) (Y:=Y) A W i j y:=by
 let B':=(upMarkMars 4 (BegMars p Y 4 (p.J i j))); let Q (x:(BellTableMars p Y).Field a):=LegendMars (Fin.cons B' (Fin.cons (upMarkMars a x) W))
 let B:=Q 0
 let k:Fin (n+2):=(0:Fin (n+1)).succ
 let V0:ΡeaderMars.Ref ((B k).1):=(BellTableMars p Y).representative a A
 let v:(i:Fin (n+2))→ΡeaderMars.Ref ((B i).1):=update (fun i=>(B i).2) k V0
 have ht:(fun i=> (Sigma.mk (β:=_) (B i).1 (v i):ΡeaderMars.Token))=Q A:=by
    funext i; refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun j=>?_) i) i
    · rw [show v 0=(B 0).2 from update_of_ne (show (0:Fin (n+2))≠k from Ne.symm (Fin.succ_ne_zero _)) _ _]; rfl
    · change Sigma.mk (B k).1 (v k)=_; rw [show v k=V0 from update_self ..]; rfl
    rw [show v j.succ.succ=(B j.succ.succ).2 from update_of_ne ((Fin.succ_injective _).ne (Fin.succ_ne_zero j)) ..]; rfl
 unfold PFoilMoon TideLunaMars; rw[ReelFoilMoon]; exact (congrArg ((BellTableMars p Y).read y) ht)
lemma foilSMMars (a:ℕ)(A:(BellTableMars p Y).Field a)(i j:Axis):ContDiffOn ℝ ∞ (PFoilMoon (p:=p) (Y:=Y) A W i j) (conf _):= (BellTableMars p Y).class_smooth _ (BellSmMars p Y) _
noncomputable def spoolLunaMars (a:ℕ) (K:Payroll (n+1))(i j :Axis) : (BellTableMars p Y).Field a→ₗ[ℂ] ℂ where
 toFun A:= RhythmMars A W x χ K i j
 map_add' A B:=by
    unfold RhythmMars RyeMars WrapMars; rw [← integral_add (soilIntMars _ (foilSMMars W a A i j) 0 χ x h K i j) (soilIntMars _ (foilSMMars W a B i j) 0 χ x h K i j)]; exact integral_congr_ae (Eventually.of_forall (fun y=>by dsimp only; unfold SoilMars; rw[← LFPriceMars,map_add,smul_add,LFPriceMars, LFPriceMars]))
 map_smul' c A:= by
    unfold RhythmMars RyeMars WrapMars; change (∫ y:E4,_) = c • ∫ y:E4,_; rw[←integral_smul]; apply integral_congr_ae; filter_upwards with y; unfold SoilMars; rw[←LFPriceMars,map_smul,LFPriceMars,smul_comm]
-- definition h included? def needs include explicitly
variable {a:ℕ}
noncomputable def rankFluxMars (i:Axis)(a:ℕ) :(BellTableMars p Y).Field a→ₗ[ℂ] ℂ:=∑ b:Axis, spoolLunaMars W x χ h a (Payroll.ticket i) b i
lemma rankFluxApplyMars (i:Axis)(A:(BellTableMars p Y).Field a): rankFluxMars W x χ h i a A=ΘMilesMars A W x χ i:=by unfold rankFluxMars; rw [LinearMap.sum_apply]; rfl
noncomputable def rankPulseMars (Ω:Ortho.Skew)(a:ℕ) :(BellTableMars p Y).Field a→ₗ[ℂ] ℂ:=∑ b:Axis,∑ i:Axis, spoolLunaMars W x χ h a (Payroll.desk 0 Ω) b i
lemma rankPulseApplyMars (Ω:Ortho.Skew)(A:(BellTableMars p Y).Field a): rankPulseMars W x χ h Ω a A=ΩMilesMars A W x χ Ω:=by unfold rankPulseMars; simp_rw [LinearMap.sum_apply]; rfl
-- Ω dependence linear
include h in
lemma RΩAddMars (Ω V:Ortho.Skew)(A:(BellTableMars p Y).Field a)(i j): RhythmMars A W x χ (Payroll.desk 0 (Ω+V)) i j = RhythmMars A W x χ (Payroll.desk 0 Ω) i j + RhythmMars A W x χ (Payroll.desk 0 V) i j:=by
 unfold RhythmMars RyeMars WrapMars
 let K:=PFoilMoon A W i j
 rw [← integral_add (soilIntMars K (foilSMMars W a A i j) 0 χ x h _ _ _) (soilIntMars K (foilSMMars W a A i j) 0 χ x h _ _ _)] -- tune
 apply integral_congr_ae; filter_upwards with u; unfold SoilMars; have ht(p:Points (n+2)) : (Payroll.desk (0:Fin (n+1)) (Ω+V)).K j p= (Payroll.desk 0 Ω).K j p+(Payroll.desk 0 V).K j p:=by simp [Payroll.angle,M4.move] -- tune
 rw [ht,mul_add,add_smul]
lemma RΩScaleMars (Ω:Ortho.Skew)(c:ℝ)(A:(BellTableMars p Y).Field a)(i j): RhythmMars A W x χ (Payroll.desk 0 (c • Ω)) i j = c • RhythmMars A W x χ (Payroll.desk 0 Ω) i j:=by
 unfold RhythmMars RyeMars WrapMars; rw [←integral_smul]; apply integral_congr_ae; filter_upwards with u; unfold SoilMars
 have ht(p:Points (n+2)) : (Payroll.desk (0:Fin (n+1)) (c • Ω)).K j p=c*(Payroll.desk 0 Ω).K j p:=by simp [Payroll.angle,M4.move] -- tune
 rw [ht,mul_left_comm, mul_smul]
noncomputable def rankGyroMars (a:ℕ) : Ortho.Skew→ₗ[ℝ] ((BellTableMars p Y).Field a→ₗ[ℂ] ℂ) where
 toFun Ω:= rankPulseMars W x χ h Ω a
 map_add' A V:=by apply LinearMap.ext; intro w; rw [LinearMap.add_apply]; simp only[rankPulseApplyMars]; unfold ΩMilesMars; simp_rw [RΩAddMars W x χ h, sum_add_distrib]
 map_smul' c A:=by apply LinearMap.ext; intro w; change _=c • ((rankPulseMars W x χ h A a) w); simp_rw[rankPulseApplyMars]; unfold ΩMilesMars; simp_rw[RΩScaleMars, smul_sum]
lemma rankGyroApplyMars (Ω:Ortho.Skew) (A:(BellTableMars p Y).Field a): rankGyroMars W x χ h a Ω A=ΩMilesMars A W x χ Ω:= rankPulseApplyMars ..
#print axioms rankGyroApplyMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
