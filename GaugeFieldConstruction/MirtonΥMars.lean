import GaugeFieldConstruction.SapinΩMars
/-!
 # contoured thrust. descending.
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
variable (W:Fin n→ (BellTableMars p Y).Tag)(x:Points (n+1))(χ:Bulb)(h: BreatherMars χ 0 x)
variable (H:FirstPackMars p Y)
-- charge fuel. linear reads with two heads.
variable (D:NSF.Caps n) (w: ChartVuMars D)
lemma DualTailMars (p:Ticket u C)(Y:AreaQc S)(x:Points (n+2))(B C:ΡeaderMars.Token):
    (BellTableMars p Y).read x (Fin.cons B (Fin.cons C (WriteMars D w)))=∑ ρ:LabelsMars D,ChartTaxMars w ρ * (BellTableMars p Y).read x (Fin.cons B (Fin.cons C (TiesMars D ρ))):=by
 let T:=BellTableMars p Y; let f:=RaiseCapMars B.1 (RaiseCapMars C.1 D); let Z: MultilinearMap ℂ (fun i=> FlyerMars (D i)) ℂ:= ((T.value f x).curryLeft B.2).curryLeft C.2
 have ht(v:ChartVuMars D): T.read x (Fin.cons B (Fin.cons C (WriteMars D v)))=Z v:=by
    let V:ΡeaderMars.Vector f:= Fin.cons (α:=fun i=>ΡeaderMars.Ref (f i)) B.2 (Fin.cons C.2 v)
    have hv:Fin.cons (α:=fun _:Fin (n+2)=>ΡeaderMars.Token) B (Fin.cons C (WriteMars D v))=(fun i=> Sigma.mk (f i) (V i)):=by ext1 j; refine Fin.cases rfl (fun i=>Fin.cases rfl (fun j=>rfl) i) j
    rw[hv,T.read_eq]; rfl
 rw[ht,QtyApplyMars Z w]; apply sum_congr rfl; exact fun i _=>congrArg (ChartTaxMars w i *·) (ht (HitsMars i)).symm
noncomputable abbrev LinkVMars (p:Ticket u C)(Y:AreaQc S)(D:NSF.Caps n)(w:ChartVuMars D): Fin n→ (BellTableMars p Y).Tag:= (BellTableMars p Y).classTokens ∘ WriteMars D w
variable {d:ℕ}
include H
lemma Cost2Mars (y:Points (n+2))(g: y∈conf (n+2))(A:(BellTableMars p Y).Field d)(i j): PFoilMoon A (LinkVMars p Y D w) i j y= ∑ ρ:LabelsMars D, ChartTaxMars w ρ* PFoilMoon A (highQtyMars p Y ρ) i j y:=by
 let T:=BellTableMars p Y
 obtain ⟨A,rfl⟩:=T.onto _ A
 obtain ⟨B,e⟩:=T.onto 4 (BegMars p Y 4 (p.J i j)); let F:=(PostMars 4 B); let G:=(PostMars d A)
 have he(v: ChartVuMars D): PFoilMoon (T.project _ A) (LinkVMars p Y D v) i j y=T.read y (Fin.cons F (Fin.cons G (WriteMars D v))):=by
    unfold PFoilMoon TideLunaMars; rw [←e, ← T.at_project T (SymHallMars H) (fun _=>le_rfl) g]; congr 1; ext1 i; refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun j=>?_) i) i <;> rfl
 rw [he w,DualTailMars D w p Y] -- order variable declaration tune
 apply sum_congr rfl; exact fun i _=>congrArg (ChartTaxMars w i*·) (he (HitsMars i)).symm -- hits
lemma Cost1Mars (v:x∈conf (n+1))(A:(BellTableMars p Y).Field d): TideLunaMars A (LinkVMars p Y D w) x = ∑ ρ:LabelsMars D, ChartTaxMars w ρ * TideLunaMars A (highQtyMars p Y ρ) x := by
 obtain ⟨A,rfl⟩:=(BellTableMars p Y).onto d A
 refine (AcostMoon H v d A (WriteMars D w)).trans ((TailQtyMars p Y D w d A x).trans (Finset.sum_congr rfl fun i _=> congrArg (ChartTaxMars w i*·) (AcostMoon H v d A (TiesMars D i)).symm))
lemma AvailableMars: ∃ d:NSF.Caps n,∃ w:ChartVuMars d,W=LinkVMars p Y d w:=by
 obtain ⟨q,rfl⟩:=LiftQtyMars W; exact ⟨(fun i=>(q i).1),(fun i=>(q i).2),rfl⟩
include h
lemma RhythmPulseMars (K: Payroll (n+1))(A:(BellTableMars p Y).Field d)(i j): RhythmMars A (LinkVMars p Y D w) x χ K i j= ∑ ρ:LabelsMars D, ChartTaxMars w ρ * RhythmMars A (highQtyMars p Y ρ) x χ K i j:=by
 unfold RhythmMars RyeMars WrapMars; let Z(ρ:LabelsMars D):=PFoilMoon A (highQtyMars p Y ρ) i j; let Ξ:=PFoilMoon A (LinkVMars p Y D w) i j
 have e(ρ): Integrable (fun y:E4=>ChartTaxMars w ρ * SoilMars (Z ρ) K χ i j (y,x)):= Integrable.const_mul (soilIntMars _ (foilSMMars _ _ _ _ _) 0 χ x h _ _ _) _ -- tune
 simp_rw [←integral_const_mul]; rw [←integral_finsetSum _ (fun i _=> e i)]
 refine integral_congr_ae (Eventually.of_forall (fun y=> ?_))
 by_cases hy:y∈run (LED χ i)
 · change SoilMars Ξ K χ i j (y,x)=_
   have hx:=RoomMars χ 0 x h y (cone _ _ hy)
   unfold SoilMars Ξ; rw [Cost2Mars H D w (fuse.symm (y,x)) hx A i j, smul_sum]
   apply sum_congr rfl; intro a _; change (_:ℝ) • (ChartTaxMars w a • Z a (fuse.symm (y,x))) = ChartTaxMars w a • ((_:ℝ) • Z a (fuse.symm (y,x))); exact smul_comm ..
 change SoilMars Ξ K χ i j (y,x) =_; rw[SoilAreaMars Ξ K χ i j _ hy]; symm; apply sum_eq_zero; intro k _; rw [SoilAreaMars _ _ _ _ _ _ hy,mul_zero]
lemma WarrantTiltMars (A:(BellTableMars p Y).Field d)(i): ΘMilesMars A W x χ i=TideLunaMars (riseUpsMars i A) W x := by
 obtain ⟨d,w,rfl⟩:= AvailableMars W H -- args tune
 rw [Cost1Mars x H d w h.bounds]
 unfold ΘMilesMars; simp_rw [RhythmPulseMars x χ h H d w]; rw[sum_comm]; apply sum_congr rfl; intro ρ _; rw [← mul_sum]; exact congrArg (ChartTaxMars w ρ *·) ((ChapelCompleteMars H 0 _ A).1 n _ ρ x χ h i)
lemma WarrantSpinMars (A:(BellTableMars p Y).Field d)(Ω): ΩMilesMars A W x χ Ω=TideLunaMars (SphereHoursMars H d Ω A) W x := by
 obtain ⟨dV,w,rfl⟩:=AvailableMars W H; rw[Cost1Mars x H dV w h.bounds]; unfold ΩMilesMars; simp_rw [RhythmPulseMars x χ h H dV w]; -- sum reorder
 let F (i j:Axis)(ρ:LabelsMars dV):= RhythmMars A (highQtyMars p Y ρ) x χ (Payroll.desk 0 Ω) i j; let v(ρ:LabelsMars dV):=ChartTaxMars w ρ
 change (∑ i:Axis,∑ j:Axis,∑ ρ:LabelsMars dV,v ρ*F i j ρ)=_
 simp_rw [show ∀ i:Axis,(∑ j:Axis,∑ ρ:LabelsMars dV,v ρ* F i j ρ)=∑ ρ:LabelsMars dV,∑ j:Axis,v ρ*F i j ρ from fun i=> sum_comm]
 rw[sum_comm]; apply sum_congr rfl; intro i _; change (∑ j:Axis,∑ k: Axis,v i * F j k i)=_ ; simp_rw [←mul_sum]; exact congrArg (v i *·) (SphericalMars H Ω d A _ dV i x χ h)
-- NSF prices
#print axioms WarrantTiltMars
#print axioms WarrantSpinMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
