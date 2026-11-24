import GaugeFieldConstruction.RookiMars
/-!
 # Tilt commuting under all RiseTilt, spin row produces
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
-- D identities basis tilt. 
include H
lemma DinnerDirMars (i:Axis) : Points.cons (0:E4) (direction (0:Fin (n+1)) i)= direction ((0:Fin (n+1)).succ) i:=CorePlaneMars ((0:Fin (n+1)),(i,false)) |>.symm -- unfolds neg
lemma FoilQUpMars {b}(j i k:Axis)(A:(BellTableMars p Y).Field b) (x:Points (n+2))(h:x∈conf (n+2)): D (Points.cons 0 (direction (0 : Fin (n+1)) j)) (PFoilMoon A W i k) x= PFoilMoon (riseUpsMars j A) W i k x:=by
 let X:=PFoilMoon A W i k; let Q':=BegMars p Y 4 (p.J i k)
 let q(c:ℕ)(B:(BellTableMars p Y).Field c) : Fin (n+2)→(BellTableMars p Y).Tag:= Fin.cons (upMarkMars 4 Q') (Fin.cons (upMarkMars c B) W)
 let e:= q b A; let l:=(0:Fin (n+1)).succ
 have he(c)(B:(BellTableMars p Y).Field c): Function.update e l (upMarkMars c B)=q c B:=by
    funext i; refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun v=>?_) i) i
    · rw[Function.update_of_ne (show (0:Fin (n+2))≠l from Ne.symm (Fin.succ_ne_zero _))]; rfl
    · rw[Function.update_self]; rfl
    rw [Function.update_of_ne ((Fin.succ_injective _).ne (Fin.succ_ne_zero v))]; rfl
 let T:=BellTableMars p Y
 have ht := (DictumMars p Y).derivative_slot (DictTiltMars H) (T:=T) (SymHallMars H) (BellSmMars p Y) h l e A j
 change T.useAt T x (Function.update e l (upMarkMars _ (riseUpsMars j A)))= D (direction l j) (fun y=> T.useAt T y (Function.update e l (upMarkMars b A))) x at ht
 rw [he] at ht; simp_rw [he b A] at ht
 rw [DinnerDirMars H]; exact ht.symm
include h
-- stress. tilt derivative applies to ΘMiles Slot Clock K pure
lemma tiltΘMars {b}(k i j)(A:(BellTableMars p Y).Field b):
    D (direction 0 k) (fun x=>RhythmMars A W x χ (Payroll.ticket i) j i) x= RhythmMars (riseUpsMars k A) W x χ (Payroll.ticket i) j i:=by
 let v:= direction (0:Fin (n+1)) k; let F:= PFoilMoon A W j i
 exact (CordDMars χ 0 x h j i F (foilSMMars W b A j i) [v]).trans (RulerMars H (D (Points.cons 0 v) F) _ (fun y hx=>FoilQUpMars W H k j i A y hx) _ _ _ _ _ _ h)
lemma tiltΩMars {b}(k i j)(Ω:Ortho.Skew) (A:(BellTableMars p Y).Field b):
    D (direction 0 k) (fun x=>RhythmMars A W x χ (Payroll.desk 0 Ω) j i) x= RhythmMars (riseUpsMars k A) W x χ (Payroll.desk 0 Ω) j i- (Ω.val i k) • RhythmMars A W x χ (Payroll.ticket i) j i:=by
 let v:=direction (0:Fin (n+1)) k; let F:=PFoilMoon A W j i; let G:= D (Points.cons 0 v) F
 have he:filingMars 0 Ω v i=Ω.val i k:=by simp[filingMars,v,direction]
 have hz:= RulerMars H G (PFoilMoon (riseUpsMars k A) W j i) (fun y hx=>FoilQUpMars W H _ _ _ A y hx) (Payroll.desk 0 Ω) χ j i x 0 h; change D v (RyeMars F (Payroll.desk 0 Ω) χ j i) x=_; rw [spendDeskMars F (foilSMMars _ _ _ _ _) 0 Ω χ x h v, he]; exact congrArg (·- _) hz
-- D sum operator cost
lemma ΛSumTilt {α:Type*}(s:Finset α)(k: Axis)(f:α→Points (n+1)→ℂ)(u:∀ j∈s,DifferentiableAt ℝ (f j) x): D (direction 0 k) (fun x=>∑ j∈s, f j x) x=∑ j∈s,D (direction 0 k) (f j) x:=by
 unfold D; rw [fderiv_fun_sum u,_root_.sum_apply]
lemma htiltMars (j i:Axis)(K:Payroll (n+1)){b} (A:(BellTableMars p Y).Field b):DifferentiableAt ℝ (fun x=> RhythmMars A W x χ K j i) x:=
    (((PodDPMars (PFoilMoon A W j i) (foilSMMars W _ _ _ _) χ 0 _ _ K) x h).contDiffAt ((BreathingMars χ (0:Fin (n+1))).mem_nhds h)).differentiableAt (by simp)
lemma DΘMilesMars (k i:Axis){b}(A:(BellTableMars p Y).Field b): D (direction 0 k) (fun x=> ΘMilesMars A W x χ i) x= ΘMilesMars (riseUpsMars k A) W x χ i:=by
 unfold ΘMilesMars; rw [ΛSumTilt x χ h H _ _ _ (fun j _=> htiltMars W x χ h H _ i (Payroll.ticket i) A)]; exact sum_congr rfl (fun j _=> tiltΘMars W x χ h H ..) -- lemma inclusion order tune
lemma DΩMilesMars (k:Axis)(Ω:Ortho.Skew){b}(A:(BellTableMars p Y).Field b): D (direction 0 k) (fun x=> ΩMilesMars A W x χ Ω) x= ΩMilesMars (riseUpsMars k A) W x χ Ω - (∑ i:Axis, (Ω.val i k) • ΘMilesMars A W x χ i):=by
 let K:=Payroll.desk (0:Fin (n+1)) Ω; let F(j i:Axis)(x:Points (n+1)):= RhythmMars A W x χ K j i
 have he(j i): DifferentiableAt ℝ (F j i) x:= htiltMars W x χ h H _ _ _ A
 unfold ΩMilesMars
 rw[ΛSumTilt x χ h H univ k (fun j y=>∑ i:Axis,F j i y) (fun j _=>DifferentiableAt.fun_sum (fun i _=>he j i))] -- defeq rw let
 have ht(j:Axis):D (direction 0 k) (fun x=>∑ i:Axis,F j i x) x= ∑ i:Axis,(RhythmMars (riseUpsMars k A) W x χ K j i -(Ω.val i k) • RhythmMars A W x χ (Payroll.ticket i) j i):=by
    rw [ΛSumTilt x χ h H univ k (F j) (fun i _=>he j i)]; exact sum_congr rfl fun i _=> tiltΩMars W x χ h H k i j Ω A
 simp_rw [ht,sum_sub_distrib]; unfold ΘMilesMars; simp_rw [smul_sum]; congr 1; exact sum_comm
omit h
lemma TraverseMoonMars (j:Axis){a}(A:(BellTableMars p Y).Field a)(e:EpochLunaMars a A): EpochLunaMars (a+1) (riseUpsMars j A):=by
 intro n D s x χ g k
 let U:=highQtyMars p Y s; let v:=direction (0:Fin (n+1)) j
 rw [← DΘMilesMars U x χ g H j k A]
 have hm: riseUpsMars k (riseUpsMars j A)=riseUpsMars j (riseUpsMars k A):= (DictumMars p Y).abelian (SymHallMars H) (DictTiltMars H) (BellSmMars p Y) A k j
 rw [hm]; exact (GermD v (((BreathingMars χ (0:Fin (n+1))).eventually_mem (show x∈ _ from g)).mono (fun i t=>e n D s i χ t k))).trans (dialπMars H U (riseUpsMars k A) x g.bounds j).symm
lemma TraverseSpinMoon (j:Axis){a}(Ω:Ortho.Skew)(A B:(BellTableMars p Y).Field a)(e:EpochLunaMars a A)(f: FortuneMars a Ω A B):
    FortuneMars (a+1) Ω (riseUpsMars j A) (riseUpsMars j B + ∑ i:Axis,(Ω.val i j : ℂ) • riseUpsMars i A):=by
 intro n D s x χ g
 let U:=highQtyMars p Y s; let v:=direction (0:Fin (n+1)) j
 have ht:Analysis.D v (fun x=> ΩMilesMars A U x χ Ω) x=TideLunaMars (riseUpsMars j B) U x:=
    (GermD v (((BreathingMars χ (0:Fin (n+1))).eventually_mem (show x∈_ from g)).mono (fun i t=> f n D s i χ t))).trans (dialπMars H U B x g.bounds j).symm
 rw [DΩMilesMars _ _ _ g H] at ht -- v
 rw [← LunaPriceMars U x,map_add,map_sum, LunaPriceMars]; simp_rw [map_smul, LunaPriceMars]; simp_rw [show U=highQtyMars p Y s from rfl, e _ _ _ _ _ g,Complex.real_smul] at ht; exact sub_eq_iff_eq_add.mp ht
#check dialπMars
#print axioms DΘMilesMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
