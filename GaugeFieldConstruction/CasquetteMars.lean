import GaugeFieldConstruction.NutrisMars
/-!
 # formal derivation of all finite grades. both signed directions active. no new assumptions on rank equality needed.
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
local notation "T"=> BellTableMars p Y
local notation "M"=> TerraMars p Y
namespace FirstPackMars
def liftLlMars {d e:ℕ}(h:d≤e)(l:TrailsMars d): TrailsMars e:=⟨⟨l.1.val,lt_of_lt_of_le l.1.isLt (Nat.succ_le_succ h)⟩,l.2⟩
def liftLaMars {d e:ℕ}(h:d≤e)(i:LabelMars d): LabelMars e:= IndexMars e ((ChaseMars d i).1,liftLlMars h (ChaseMars d i).2)
def pushLlMars {d:ℕ}(a: CompassMars)(l:TrailsMars d):TrailsMars (d+1):=⟨l.1.succ,(Fin.cons a l.2)⟩
def pushLaMars {d:ℕ}(a: CompassMars)(i:LabelMars d): LabelMars (d+1):=IndexMars _ ((ChaseMars d i).1,pushLlMars a (ChaseMars d i).2)
noncomputable def ΛTransportMars {d e:ℕ}(f:LabelMars d→LabelMars e):FlyerMars d→ₗ[ℂ] FlyerMars e:= ∑ i:LabelMars d,(LinearMap.proj i).smulRight (coneOneMars e (f i))
abbrev ΛRiseMars {d e:ℕ}(h:d≤e):= ΛTransportMars (liftLaMars h)
abbrev ΛSlopeMars (d:ℕ)(a:CompassMars):= ΛTransportMars (d:=d) (pushLaMars (d:=d) a)
lemma ΛTAtMars {d e:ℕ}(f:LabelMars d→LabelMars e)(i:LabelMars d): ΛTransportMars f (coneOneMars d i)=coneOneMars e (f i):=by
 unfold ΛTransportMars; rw [LinearMap.sum_apply,Finset.sum_eq_single i]
 · simp [coneOneMars]
 · intro j _ v; simp [coneOneMars,v]
 simp
lemma PeelLMars {d e:ℕ}(h:d≤ e)(i:LabelMars d): ChaseMars e (liftLaMars h i)=((ChaseMars d i).1, liftLlMars h (ChaseMars d i).2):=(IndexMars e).symm_apply_apply _
lemma PeelPMars {d:ℕ}(i:LabelMars d)(a:CompassMars): ChaseMars (d+1) (pushLaMars a i)=((ChaseMars d i).1,pushLlMars a (ChaseMars d i).2):=(IndexMars _).symm_apply_apply _
lemma moveαMoon {d e:ℕ}(h:d≤e)(D:NSF.Caps n)(i:LabelMars d)(w:LabelsMars D)(x:Points (n+1)): (T).read x (Fin.cons (coneMaskMars e (liftLaMars h i)) (TiesMars D w))=(T).read x (Fin.cons (coneMaskMars d i) (TiesMars D w)):=by rw [ArcBillMoon p Y,ArcBillMoon p Y,PeelLMars]; rfl
lemma pushTrailMars {d:ℕ}(a:CompassMars)(u:TrailsMars d): unfoldTrailsMars (pushLlMars a u)=a :: unfoldTrailsMars u:= List.ofFn_succ -- tune
lemma tiltαMoon {d:ℕ}(D:NSF.Caps n)(a:CompassMars)(i:LabelMars d)(w:LabelsMars D)(x:Points (n+1)): (T).read x (Fin.cons (coneMaskMars _ (pushLaMars a i)) (TiesMars D w))=Analysis.D (guideDirMars (0,a)) (fun y=>(T).read y (Fin.cons (coneMaskMars _ i) (TiesMars D w))) x :=by rw [ArcBillMoon p Y,PeelPMars,pushTrailMars _ _]; simp_rw [ArcBillMoon p Y]; rfl
lemma lumMars {E:Type*}[AddCommGroup E][Module ℂ E]{d:ℕ}(g:FlyerMars d→ₗ[ℂ] E)(x:FlyerMars d):g x=∑ i: LabelMars d,x i • g (coneOneMars d i):=by
 conv_lhs=> rw [← Finset.univ_sum_single x]
 rw [map_sum]; refine Finset.sum_congr rfl fun i _=> ?_
 rw [←map_smul]; congr 1; ext a; by_cases h:a=i <;> simp[coneOneMars,h] -- remove I
lemma guidMultMars {d:ℕ}(i:LabelMars d)(w:Fin n→ΡeaderMars.Token)(a:CompassMars)(x:Points (n+1))(h:x∈conf (n+1)): (T).read x (Fin.cons (coneMaskMars _ (pushLaMars a i)) w)=Analysis.D (guideDirMars (0,a)) (fun y=>(T).read y (Fin.cons (coneMaskMars d i) w)) x:=by
 let N:=ArrangeT n w; let F (ρ:LabelsMars N) :=fun y=>(BellTableMars p Y).read y (Fin.cons (coneMaskMars d i) (TiesMars N ρ))
 have he(ρ):DifferentiableAt ℝ (F ρ) x:=by
    have hz := ((T).smooth_read (BellSmMars p Y) (Fin.cons (coneMaskMars d i) (TiesMars N ρ)) x h).contDiffAt ((conf_open _).mem_nhds h); exact hz.differentiableAt (by simp)
 conv_lhs=>rw[FullTailQtyMars]
 conv_rhs=> arg 2; intro y; rw[FullTailQtyMars] -- deriv application elaboration arg 2?
 simp_rw [tiltαMoon p Y]
 let X:=guideDirMars (n:=n+1) (0,a); let A(ρ:LabelsMars N):= ChartTaxMars (d:=N) (fun i=>(w i).2) ρ
 change (∑ ρ:LabelsMars N,A ρ * YM.Analysis.D X (F ρ) x)=YM.Analysis.D X (fun y=>∑ ρ:LabelsMars N,A ρ * F ρ y) x
 rw [D,fderiv_fun_sum (fun i _=>(he i).const_mul _),_root_.sum_apply] -- unfolds LHS first!
 apply sum_congr rfl; intro j _; rw [fderiv_const_mul (he _)]; rfl -- tune over ℝ
lemma paidArcMars {d e:ℕ}(f : FlyerMars d→ₗ[ℂ] FlyerMars e)(v:FlyerMars d)(w:Fin n→ΡeaderMars.Token)(x:Points (n+1)): (T).read x (Fin.cons (PostMars e (f v)) w) = ∑ i:LabelMars d, v i * (T).read x (Fin.cons (PostMars e (f (coneOneMars d i))) w):= lumMars (((T).injectFront w x e) ∘ₗ f) v
lemma backαMoon {d e:ℕ}(h:d≤e)(i:LabelMars d)(w:Fin n→ΡeaderMars.Token)(x:Points (n+1)):
    (T).read x (Fin.cons (coneMaskMars e (liftLaMars h i)) w)=(T).read x (Fin.cons (coneMaskMars d i) w):=by rw[FullTailQtyMars, FullTailQtyMars]; apply sum_congr rfl; intro j _; rw [moveαMoon _ _ h]
lemma doorsαMoon {d e:ℕ}(h:d≤e)(v: FlyerMars d)(w:Fin n→ΡeaderMars.Token)(x:Points (n+1)):
    (T).read x (Fin.cons (PostMars e (ΛRiseMars h v)) w)=(T).read x (Fin.cons (PostMars d v) w):=by
 rw [paidArcMars]; refine Eq.trans ?_ (paidArcMars p Y (LinearMap.id: FlyerMars d→ₗ[ℂ] FlyerMars d) v w x).symm
 apply sum_congr rfl; intro i j; rw [ΛRiseMars,ΛTAtMars]; exact congrArg (v i *·) (backαMoon p Y h i w x)
lemma guidePriceMars {d:ℕ}(v:FlyerMars d)(w:Fin n→ΡeaderMars.Token)(x:Points (n+1))(h:x∈conf (n+1))(a: CompassMars):
    (T).read x (Fin.cons (PostMars (d+1) (ΛSlopeMars d a v)) w)=YM.Analysis.D (guideDirMars (0,a)) (fun y=>(T).read y (Fin.cons (PostMars d v) w)) x:=by
 rw[paidArcMars]
 let f := (LinearMap.id: FlyerMars d→ₗ[ℂ] FlyerMars d)
 conv_rhs=> change D _ (fun y=>(BellTableMars p Y).read y (Fin.cons (PostMars d (f v)) w)) x; arg 2; intro y; rw [paidArcMars]
 simp_rw [ΛSlopeMars,ΛTAtMars, PostMars]; -- need list. next goal
 let F(i:LabelMars d):= fun y=> (BellTableMars p Y).read y (Fin.cons (coneMaskMars d i) w)
 have he(i): DifferentiableAt ℝ (F i) x:= (((BellSmMars p Y).on_conf _ _ x h).contDiffAt ((conf_open _).mem_nhds h)).differentiableAt (by simp)
 let X:=guideDirMars (n:=n+1) (0,a); change _= YM.Analysis.D X (fun y=>∑ i: LabelMars d,v i * F i y) x; rw [YM.Analysis.D, fderiv_fun_sum (fun i _=>(he i).const_mul _),_root_.sum_apply]; apply sum_congr rfl; intro i _; rw [fderiv_const_mul (he _)]; exact congrArg (v i *·) (guidMultMars p Y i w a x h)
#print axioms guidePriceMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
