import YM.CF.Neige.Key
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable {θ m U D v':ℝ}{q:Chi} {M: Gaussian.Table (Rows.In x A F (G:=G))}{M':Gaussian.Table (Rows.In x A' F' (G:=G))} {N:ℝ→ Gaussian.Table (Rows.In x A F (G:=G))}{N':ℝ→Gaussian.Table (Rows.In x A' F' (G:=G))}
def Miles(S:StepData c f)(r:ℕ)(i j:Bond f):Prop:= ∀ y∈Next.SectorChange.points S i, ∀ z∈Next.SectorChange.points S j, separation y z  ≤ r
def Speaks {x:ℝ} (S:StepData c f){A:Stores S}{F:Forest S.ratio}(p:Run (Active A x F) n):Prop:= p 0=p (Fin.last _) ∧∀ i:Fin n, Miles S (3*radiusB x) (p i.castSucc).val.val (p i.succ).val.val
lemma from_pair(i j:Rows.In x A F (G:=G))(hr:1000 ≤ radiusB x)(h: separation (front A F i) (front A F j)  ≤ 2*radiusB x): Miles S (3*radiusB x) i.1.val.val j.1.val.val:=by
 intro y hy z hz; have h₁:separation (front A F i) y  ≤ 1:=meetings _ hy; have h₂:separation (front A F j) z ≤ 1:=meetings _ hz; apply (separation_triangle y (front A F j) z).trans
 have hh:=separation_triangle y (front A F i) (front A F j); rw [separation_comm (front A F i) y] at h₁; omega
lemma muzzled(hr:1000 ≤ radiusB x)(hp:Names M (radiusB x))(ht:∀ t:ℝ, Names (N t) (radiusB x))(w:Run (Active A x F) (n+1))(hx:¬Speaks S w):barP M N w=0:=by
 have he(t:ℝ): tileX M N w t=0:=by
    apply Finset.sum_eq_zero; intro j hj; dsimp only; split
    next h=>
        have hl (i : Fin (n+1)):Names (linkX n M (N t) t i) (2*radiusB x):=by
            cases i using Fin.cases with
            | zero=> exact (hp.maps (ht t)).under (by omega)
            | succ i=> simp only [linkX,Fin.cons_succ]; exact (lanes_one _).less ((((lanes_one _).plus (hp.scaling t)).maps (ht t)).under (by omega))
        have hh : ∃ i: Fin (n+1), ¬ Miles S (3*radiusB x) (w i.castSucc).val.val (w i.succ).val.val:= by by_contra! hu; exact hx ⟨h.1.symm,hu⟩
        obtain ⟨i,hi⟩:=hh
        apply Finset.prod_eq_zero (Finset.mem_univ i); exact (hl i).rank ((mix w j) i.castSucc) ((mix w j) i.succ) (lt_of_not_ge fun h=>hi (from_pair _ _ hr h))
    rfl
 unfold barP; simp [he]
lemma familiar{p:Run (Active A x F) (n+1)}{w:Run (Active A' x F') (n+1)} (hb:Sample k V Y l M k' W Y' M')(hN:∀ t:ℝ,Sample k V Y l (N t) k' W Y' (N' t))(hX:Names M r)(hZ:Names M' r)(hP:∀ i, (p i).val.val=(w i).val.val)(h:∀ i,Scan S x (S.ratio.parent (p i).val.val.1) (l+r) A A' F F' k k' V W Y Y'): barP M N p=barP M' N' w:=by
 apply setIntegral_congr_fun measurableSet_Icc; intro t ht; dsimp only [tileX,close]
 apply Finset.sum_congr rfl; intro i hi
 have he(p1 p2): p p1=p p2↔w p1=w p2:=by simp_rw [Subtype.ext_iff, hP]
 have hx : p (Fin.last _)=p 0∧i (Fin.last _)=i 0↔ w (Fin.last _)=w 0 ∧ i (Fin.last _)=i 0:=and_congr (he ..) Iff.rfl
 simp_rw [he]; split; swap; · rfl
 apply Finset.prod_congr rfl; intro j hj
 let X(t):=mix p i t; let Z(t):=mix w i t; have hh(t):PatchReads.lift (X t)=PatchReads.lift (Z t):= Prod.ext (hP t) rfl
 have hr:Sample k V Y (l+r) (linkX n M (N t) t j) k' W Y' (linkX n M' (N' t) t j):=by
    cases j using Fin.cases with
    | zero=> exact tile_mul hb (hN t) hX hZ (by omega)
    | succ j=> simp only [linkX,Fin.cons_succ]; exact stone_s.less (tile_mul (stone_s.plus (hb.scaling t)) (hN t) ((lanes_one _).plus (hX.scaling t)) ((lanes_one _).plus (hZ.scaling t)) (by omega))
 exact hr _ _ _ _ (h j.castSucc) (hh j.castSucc) (hh j.succ)
end YM.CF.Neige
