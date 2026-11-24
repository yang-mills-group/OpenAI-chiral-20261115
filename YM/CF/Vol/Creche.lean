import YM.CF.Vol.Harp
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
variable {s':Signed}{k:S.Choices}
private lemma stl {f:E× B→G.Color}{m:E→B}{z:E→L[ℝ] B}(hx:0≤ t)(hm:m 0=0)(hp:DifferentiableAt ℝ m 0)(hs:‖fderiv ℝ m 0 - z‖ ≤ C)(ht:DifferentiableAt ℝ f 0)(he:‖fderiv ℝ f 0‖≤ D)(hh:∀ x, minor f (x,z x) (‖x‖*t))(h:∀ x:B, ‖fderiv ℝ f 0 (0,x)‖ ≤ ‖x‖*t): stance (f ∘ pulse m) (t+t+D*C):=by
 have h(y:E× B):‖fderiv ℝ f 0 (0,y.2)-fderiv ℝ (0:E× B→ G.Color) 0 y‖ ≤ ‖y‖*t:=by simpa using (h y.2).trans (mul_le_mul_of_nonneg_right (norm_snd_le y) hx)
 have hg:= stance_p hx hm hp hs ht he hh rfl (differentiableAt_const _) h; change stance (f ∘ pulse m -0) _ at hg; rwa [sub_zero] at hg
lemma mart(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s:Signed)(l:ℕ)(p:K.Funds S T){z:Bid.Dir G c→AxisChart G F}(R Q A:ℝ)(ha:0≤ A)
 (Q':Marble n T (Jazz T (choice s k) s) (Jade T (choice s k) s) (choice s k) (Stores.till x) (0: Ark T F) Q)(hn:1 ≤ n)
 (hL:∀ v:Mast G c, Frank T (Stores.till x) (choice s k) (Jazz T (choice s k) s) (Jade T (choice s k) s) (‖v‖*A) (v,fderiv ℝ (station z) 0 v)∧ Duke T (Stores.till x) (choice s k) (Jazz T (choice s k) s) (Jade T (choice s k) s) (‖v‖*A) (v,fderiv ℝ (station z) 0 v))
 (hp:∀ v: Fish (Key F G), Duke T (Stores.till x) (choice s k) (Jazz T (choice s k) s) (Jade T (choice s k) s) (‖v‖*A) (0,v))
 (hg:∀ i: Slots S, DifferentiableAt ℝ (gloss T x F k i) 0):
 let m:=sol S T k x F l; m 0=0 → DifferentiableAt ℝ m 0 → ‖fderiv ℝ m 0-fderiv ℝ (station z) 0‖ ≤ R → Acres T x F k s l (A+A+Q*R):=by
 intro m hm he ht; let F':=Jazz T (choice s k) s (F:=F); let Z:= Jade T (choice s k) s (F:=F)
 let σ:= fderiv ℝ (station z) 0
 have hX (f:Ark T F→ G.Color) (i: Slots S)(hS: Allows n f 0 Q)(hF:∀ x:Mast G c,minor f (x,σ x) (‖x‖*A))(h:∀ v: Fish (Key F G),fderiv ℝ f 0 (0,v)= bump T x 1 k (meal F x v) i): stance (f ∘ (pulse m) -gloss T x F k i) (A+A+Q*R):=by
    refine stance_p ha hm he ht (hS.analytic.differentiableAt (by simp)) (drops2 (paper hS) hn) hF (down_D T x F k i p (hg i) 0).1 (hg i) ?_
    intro u; rw [h,(down_D T x F k i p (hg i) u).2,sub_self,norm_zero]; positivity
 have hy(v:Fish (Key F G)):= vert_g T x F k s v p Q'; let r:=Stores.till x
 have hv (f:Ark T F→ G.Color)(h:Allows n f 0 Q)(hK:∀ v:Mast G c, minor f (v,σ v) (‖v‖*A))(hR:∀ v:Fish (Key F G),‖fderiv ℝ f 0 (0,v)‖ ≤ ‖v‖*A): stance (f ∘ pulse m) (A+A+Q*R):= stl ha hm he ht (h.analytic.differentiableAt (by simp)) (drops2 (paper h) hn) hK hR
 constructor
 · intro i; exact hX _ _ (Q'.roof i) (fun t=> (hL t).1.F i) (fun z=> (hy z).1 i)
 · intro i; exact hX _ _ (Q'.jamb i) (fun t=> (hL t).1.I i) (fun z=> (hy z).2 i)
 · intro i; exact hv (fun y=> RiftL r (F' y) (Z y) T (choice s k) i) (Q'.letup i) (fun t=>(hL t).2.L i) (fun v=> ((hp v).L i).2)
 · intro i; apply (show stance ((fun y=> RiftN r (Z y) T i) ∘ pulse m) _ from hv _ (Q'.nPole i) (fun t=> (hL t).1.N i) ?_); intro v
   let Y(y:Ark T F):=RiftN r (Z y) T i; let a:Ark T F := (0,v); have hK:= Push.side Y ((Q'.nPole i).analytic.differentiableAt (by simp)) a
   have he(t:ℝ):Y (t • a)=Y 0:=by unfold Y Z Jade; rw [show (t • a).1=t • 0 from rfl,smul_zero]; rfl
   simp_rw [he] at hK; change ‖fderiv ℝ Y 0 a‖≤_; rw [show fderiv ℝ Y 0 a=0 from hK.unique (hasDerivAt_const ..),norm_zero]; positivity
 intro i; exact hv _ (Q'.dPole i) (fun t=>(hL t).2.D i) (fun v=> ((hp v).D i).2)
lemma fund_s (T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s:Signed)(l:ℕ)(u:Ark T F)(y z A:ℝ)
 (p:Jet.Allows n (pulse (sol S T k x F l)) u z)(he:Marble n T (Jazz T (choice s k) s) (Jade T (choice s k) s) (choice s k) (Stores.till x) (pulse (sol S T k x F l) u) y) (h:∀ i,Jet.Allows n (gloss T x F k i) u A): Well T x F k s l n (max (Jet.composeCost n y z) A) u:=by
 refine ⟨fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i=> (h i).mono (le_max_right ..),fun i=>?_,fun i=>?_,fun i=>?_⟩
 all_goals first
   | exact (((paper (he.roof i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.jamb i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.letup i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.nPole i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.dPole i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.pays i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.S i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.Q i)).comp p).mono (le_max_left ..))
   | exact (((paper (he.I i)).comp p).mono (le_max_left ..))
end YM.CF.Vol
