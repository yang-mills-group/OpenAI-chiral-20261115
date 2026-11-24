/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.BProof.Harbor.Arbor
import YM.CF.Rill.Peak
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory ProbabilityTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Skye Half Arbor Rush AnalyticBridge.GaussianFieldAlignment
namespace ArborW
variable {c f n m:Side} (S:StepData c f) (s:Signed) (b:Site c)
private theorem upright : Bijective (Locations.forest (S:=S) s b):=Finite.injective_iff_bijective.mp (fun A D he => idem A D (funext fun i=>by
  obtain ⟨i,rfl⟩ := (StepData.sendSites s (S.ratio.embed b)).surjective i; have hk := congr_fun (congr_arg Forest.up he) i; change Step.rotate _ s⁻¹=Step.rotate _ _ at hk; apply_fun (·.rotate s) at hk; simp only [Step.rotate_mul,mul_inv_cancel,Step.rotate_one] at hk; exact hk
 ) (funext fun i=>by obtain ⟨i,rfl⟩ := (StepData.sendSites s (S.ratio.embed b)).surjective i; exact congr_fun (congr_arg Forest.height he) i))
private lemma warp (W:Ratio c f)(p:S.ratio=W): Bijective (fun x:Forest W=> (p ▸ (Locations.forest s b (p.symm ▸ x) : Forest S.ratio) : Forest W)):=by subst W; exact upright S s b
variable {T:StepData (More n) (More m)}(G:Ratio n m) {q: Push.SectorMeasure.Chi} {z:ℝ}{R:Patch} {r l k:ℕ}
variable (h:T.ratio=ratio G)
lemma align (s:Sweep n)[Nonempty (Forest (ratio G))] : MeasurePreserving (fun x: Forest (ratio G)=> moveTree G T h x s) (grove _) (grove _):= Vogue.orderMP (Equiv.ofBijective (fun x=> moveTree G T h x s) (warp T s.s ((assembly n).embed s.b) (ratio G) h))
lemma belong (W Y:Ratio c f)(q:W=Y)(F:Forest Y): (q ▸ (q.symm ▸ F : Forest W) : Forest Y)=F:=by cases q; rfl
lemma whose (X:Forest (ratio G)): h ▸ toForest G T h X=X:=belong _ _ h X -- tactic fails dependency
lemma forest_x {N M:Side}(x y:Ratio N M) (h:x=y)(A: Forest x): Forest.up (h ▸ A : Forest y) = Forest.up A:=by subst x; rfl
variable (X:ClockD R r l k)(p:G.count=R.L)(i:Axis)
-- (ClockD R mρ n k)
local notation "Xs" b:max => shade n i b X.pF
local notation "Ys" b:max => shade m i b X.pF
local notation "Φs" b:max=>Leg.reach G (shade n i b X.uF) k
open Precision -- Chi
include p h
lemma seer (A B:Forest (ratio G))(U V:Pane n)(P Q:Pane m)(b:Bool) (v:∀ i, (ratio G).parent i ∈ Xs b → A.up i=B.up i)(x:Agrees (↑(Xs b)) U V)(y:Agrees (↑(Ys b)) P Q): Agrees (↑(Φs b)) (seine G A q z P U) (seine G B q z Q V):=by
 let C:=Xs b; let K:=(ratio G).parent; intro l u g; let H:=(Φs b).image K; let f:=toForest G T h; rw [←whose G h A, ←whose G h B]
 refine Rill.seineR G h (f A) (f B) P Q U V z l (E:=H) (h ▸ mem_image_of_mem K u) (F:=C) (ClockD.ripley i G X p b) (fun x ht=>?_) x ?_
 · have hx:= X.kids i G p b x (h ▸ ht); exact y x (hx (by simp)) (hx (by simp))
 intro j u; unfold f toForest; rw [forest_x _ _ h.symm, forest_x _ _ h.symm]; exact v j (h ▸ u)
variable (q:Push.SectorMeasure.Chi) -- qualified
omit p
lemma mirrorG {V:Pane n}{U:Pane m}(F:Forest (ratio G)) : seine G (moveTree G T h F (Fixed.reflectSweep n i)) q z (Fixed.reflConfig m i U) (Fixed.reflConfig n i V)= Fixed.reflConfig m i (seine G F q z U V):=by
 let j:=Fixed.reflectSweep n i; let y:=Fixed.reflectSweep m i; have hp: reSweep G j=y:=by simp [y,j,reSweep,Fixed.reflectSweep]; exact map_zero G.root
 rw [←Fixed.flash_reflect, ←Fixed.flash_reflect, ←Fixed.flash_reflect]; change seine G (moveTree G T h F j) q z (flashA y U) _ = flashA y _; rw [←hp]; exact seine_mv G q z T h F j V U
end ArborW
end YM.CF.BProof.Bide
