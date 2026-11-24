import YM.CF.Siete.Fiance
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Shelter
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Held
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
open MultiNext.SignedSource Lyre Banjo Analysis Pressure Next.Fluctuations
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n m:Side}{k p j:ℕ}{B:BudgetPoint}{X:Support (More n)}{o a:Seat n}{C ε u Q:ℝ}{V:Pane n}{g:Seat n→SU.E}{r:ℕ}
abbrev sphereQ(V:Pane n)(o:Seat n)(r:ℕ)(g:Seat n→SU.E) : tangD n → tangD n:= crop o r g ∘ increment V
lemma lift_q (p:Canvas B o r V g k C) (e:reach n)(h:separation o e.1≤ r): g e.1* V e* (g (e.1+step e.2))⁻¹= group.lieExp (crop o r g V e):= (p.seen.self_of_nhds e h).trans (mul_one _)
abbrev pier (e:reach n)(u:SU.E): tangD n→L[ℝ] group.Color:=(group.adjoint u).toContinuousLinearMap.comp (ContinuousLinearMap.proj e)
private def bar(e:reach n)(u:SU.E): tangD n→L[ℝ] Heir.Chord group:= (0: tangD n→L[ℝ] (group.Color×group.Color)).prod ((pier e u).prod (0:_→L[ℝ]_))
private lemma bar_norm(e:reach n)(u:SU.E)(x:tangD n): ‖bar e u x‖=‖x e‖:=by
 unfold bar pier; simp [Prod.norm_def]
lemma hatV (p:Canvas B o r V g k C) (e:reach n)(h:separation o e.1≤ r)(v:tangD n): sphereQ V o r g v e=Heir.decode (((0,0),(0,crop o r g V e))+bar e (g e.1) v):=by
 let H:tangD n→Pane n:=increment V; have he:gauge g (increment V v) e= group.lieExp (group.adjoint (g e.1) (v e))*gauge g V e:=by rw [Next.SectorChange.exp_adjoint]; unfold Lattice.gauge increment; group
 change crop o r g (increment V v) e= _; rw [crop,if_pos h, he,show gauge g V e= _ from lift_q p e h]; unfold decode Heir.touch bar; simp [pier]
lemma post_jet (p:Canvas B o r V g k C) (e:reach n)(w a:ℝ)(ht:‖crop o r g V‖ ≤ w)(ha:∀ x:Heir.Chord group, ‖x‖ ≤ w→Through k Heir.decode x a)(h:separation o e.1≤ r) (y:Seat n)(v:Fin j→ tangD n)(hv:∀ i,B.dirBound y (v i))(q:j≤k)(u:tangD n := 0)(hx:u=0): ‖iteratedFDeriv ℝ j (sphereQ V o r g) u v e‖ ≤ a * (Lyre.width B y e)^j:=by
 subst u; let A:=crop o r g V e; let δ:Heir.Chord group:=((0,0),(0,A)); have hg:‖δ‖≤w:=by simpa [δ,Prod.norm_def] using (norm_le_pi_norm (crop o r g V) e).trans ht
 let F:(Heir.Chord group)→ group.Color:=fun z=>decode (δ+z); have hF:ContDiffAt ℝ (j:ℕ∞ω) F 0:= (show ContDiffAt ℝ (j:ℕ∞ω) Heir.decode (δ + 0) by rw [add_zero]; exact (ha _ hg).smooth.of_le (Nat.cast_le.mpr q)).comp (f:=fun z=> δ+z) 0 (contDiffAt_const.add contDiffAt_id)
 let L: tangD n→L[ℝ] group.Color:= ContinuousLinearMap.proj e; let P:= sphereQ V o r g
 rw [show iteratedFDeriv ℝ j P 0 v e= iteratedFDeriv ℝ j (L ∘ P) 0 v from congrArg (fun f=> (f : (tangD n) [×j]→L[ℝ] group.Color) v) (L.iteratedFDeriv_comp_left (f:=P) p.germ le_top).symm] -- tune
 let u:=bar e (g e.1)
 rw [show L ∘ P=F ∘ u from funext fun i=> hatV p e h i,Push.Uniform.iter_lin_at (show ContDiffAt ℝ (j:ℕ∞ω) F (u 0) by rw [map_zero]; exact hF),map_zero]; unfold F; rw [iteratedFDeriv_comp_add_left, add_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 have h:= ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le ((ha _ hg).pay _ q) (show ∀ i,‖u (v i)‖≤Lyre.width B y e from fun i=> (bar_norm e _ _).trans_le (hv i e))
 simpa using h
lemma berth (p:Canvas B o r V g k C) (e:reach n)(h:r < separation o e.1)(v:Fin j→ tangD n): iteratedFDeriv ℝ j (sphereQ V o r g) 0 v e=0:=by
 let L: tangD n→L[ℝ] group.Color:= ContinuousLinearMap.proj e; let P:=sphereQ V o r g
 rw [show iteratedFDeriv ℝ j P 0 v e= iteratedFDeriv ℝ j (L ∘ P) 0 v from congrArg (fun f=> (f : (tangD n) [×j]→L[ℝ] group.Color) v) (L.iteratedFDeriv_comp_left (f:=P) p.germ le_top).symm]; rw [show L ∘ P=fun _=>0 from funext fun _=>if_neg h.not_ge, iteratedFDeriv_fun_zero]; rfl
end YM.CF.Siete
