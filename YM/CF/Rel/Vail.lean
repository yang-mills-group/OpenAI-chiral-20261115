import YM.CF.Rel.Cool
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
abbrev portV(j:Body 2 n):Wind n:= Sum.inl ((ŧ n).symm j)
lemma hub {o:Site n}{i:Fin m}{r:Disk n m}(hp:r∈Pots o l m): (boot o (portV (r i))).length ≤ 2*(4*l)+4:=by
 obtain hx:= (shade_p.mp hp) i; obtain ⟨⟨x,b⟩,he⟩:= (ŧ n).surjective (r i); have hp:(ŧ n (x,b)).1=x:=rfl; rw [←he,hp] at hx; rw [← he]; unfold portV; rw [(ŧ n).symm_apply_apply]; unfold boot; simp only [List.length_append,square,List.length_cons,List.length_nil, reverse,List.length_reverse,List.length_map]; have hy:=short o x; omega
open Push.Uniform
lemma storms(G:Gauge)(k:ℕ):∃ C:ℝ,0≤ C∧∀{n:Side}(x:InputZ G n),‖x‖ ≤ 1→∀ i:Blip n, Push.Uniform.Allows k (fun y:InputZ G n=> G.mat (represent y i)) x C:=by
 obtain ⟨C,hC,h⟩:=exists_allows (isCompact_closedBall (0:G.Color) 1) (fun i (_: i∈closedBall (0:G.Color) 1)=>G.exp_jet.contDiffAt (x:=i)) k -- tune structure
 refine ⟨composeCost k C 1,by unfold composeCost; positivity,fun {n} x he i=>?_⟩; let L:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _: Body 1 n=>G.Color) (Trot _ i)); have ht:‖L x‖≤1:=(norm_le_pi_norm x (Trot _ i)).trans he
 simp_rw [Work.F03.represent_link]; exact (h _ (mem_closedBall.mpr (by rw [dist_zero_right]; exact ht))).comp (f:=L) (allows_linear (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y=> by rw [one_mul]; exact norm_le_pi_norm y (Trot _ i)) ht) -- tune
lemma yard (G:Gauge)(k:ℕ):∃ f:ℕ→ℝ,nib f ∧∀ l:ℕ,∀{n:Side}(x:InputZ G n), ‖x‖ ≤ 1 → ∀ (i:Site n)(w:Walk),w.length ≤ 2*(4*l)+4→Allows k (fun y:InputZ G n=> G.curvature (travel (represent y) i w)) x (f l):=by
 obtain ⟨C,hC,H⟩:=storms G k; let L : G.Mat→L[ℝ] G.Color:= G.projectColor.toContinuousLinearMap
 let P:=fun i:ℕ=> travelCost G k (2*(4*i)+4) C; let X:= fun i=> AnalyticBridge.SectorAffine.curvatureCost G * P i
 have hp:nib P:=by
    have hL:CapY (fun i=>2*(4*i)+4):=((CapY.lives.scal 4).scal 2).add (seedR 4)
    let B:= Real.exp 1* ‖(1:G.Mat)‖
    apply nib.mul _ (nib_const ((1+C)^k) (by positivity)) -- tune implicit
    exact (nib_const _ (Nat.cast_nonneg k.factorial)).mul ((nib_const B (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mul (((nib_const 1 zero_le_one).add ((nib_const ((2:ℝ)^k) (by positivity)).mul ((nib_const 1 zero_le_one).add (nib.mate hL)))).pow _))
 exact ⟨X,(nib_const _ (AnalyticBridge.SectorAffine.curvature_nn G)).mul hp,fun i _ x hx j w hw=> AnalyticBridge.SectorAffine.curvature_price (travel_jets (H x hx) j hw)⟩
end YM.CF.Rel
