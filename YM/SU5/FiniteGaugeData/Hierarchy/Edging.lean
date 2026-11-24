import YM.SU5.FiniteGaugeData.Hierarchy.Chalk
/-! # Estimating the upper-side dependence of the actual CAR stencil in one step -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Fiber
section
variable {X I:Type*}[MeasurableSpace X]
private lemma multiply {g h:I→X→SU.E}(p:Deal g)(q:Deal h): Deal (fun i x=>g i x*h i x):=
  (p.prod q).post (continuous_fst.mul continuous_snd)
private lemma flip {g:I→ X→SU.E}(p:Deal g):Deal (fun i x=> (g i x)⁻¹) := p.post continuous_inv
variable (N:I→ Side)(L:Side)(P:I→Side)(s:∀i,(P i).val=(N i).val*L.val)
variable (W:(i:I)→ X→ Pane (P i)) (v:Deal (fun (i:Σ i, Edge (Seat (P i))) x=> W i.1 x i.2))
local notation "G" => bead N L P s

private lemma finitely_sized (k:ℕ) : ({l:Walk | l.length≤k}:Set Walk).Finite := by
  let R:= Σ i :_root_.Fin (k+1), List.Vector Step i.val
  let F(v:R):Walk:= v.2.val
  classical
  letI : Finite Step:= Finite.of_injective (fun v:Step=>(v.dir,v.neg)) (by rintro ⟨a,b⟩ ⟨c,d⟩ t; simpa using t)
  letI : Fintype Step:=Fintype.ofFinite _
  haveI : Fintype R:= Sigma.instFintype
  exact (Set.finite_range F).subset (fun l (p:l.length≤k)=> ⟨⟨⟨l.length,Nat.lt_succ_of_le p⟩,l,rfl⟩,rfl⟩)
include v
lemma fold_m (k:(i:I)→Forest (ratio (bead N L P s i)))(a:(i:I)→Seat (P i)):
    Deal (fun i x=> (k i).foldAt (W i x) (a i): I→ X→SU.E) := by
  let R(i:I):= (k i).hike (a i); let S:= Set.range R
  have hS:S.Finite:=(finitely_sized (4*L.val)).subset (by rintro l ⟨i,rfl⟩; exact ((k i).hike_lower (a i)).trans ((k i).bound (a i)))
  classical
  haveI : Fintype S:= hS.fintype
  apply flip
  exact Deal.assembly (fun j:S=>fun (i:I) x=>travel (W i x) (a i) j.val) (fun j=>Satin.roam P W (fun z=>v.re (fun (i:I)=>(show (Σ i,Edge (Seat (P i))) from ⟨i,z i⟩))) _ _) (fun i=>⟨_,⟨i,rfl⟩⟩)

lemma seine_m (k:(i:I)→ Forest (ratio (bead N L P s i)))(a:(i:I)→ Edge (Seat (P i)))
    (V:(i:I)→ Pane (N i))(q:Chi)(e:ℝ) (p:0<e)(u:2*e<firstRadius SU.group) :
    Deal (fun i x=>seine (G i) (k i) q e (W i x) (V i) (a i):I→ X→SU.E):=by
  let x(i:I):=(a i).1; let y(i:I):=(a i).1+step (a i).2
  have hx:= fold_m N L P s W v k x; have hy:= fold_m N L P s W v k y
  apply multiply (multiply (flip hx) _) (flip (flip hy))
  apply ((multiply (multiply hx (v.re (fun i:I=>⟨i,a i⟩))) (flip hy)).prod (Deal.pure (X:=X) (T:=fun _=>SU.E) (fun i:I=>Precision.replica (ratio (bead N L P s i)) (show Config SU.group _ from V i) (a i)))).post (g:=fun (z:SU.E×SU.E)=>knit q e z.1 z.2)
  exact (SU.group.lieExp_cont.comp ((patched_continuous q p u).comp (continuous_fst.mul continuous_snd.inv))).mul continuous_snd

variable (j D:ℕ)(vA:LaurentRadius j L D)(ho:Odd L.val)
variable (M:I→ Male)(Q:I→Op SU.Slot){d:ℝ}(y:∀i,‖Q i‖ ≤ d)
variable (q:Chi)(e:ℝ) (p:0<e)(u:2*e<firstRadius SU.group)
include vA ho y p u
omit v
lemma gather (U:Chorus)(W:(i:I)→X→Fields (P i))(V:(i:I)→Fields (N i))
    (r:Deal (fun (i:Σ i,Edge (Seat (P i))) x=> (W i.1 x).2 i.2)) :
    Menu (T:=fun i=> FC (Single (P i))) (fun i x=> gathered (G i) j (Q i) (M i) ho q e (wholeZ (N i) U) (W i x) (V i)) := by
  let J(i:I):=Forest (ratio (G i)); let P'(a:Σ i,J i):= P a.1; let N'(a:Σ i,J i):= N a.1
  refine Satin.circle (J:=J) ?_
  refine Satin.wool N' L P' (fun a=>s a.1) j D vA ho (fun a=>M a.1) (fun a=> Q a.1) (fun a=> y a.1)
    (fun i x=> middle (G i.1) q e i.2 (W i.1 x) (V i.1)) ?_ U
  intro a
  exact seine_m N' L P' (fun a=>s a.1) (fun a x=>(W a.1 x).2) (r.re (fun (a:Σ i:(Σ i,J i),Edge (Seat (P' i)))=> ⟨a.1.1,a.2⟩)) Sigma.snd a (fun a=> (V a.1).2) q e p u
#print axioms gather
end
end Fiber
section averages
variable {X T:Type*}[MeasurableSpace X]{P:T→Type*}[∀i,NormedAddCommGroup (P i)][∀i,NormedSpace ℝ (P i)]
variable {V:T→Type*}{F':∀i:T,V i→X→P i}(h: Menu (T:=fun i:Σ j,V j=>P i.1) (fun (i:Σ j:T,V j) x=> F' i.1 i.2 x))
include h
lemma menu_integral [∀i,MeasurableSpace (V i)](μ:∀i,Measure (V i))[∀i,IsProbabilityMeasure (μ i)]
    (t:∀ i x,Integrable (fun j=> F' i j x) (μ i)) :
    Menu (T:=P) (fun i x=>∫ v,F' i v x∂μ i):=by
  obtain ⟨D,d,u⟩:=h.budget; refine ⟨?_,D,d,fun i x=>?_⟩; swap
  · exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun y=> u ⟨i,y⟩ x) |>.trans_eq (by simp)
  intro ε e; obtain ⟨D,v,k⟩:=h.deal (ε/2) (by linarith); refine ⟨D,v,fun x y w i=>?_⟩
  rw [dist_eq_norm,← integral_sub (t i x) (t i y)]; apply lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C:=ε/2) ?_) (by simp; linarith)
  exact Eventually.of_forall fun z=> by simpa only [←dist_eq_norm] using (k x y w ⟨i,z⟩).le

lemma menu_convex [∀i,Fintype (V i)] {v:∀i:T,V i→ X→ℝ} (e:∀i j x,0≤ v i j x)(t:∀i x, ∑ j:V i,v i j x=1)
    (g: Chalk.flash (fun (s:Σ i:T,V i) x=>v s.1 s.2 x)) :
    Menu (T:=P) (fun i x=>∑ j:V i, v i j x • F' i j x):=by
  have hm(i:T)(x:X)(a:V i→P i)(d:ℝ)(w:∀v:V i,‖a v‖ ≤ d): ‖∑ j:V i,v i j x • a j‖ ≤ d:=by
    calc
     _ ≤ ∑ j:V i,v i j x*d:= (norm_sum_le ..).trans (sum_le_sum fun j _=>by rw [norm_smul, Real.norm_of_nonneg (e ..)]; exact mul_le_mul_of_nonneg_left (w j) (e ..))
     _ = d:= by rw [←sum_mul,t,one_mul]
  obtain ⟨C,c,u⟩:=h.budget; refine ⟨?_,C,c,fun i x=>hm i x _ _ fun v=> u ⟨i,v⟩ x⟩
  classical
  intro ε H; obtain ⟨Q,g,w⟩:=g; obtain ⟨P,t,p⟩:=h.deal (ε/2) (by linarith)
  refine ⟨(Q:Finset (Set X))∪P,Deck.join Q P g t,fun x y z i=>?_⟩; rw [dist_eq_norm,← Finset.sum_sub_distrib]; have he(j:V i):= (w x y (Deck.grow subset_union_left x y z) ⟨i,j⟩).symm; dsimp only at he; simp_rw [he,← smul_sub]; apply lt_of_le_of_lt (hm i x _ (ε/2) ?_) (by linarith); exact fun j=> by simpa only [←dist_eq_norm] using (show dist _ _< ε/2 from p x y (Deck.grow subset_union_right x y z) ⟨i,j⟩).le
end averages
end YM.CF.Buffered.Afterglow.Hierarchy
