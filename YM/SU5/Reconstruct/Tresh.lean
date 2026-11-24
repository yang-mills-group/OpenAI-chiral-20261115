import YM.SU5.Reconstruct.Cadence
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis.Regularizing
open Function Set Filter Metric MeasureTheory Measure InnerProductSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy Vacancy.Average Sunbelt Spectral OS Analysis Semigroup Reconstruction
open scoped Topology InnerProductSpace NNReal ENNReal
variable {A : Hilbert}(M : Mesh) {j:Axis}(B: Sunbelt j (marks M) A) (S : OS.Semigroup A j)
local notation "K"=> B.track.aviator B.list
local notation "T"=> B.track.Realm B.list
local notation "P₀"=> (K).orthogonalProjectionOnto
local notation "Ψ"=> B.plane
variable (h : B.heat = S.E) (q : ∀ i, ∀ (v:marks M)(t:ℝ≥0), ((B.track.crew i).play v).comp (S.E t)=(S.E t).comp ((B.track.crew i).play v))
local notation "G★"=>regionT M B S q
noncomputable def ort (X:A.Op): (B.track.Realm B.list).Op:= (P₀).comp (X.comp (K).subtypeL)
local notation "N₀"=>ort M B
section
variable {P D:Type} [Fintype P] [DecidableEq P]
omit [Fintype P][DecidableEq P] in
lemma relies {U:Type}[AddGroup U](a b:P→U)(d r:P→U)(X:P→A.Op)(S:U→A.Op)(x:A)(t:List P)(e:∀ i∈t,d i=r i): ∀ v:U, parkFilm a b d X S x t v= parkFilm a b r X S x t v:=by
 induction t with
 | nil=>exact fun _=>rfl
 | cons i t ih=>intro v; rw [film_step,film_step,e i List.mem_cons_self,ih (fun _ h=>e _ (List.mem_cons_of_mem _ h))]
local notation "V₀"=> SceneGrid M
local notation "R₀"=> Axis → ℝ
local notation "Ω"=> plain M
variable (x:B.track.aviator B.list) -- F undefined replace
-- thick inserts X from the **full** system, define continuous relay by compressing
variable (a b:P→ SceneGrid M)(X:P→A.Op)
variable (z:P→Axis→ℝ)(e:Axis→ℝ)(t:List P)
noncomputable abbrev Dress (P:Type)(n:FrameRef):=P→ SceneCut M n
abbrev plotted (M:Mesh){P:Type} (n:FrameRef)(d:P→SceneGrid M)(u:P→SceneCut M n): P→SceneGrid M:=fun i=> d i + pellet M n (u i)
local notation "Π" n:max=> Dress M P n
local notation "Φ" z:max=> parkFilm a b z X Ψ (x.val:A)
local notation "Ω̂" z:max=> parkFilm (Ω ∘ a) (Ω ∘ b) z ((N₀) ∘ X) (moor (G★)) (x : T) -- Ω composition AddMonoidHom coerces

-- average occurs at ABSOLUTE positions, no cross-axis commutation trick needed
include h
lemma apertureFilm (p:t.Nodup)
    (L:Filter D)(f:D→FrameRef)(c:Tendsto f L zoom)
    (g:D→SceneGrid M)(r:D→P→SceneGrid M)(v:∀l:P,Tendsto (fun d => plain M (r d l)) L (𝓝 (z l)))
    (d:Tendsto (fun i=> plain M (g i)) L (𝓝 e)) :
    Tendsto (fun i=> Average.center (fun w:Dress M P (f i)=> ((Φ (plotted M (f i) (r i) w)) t (g i)))) L
      (𝓝 ((((Ω̂ z) t e:K):K).val:A)) := by
    induction t generalizing D e with
    | nil =>
       have h(i:D): Average.center (fun w:Dress M P (f i)=> (Φ (plotted M (f i) (r i) w)) [] (g i))=x.val:= Average.constant (A:=Dress M P (f i)) x.val
       simp_rw [h]; exact tendsto_const_nhds
    | cons i t ih=>
       obtain ⟨p,w⟩:= List.nodup_cons.mp p
       let U:= fun n:D=>SceneCut M (f n); let W(n:D)(y:U n) := r n i + pellet M (f n) y
       let J:= Σ n:D, U n; let L':= uniform L U
       let s'(u:J):= a i+b i+ W u.1 u.2 -- used at suffix
       let V(n:D):= fun u:P→ U n=> plotted M (f n) (r n) u
       let I'(u:J):A:= Average.center (fun p=> parkFilm a b (V u.1 p) X Ψ (x.val:A) t (s' u))
       have he(n:D): Average.center (fun y:Dress M P (f n)=> ((Φ (plotted M (f n) (r n) y)) (i::t) (g n)))= Average.center (fun u:U n=> Ψ (a i + W n u-g n) (X i (I' ⟨n,u⟩))):=by
          rw [splice i]; apply Average.eq_of; intro u
          unfold I'; rw [← Average.natural,← Average.natural]; apply Average.eq_of; intro z
          rw [film_step]
          have h' : plotted M (f n) (r n) (Function.update z i u) i=W n u:=by simp only [plotted,W,Function.update_self]
          rw [h']; exact congrArg (fun y:A=> Ψ _ (X i y)) (relies a b (plotted M (f n) (r n) (Function.update z i u)) (plotted M (f n) (r n) z) X _ _ _ (fun j h=> by rw [plotted,Function.update_of_ne (show j≠ i from fun q=>p (q ▸ h))]) _)
       -- buy suffix in this actual parameter D, with arbitrary previous query shift
       let y₀ := plain M (a i)+plain M (b i)+z i
       let m:=plain M (a i)+z i-e
       let x':T:= (Ω̂ z) t y₀
       have hv : Tendsto (fun i:J=> plain M (s' i)) L' (𝓝 y₀) := by
         have hw:= pellet_moves M L' (fun i:J=> f i.1) (c.comp (at_uniform L)) (fun i:J=>i.2)
         have H':Tendsto (fun i':J=> plain M (W i'.1 i'.2)) L' (𝓝 (z i)):=by unfold W; simp_rw [map_add]; rw [← add_zero (z i)]; exact ((v i).comp (at_uniform L)).add hw -- tune
         unfold s'; simp_rw [map_add]; exact tendsto_const_nhds.add H'
       have hy:Tendsto I' L' (𝓝 x'.val):= ih y₀ w L' (fun u:J=> f u.1) (c.comp (at_uniform L)) s' (fun x:J=> r x.1) (fun x=> (v x).comp (at_uniform L)) hv
       let Y:= X i x'.val; let d₀(n:D):=a i+ r n i-g n
       have hp : Tendsto (fun n=> Average.center (fun u: U n=> Ψ (a i+ W n u-g n) Y)) L (𝓝 ((moor (G★) m (P₀ Y):K).val : A)) := by
          have he(n:D)(u:U n) : a i+ W n u-g n=d₀ n + pellet M (f n) u:=by unfold W d₀; abel
          simp_rw [he]; exact across_pad M B S h q L f c d₀ m (by unfold d₀; simp_rw [map_sub,map_add]; exact (tendsto_const_nhds.add (v i)).sub d) Y
       simp_rw [he]; change Tendsto _ _ (𝓝 ((moor (G★) m ((P₀) Y):K).val : A)); apply tendsto_of_tendsto_of_dist hp
       apply avg_price L (A:=U) (F:=fun u:J=>Ψ (a i+ W u.1 u.2-g u.1) Y) (G:=fun u:J=> Ψ (a i+W u.1 u.2-g u.1) (X i (I' u))) -- clash notation G
       have he : Tendsto (fun u:J=>dist Y (X i (I' u))) L' (𝓝 0):=by
          let f(u:J):= X i (I' u)
          have hz:Tendsto f L' (𝓝 Y):= ((X i).continuous.tendsto _).comp hy
          have hx:Tendsto (fun u:J=>dist Y (f u)) L' (𝓝 (dist Y Y)) := tendsto_const_nhds.dist hz
          simpa only [dist_self] using hx
       refine squeeze_zero' (Eventually.of_forall fun _=> dist_nonneg) ?_ he
       refine Eventually.of_forall fun i=>?_
       rw [dist_eq_norm,dist_eq_norm,←map_sub]; exact plane_cost M B S h _ _
end
end YM.SelectionAnalysis.Regularizing
