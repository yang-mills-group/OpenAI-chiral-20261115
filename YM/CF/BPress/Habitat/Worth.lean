import YM.CF.BPress.Habitat.Loom
/- all Pose. -/
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Habitat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Upled
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat.Plain
attribute [local instance] opCStarAlgebra
variable {N s:Side}{D:Type}[MeasurableSpace D]
namespace Plain
variable (x y:Plain N) (u v:Mach (More N))
def rotateQ (u:Mach s)(g:Lamp s): Lamp s:=fun x=> Upled.dial (u x) (g x)
def τ := (gauge u x.G,feast u x.X, x.stars,rotateQ u x.H0, rotateQ u x.H1)
private lemma brt (f: Lamp (More N)): rotateQ v (rotateQ u f)=rotateQ (v*u) f :=by
 apply funext; intro i; unfold rotateQ; change Upled.dial (v i) (Upled.dial (u i) (f i))=_; rw [dial_seq]; rfl
lemma τ_ρ : ∀ v : Mach (More N), τ (τ x u) v=τ x (v*u):=by
 intro v; have he (X:Bkg (More N)): gauge v (gauge u X)= gauge (v*u) X:=by ext1 i; simp only [Lattice.gauge,Pi.mul_apply,mul_inv_rev]; simp only [mul_assoc]
 have h(g:Lamp (More N)): rotateQ v (rotateQ u g)=rotateQ (v*u) g:=brt u v g
 unfold τ; simp only [G,X,stars,H0,H1]; rw [he]; simp_rw [h]; rw [show feast v (feast u _)=feast (v*u) x.X from shuffle_seq v u x.X] -- tune abbrev
lemma τ_one: τ x 1=x:=by unfold τ; rw [show gauge (1:Mach _) x.G=x.G from (by ext1 i; simp [Lattice.gauge]),show feast 1 _=x.X from shuffle_one _]; simp_rw [show ∀ f:Lamp (More N),rotateQ 1 f=f from fun f=> funext (fun i=> dial_one _)]
private lemma rot_rule {X Y Z J : Type*}[TopologicalSpace X][TopologicalSpace Y][TopologicalSpace Z](g:X ×Y→Z)(p:Continuous g): Continuous (fun x:(J→X)×(J→Y)=>(fun i:J=>g (x.1 i,x.2 i))):= continuous_pi fun i=> p.comp (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))
private lemma rot_c : Continuous (fun x:Mach s × Lamp s=>rotateQ x.1 x.2) :=by
 let f(x:Mach s × Lamp s)(i:Site s):= Upled.dial (x.1 i) (x.2 i)
 exact rot_rule _ dial_c
private lemma cont_H1 : Continuous (H1 (N:=N)):= continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
private lemma cont_H0 : Continuous (H0 (N:=N)):= continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
private lemma rp_cont {X:Type*}[TopologicalSpace X] (x:X→Mach s)(M:X→Lamp s)(p:Continuous fun i:X=> (x i,M i)) : Continuous fun i=> rotateQ (x i) (M i):= by
 let F(X:Mach s × Lamp s):= rotateQ X.1 X.2
 change Continuous (F ∘ fun i=>(x i,M i))
 exact rot_c.comp p
lemma ambiance : Continuous (fun x: Mach (More N) × Plain N=> τ x.2 x.1):=by
 refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ((cont_star (N:=N)|>.comp continuous_snd).prodMk (Continuous.prodMk ?_ ?_)))
 pick_goal 4; · apply rp_cont (s:=More N) Prod.fst (fun x=>H1 x.2) (Continuous.prodMk continuous_fst ((cont_H1 (N:=N)).comp continuous_snd))
 pick_goal 3; · apply rp_cont (s:=More N) Prod.fst (fun x=>H0 x.2) (Continuous.prodMk continuous_fst ((cont_H0 (N:=N)).comp continuous_snd))
 · apply continuous_pi; intro i; exact ((((continuous_apply i.1).comp continuous_fst).mul ((continuous_apply i).comp (cont_G.comp continuous_snd))).mul (((continuous_apply (i.1+step i.2)).comp continuous_fst).inv)) -- tune
 have ht : Continuous (fun x:Mach (More N) × Stun N=> feast x.1 x.2):= rot_rule _ scaled_cont; let X(x:Mach (More N) × Plain N):=(x.1,Plain.X x.2); change Continuous ((fun x: Mach (More N) × Stun N=> feast x.1 x.2) ∘ X); exact ht.comp (continuous_fst.prodMk (cont_X.comp continuous_snd))
variable (S:Support (More N))
lemma τ_canon : evalC S (τ x u) (τ y u)=evalC S x y:=by
 rw [evalC,evalC,show invitation S ((τ x u).1) ((τ y u).1)= invitation S x.G y.G from invitation.iso _ _ u,show turnTick S (τ x u) (τ y u)=turnTick S x y from rfl]; apply congrArg; unfold meetP; apply congrArg (·+ (0:ℝ)); apply sum_congr rfl; intro i _; unfold sun; rw [show dist (Plain.X (τ x u) i) (Plain.X (τ y u) i)= dist (x.X i) (y.X i) from scaled_d (u i) _ _, show δFee (H0 (τ x u) i) (H0 (τ y u) i)= δFee (x.H0 i) (y.H0 i) from dialCost (u i) _ _]; rw [show δFee (H1 (τ x u) i) (H1 (τ y u) i)= δFee (x.H1 i) (y.H1 i) from dialCost (u i) _ _]
lemma spin_move (t:Bool)(v:ℝ): spin (τ x u) t v = rotateC u (x.spin t v):= by funext i; cases t<;>rfl
-- prove given and Meas. Later. visibility.
@[ext] lemma plain_ext (p:x.G=y.G)(g:x.X=y.X) (h:x.stars=y.stars)(l: x.H0=y.H0) (k:x.H1=y.H1): x=y:= Prod.ext p (Prod.ext g (Prod.ext h (Prod.ext l k)))
lemma tagStar {B:Type*}[MeasurableSpace B](F:B→ Plain N)(h:Measurable fun x=>(F x).G)(p:Measurable fun x=>(F x).X)(q:Measurable fun x=>(F x).stars)(s:∀ t:Bool, Measurable fun x=>(F x).lamp t) : Measurable F:=h.prodMk (p.prodMk (q.prodMk ((s false).prodMk (s true)))) -- eta?
end Plain
end YM.CF.BPress.Habitat
