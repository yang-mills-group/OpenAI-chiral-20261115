import YM.CF.BPress.Habitat.Worth
/- visibility and purchase ext. accessor currents at support alone. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Habitat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Upled
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat.Plain
attribute [local instance] opCStarAlgebra
variable {N s:Side}
namespace Plain
variable (S:Support (More N))
structure Along (x y:Plain N): Prop where
 up: Agrees S x.G y.G
 rods: Phase.Sample.AgreeF S x.X y.X
 bits:∀ i:Site N,node i∈S→ x.stars i=y.stars i
 arms:∀ i∈ S,∀ v:Bool, x.lamp v i=y.lamp v i
variable {x y z:Plain N}
namespace Along
@[refl] lemma refl(x:Plain N): Along S x x:= ⟨fun _ _ _=> rfl,fun _ _=>rfl,fun _ _=> rfl,fun _ _ _=>rfl⟩
variable {S}
@[symm] lemma symm(u:Along S x y): Along S y x:=⟨fun i a b=>(u.up i a b).symm,fun i t=>(u.rods i t).symm,fun i t=>(u.bits i t).symm,fun i t v=>(u.arms i t v).symm⟩
@[trans] lemma trans (u:Along S x y)(v:Along S y z): Along S x z:=⟨fun i p t=>(u.up i p t).trans (v.up i p t),fun i t=>(u.rods i t).trans (v.rods i t),fun i t=>(u.bits i t).trans (v.bits i t),fun i t w=>(u.arms i t w).trans (v.arms i t w)⟩
lemma drop (u:Along S x y){T:Support (More N)}(v:T⊆ S): Along T x y := ⟨agrees_mono u.up v, fun i s=> u.rods i (v s),fun i s=>u.bits _ (v s),fun i s=>u.arms i (v s)⟩
lemma move (r:Along S x y)(u:Mach (More N)) : Along S (τ x u) (τ y u):=by
 refine ⟨fun i a b=>?_,fun i h=> congrArg (scaledV (u i)) (r.rods i h),r.bits,fun i h v=>?_⟩; · change u _*x.G i*_ = u _*y.G i* _; rw [r.up i a b]
 suffices h:∀ z:Plain N,lamp (τ z u) v i=Upled.dial (u i) (lamp z v i) by rw [h x,h y,r.arms i ‹i∈S› v]; -- tune duplicate h name
 intro z; cases v<;>rfl
lemma price0 (r:Along S x y): evalC S x y=0:=by
 rw [evalC,invitation.agrees (fun i h=>r.up i (mem_filter.mp h).2.1 (mem_filter.mp h).2.2),turnTick, meetP]; rw [sum_eq_zero (s:=_) (f:=sun x y) (fun i p=>?_ ), sum_eq_zero (fun i p=>?_ )]; · ring
 · rw [r.bits i (mem_filter.mp p).2, FateTick,if_pos rfl]
 unfold sun; rw [r.rods i p, show H0 x i=H0 y i from r.arms i p false,show H1 x i=H1 y i from r.arms i p true]; simp [δFee] -- tune
end Along
variable (x y z)
abbrev nearBits(T:Support (More N)):= univ.filter fun i:Site N=> node i∈T
def mask := (Law.rep (leaks S) x.G (1:Bkg (More N)), Law.rep S x.X (fun _=> Classical.arbitrary Ballot), Law.rep (nearBits S) x.stars (fun _=> false), Law.rep S x.H0 (fun _=> ContinuousMap.const _ (0:Op Slot)), Law.rep S x.H1 (fun _=> ContinuousMap.const _ (0:Op Slot))) -- tune inferred
lemma mask_along : Along S x (mask S x):=by
 refine ⟨fun i p q=> (Law.rep_L _ _ _ i ?_).symm,fun i h=> (Law.rep_L S x.X (fun _=> Classical.arbitrary Ballot) i h).symm, fun i t=>(Law.rep_L (nearBits S) x.stars (fun _=>false) i (mem_filter.mpr ⟨mem_univ _,t⟩)).symm,fun i h v=>?_ ⟩; · exact mem_filter.mpr ⟨mem_univ _,p,q⟩
 have p:= (Law.rep_L S (x.lamp v) (fun _=>ContinuousMap.const _ (0:Op Slot)) i h).symm; cases v <;> exact p
private lemma rp_eq {X I:Type*}[Fintype I]{S:Finset I}(f g:I→X)(h:I→X)(p:Set.EqOn f g S): Law.rep S f h= Law.rep S g h:=by funext i; by_cases s:i∈S; simp [s,p s]; simp [s]
lemma maskEq (p:Along S x y): mask S x=mask S y:= plain_ext _ _ (rp_eq x.G y.G 1 (fun i p' => p.up _ (mem_filter.mp p').2.1 (mem_filter.mp p').2.2)) (rp_eq _ _ _ p.rods) (rp_eq _ _ _ (fun i h=> p.bits i ((mem_filter.mp h).2))) (rp_eq _ _ _ (fun i h=> p.arms i h false)) (rp_eq _ _ _ (fun i h=>p.arms i h true)) -- tune coercions
lemma mask_iff : mask S x=mask S y ↔ Along S x y:=⟨fun e=> (mask_along S x).trans (e.symm ▸ (mask_along S y).symm),maskEq S x y⟩
lemma mask_meas : Measurable (mask S):=by
 letI : OpensMeasurableSpace (Plain N):= @BorelSpace.opensMeasurable _ _ _ (bore_p (N:=N))
 apply tagStar; exact (Law.rep_joint _).comp ((cont_G (N:=N)).measurable.prodMk measurable_const); exact (Law.rep_joint _).comp ((cont_X (N:=N)).measurable.prodMk measurable_const); exact (Law.rep_joint _).comp ((cont_star (N:=N)).measurable.prodMk measurable_const); intro t;  let F0:= (fun x:Plain N=>(mask S x).2.2.2.1); let K(i:Site (More N)):=ContinuousMap.const Track (0:Op Slot); have he: Measurable (fun x:Plain N=>Law.rep S (x.lamp t) K) := (Law.rep_joint S).comp ((cont_lamp (N:=N) t).measurable.prodMk (g:=fun _=>K) measurable_const); cases t <;> exact he
end Plain
end YM.CF.BPress.Habitat
