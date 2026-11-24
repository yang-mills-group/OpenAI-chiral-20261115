import YM.CF.Floe.Bay
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 16000
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable{N:Side}{a b:ℝ}
def win (M:Bool→H0)(p:Bool):H0:=star (M (!p))
def echoL(x:BayP N):BayP N:=(fun i=>win (x.1 i),fun b c=>win (x.2 b c))
lemma ew (X Y:Bool→H0) (b:Bool): ‖win X b-win Y b‖=‖X (!b)-Y (!b)‖:=by unfold win; rw [←star_sub,norm_star]
lemma eh(X Y:Bool→H0):‖win X-win Y‖=‖X-Y‖:=by
 apply le_antisymm <;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr ?_
 · exact fun b=>(ew X Y b).trans_le (norm_le_pi_norm (X-Y) _)
 intro b; have ht:= norm_le_pi_norm (win X-win Y) (!b); simp_rw [Pi.sub_apply,ew,Bool.not_not] at ht; exact ht
lemma wore (x y:BayP N):‖echoL x-echoL y‖=‖x-y‖:=by
 rw [Prod.norm_def,Prod.norm_def]; refine congrArg₂ max ?_ ?_
 · exact pne fun i=> eh _ _
 exact pne fun b=> pne fun l=>eh _ _
lemma en(u: Tenant.Input N):echoL (skin u)=skin u:=by
 have he(x:H0): win (vow x)=vow x:=funext fun b=>by cases b<;>simp [win,vow]
 unfold echoL skin; simp_rw [he] -- tune dsimp
lemma carp {x:BayP N}(h:x∈Kelp N a):echoL x∈ Kelp N a :=by
 obtain ⟨Z,X⟩:=kelp_m.mp h; refine kelp_m.mpr ⟨Z,?_⟩; rwa [←en,wore]
local notation "Lb"=> Kelp N a
def eθ(x:Kelp N a):Kelp N a:=⟨echoL x.val,carp x.property⟩
lemma ele_e(g:Geometry N)(x:Kelp N a): eθ (ku.drive g x)=ku.drive g (eθ x):=by
 apply Subtype.ext; change echoL _=carryP _ _; have hx(U V:UnitS)(p:Bool→H0): win (γL U V p)= γL U V (win p):= funext fun b=>by cases b <;> simp [γL,win,mul_assoc]
 apply Prod.ext (funext fun i=> hx ..) (funext fun i=>funext fun j=> hx ..)
lemma ema(S:Seal (Site (More N)))(x y:Kelp N a): ku.eval S (eθ x) (eθ y)=ku.eval S x y:=by dsimp only [ku,eθ,echoL]; simp_rw [eh]
lemma est : Isometry (echoL (N:=N)):=Isometry.of_dist_eq fun x y=>by rw [dist_eq_norm,dist_eq_norm,wore]
lemma eθ_o : Continuous (eθ (N:=N) (a:=a)):= Continuous.subtype_mk (est.continuous.comp continuous_subtype_val) _
open MeasureTheory
private lemma ps_win {p:ℂ→ Bool→H0}{i:ℂ}(g:DifferentiableAt ℂ p (star i)): DifferentiableAt ℂ (fun z=> win (p (star z))) i:=by
 refine differentiableAt_pi.mpr fun j=> ?_; exact (differentiableAt_star_conj_iff (f:=fun z=>p z (!j))).mpr (differentiableAt_pi.mp g (!j))
private lemma ps_La{p:ℂ→Ra N H0}{i:ℂ}(g:DifferentiableAt ℂ p (star i)):DifferentiableAt ℂ (fun z:ℂ=>fun j:Edges (More N)=>win (p (star z) j)) i:=differentiableAt_pi.mpr fun j=> ps_win (p:=fun z=>p z j) (differentiableAt_pi.mp g j)
private lemma μLb{p:ℂ→Site N→Bool→H0}{i:ℂ}(g:DifferentiableAt ℂ p (star i)): DifferentiableAt ℂ (fun z:ℂ=>fun a=>win (p (star z) a)) i:= differentiableAt_pi.mpr fun k=> ps_win (p:=fun z=>p z k) (differentiableAt_pi.mp g k)
private lemma ps_Lb{p:ℂ→Rb N H0}{i:ℂ}(g:DifferentiableAt ℂ p (star i)):DifferentiableAt ℂ (fun z:ℂ=>fun (a:Bool) (j:Site N)=>win (p (star z) a j)) i:=by
 let P (x):= p x; have h:DifferentiableAt ℂ (fun z:ℂ=>(p z: Bool → Site N→ Bool→ H0)) (star i):= g; refine (differentiableAt_pi (F':=fun _ : Bool=> (Site N → Bool → H0))).mpr ?_; exact fun j=> μLb (N:=N) (p:=fun z=> p z j) (((differentiableAt_pi (F':=fun _:Bool=> (Site N → Bool → H0))).mp h) j)
private lemma pst {i:ℂ}{p:ℂ→ BayP N}(g:DifferentiableAt ℂ p (star i)): DifferentiableAt ℂ (fun j=> echoL (p (star j))) i:= (ps_La (p:=fun x=>(p x).1) g.fst).prodMk (ps_Lb (p:=fun x=>(p x).2) g.snd)
lemma echo_valid(f:Lb→ℂ)(h:Looks Lb f): Looks Lb fun x=>star (f (eθ x)):=by
 apply realigns h; intro V v γ e; intro i p; let T(x):= (γ x).val; have ht:DifferentiableAt ℂ T (star i):=e.differentiableAt (v.mem_nhds p); exact (pst ht).differentiableWithinAt
end YM.CF.Floe
