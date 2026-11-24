import Ridgetop.Mgf
set_option autoImplicit false
noncomputable section
namespace Factory
open Function MeasureTheory ProbabilityTheory Real Filter InnerProductSpace
open scoped Topology ENNReal NNReal RealInnerProductSpace BigOperators Classical
variable {E:Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "μ*"=>stdGaussian E
variable (L M:StrongDual ℝ E)
-- factor integrability helper though could avoid via polarization
lemma squares_d(n:ℕ):MemLp (fun i=> L i^n) 2 μ*:=by
 apply memLp_two_iff_integrable_sq (L.continuous.pow n|>.aestronglyMeasurable)|>.mpr; change Integrable (fun i=> (L i ^ n)^ (2:ℕ)) _; simp_rw [← pow_mul]; exact pow_int L _
lemma price_powers(i j:ℕ):Integrable (fun t=>L t^i * M t^j) μ*:= by
 change Integrable ((fun t=>L t^i)*(fun t=>M t^j)) μ*
 exact (squares_d L _).integrable_mul (squares_d M _)
abbrev webV(u:E):=InnerProductSpace.toDual ℝ E u
lemma wick(u v:E): (∫ t,(webV u) t^2 * (webV v) t^2 ∂μ*) = ‖u‖^2*‖v‖^2+2*⟪u,v⟫^2:=by
 let a:=webV u; let b:=webV v; let p:=webV (u+v); let m:=webV (u-v)
 have h(t:E): p t^4 + m t^4=(2*(a t)^4 + 12*(a t^2*b t^2)) + 2*(b t)^4:=by
    change ((toDual ℝ E) (u+v) _ )^4 + ((toDual ℝ E) (u-v) _)^4 = _; rw [map_add,map_sub]; change (a t+b t)^4+(a t-b t)^4=_; ring
 let l:=∫ t:E,p t^4 + m t^4∂ μ*
 have hr:l=2*(3*‖u‖^4) + 12*(∫ t,a t^2*b t^2∂ μ*) + 2*(3*‖v‖^4):=by
    unfold l; simp_rw [h]; erw [integral_add (((pow_int a 4).const_mul 2).add ((price_powers a b 2 2).const_mul 12)) ((pow_int b 4).const_mul 2),integral_add ((pow_int a 4).const_mul 2) ((price_powers a b 2 2).const_mul 12), integral_const_mul,integral_const_mul,integral_const_mul,tetra,tetra]; simp only [a,b,webV,LinearIsometryEquiv.norm_map]
 have hl:l= 3*‖u+v‖^4+3*‖u-v‖^4:=by unfold l; rw [integral_add (pow_int p _) (pow_int m _),tetra,tetra]; simp only [p,m,webV,LinearIsometryEquiv.norm_map]
 rw [hl,show (4:ℕ)=2*2 from rfl] at hr; simp_rw [pow_mul] at hr; rw [norm_add_sq_real,norm_sub_sq_real] at hr
 change (∫ t,a t^2*b t^2∂ μ*) = _
 nlinarith only [hr]
lemma pair_u(u v:E): (∫ t,(webV u) t * (webV v) t∂μ*) =⟪u,v⟫:=by
 let a:=webV u; let b:=webV v; let p:=webV (u+v)
 have hu: Integrable (fun t=>a t*b t) μ*:=by simpa using price_powers a b 1 1
 have H(t:E): p t^2 = a t^2 + 2*(a t*b t)+b t^2:=by change ((toDual ℝ E) (u+v) _ )^2 = _; rw [map_add]; change (a t+b t)^2=_; ring
 let l:=∫ t:E,p t ^2 ∂ μ*
 have hr:l=‖u‖^2+2*(∫ t,a t*b t∂ μ*) + ‖v‖^2:=by unfold l; simp_rw [H]; erw [integral_add ((pow_int a 2).add (hu.const_mul 2)) (pow_int b 2),integral_add (pow_int a 2) (hu.const_mul 2), integral_const_mul,twice,twice]; simp only [a,b,webV,LinearIsometryEquiv.norm_map]
 have hl:l= ‖u+v‖^2:=by unfold l; rw [twice]; apply congrArg (fun z:ℝ=>z^2); exact (toDual ℝ E).norm_map _
 rw [hl,norm_add_sq_real] at hr; change (∫ t,a t*b t∂ μ*) = _; linarith only [hr]
#print axioms pair_u
end Factory
