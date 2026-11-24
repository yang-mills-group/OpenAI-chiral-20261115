import YM.CF.Flare.Pyre
set_option autoImplicit false
noncomputable section
namespace YM.CF.Flare
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
lemma snow(u:Ket n)(x:Wave n): let P:=acts (create u) x; let W:=acts (remove u) x; ‖P‖^2+‖W‖^2=‖u‖^2*‖x‖^2:=by
 intro P W
 rw [← inner_self_eq_norm_sq (𝕜:=ℂ),← inner_self_eq_norm_sq (𝕜:=ℂ)]; let U:= create u; let V:=remove u; rw [← map_add]; -- tune
 rw [show inner ℂ P P=inner ℂ x (acts (V*U) x) by rw [act_mul,←act_inner V x (acts U x)]; unfold P; rw [show star V=U from star_star _], show inner ℂ W W=inner ℂ x (acts (U*V) x) by rw [act_mul, ←act_inner U x (acts V x)], ←inner_add_right, ←act_add, car,act_smul,act_one,inner_smul_right]; -- tune
 simp [inner_self_eq_norm_sq_to_K ,← Complex.ofReal_pow]
lemma cost_pe(b:Bool)(u:Ket n):‖creed b u‖≤‖u‖:=by
 suffices p: ‖create u‖≤‖u‖ by cases b; exact p; exact (norm_star _).trans_le p
 rw [←Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro i; have hp:= snow u i; apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg i))).1; rw [mul_pow]; exact (le_of_le_of_eq (le_add_of_nonneg_right (sq_nonneg _)) hp)
variable {P Q K T D:Op n}(h:Clad P Q T D K)
abbrev Reader0(n:Type*)[LinearOrder n][Fintype n]:= Bool × Ket n
def ton(v:Reader0 n):= creed v.1 v.2
def iceT(L:Op n)(x:Reader0 n): FC n := creed x.1 (acts (if x.1 then 1+star L else 1-L) x.2)
include h
lemma ivory (p:Wave n)(u:Sea Q p): ∀ x:Wave n, inner ℂ p (acts (quant (1+laneP Q T K)) x)= inner ℂ p x:=by
 let L:=laneP Q T K
 have hp :acts (quant Q) p=p:=by nth_rw 1 [←u.1]; rw [←act_mul,line_quant h.helm,u.1]
 have hv: star L*Q=0:=by nth_rw 1 [← h.helm.isSelfAdjoint]; rw [←star_mul,h.bare,star_zero]
 intro x; rw [←act_inner, ←quant_star,star_add,star_one, show star (laneP Q T K)=_ from rfl]
 rw [show acts (quant (1+star L)) p=p by nth_rw 1 [←hp]; rw [←act_mul, ←quant_mul,add_mul,hv,add_zero,one_mul,hp]] -- tune stars
lemma mixC (v:Reader0 n): ton v * quant (1+laneP Q T K)=quant (1+laneP Q T K)*iceT (laneP Q T K) v:=by
 let L:=laneP Q T K
 obtain ⟨b,x⟩:=v; cases b
 · change create x*_ = quant (1+L)* create (acts (1-L) x); rw [quant_create, ←act_mul,h.flick,act_one]
 change remove x*quant (1+L)=_ * remove (acts (1+star L) x); rw [quant_ann,star_add,star_one]
lemma read0 (p q:Wave n)(v:Sea P p)(u:Sea Q q)(L:List (Reader0 n)):
 inner ℂ q (acts (rollC ton L * quant T) p)=skyGlow q T p * inner ℂ q (acts (rollC (iceT (laneP Q T K)) L) q) :=by
 let B:=quant (1+laneP Q T K); let f:=skyGlow q T p; have hp:acts (quant T) p=f • acts B q:= by rw [broomstick h p q v u,tallied _ h.reef]
 have he:rollC ton L * B=B* rollC (iceT (laneP Q T K)) L:=by
    induction L with
    | nil=> simp [rollC]
    | cons i L ih=>rw [rollC,List.map_cons,List.prod_cons, mul_assoc]; change ton i*(rollC ton L*B) = B*(iceT _ i * rollC _ L); rw [ih,←mul_assoc,mixC h,mul_assoc] -- tune
 rw [act_mul,hp,map_smul,inner_smul_right,←act_mul,he,act_mul,ivory h q u]
def unitsC(n:Type*)[LinearOrder n][Fintype n](w:List (Reader0 n)):ℝ:= (w.map fun i=>‖i.2‖).prod
variable [Nonempty n]{a:ℝ}
omit h
lemma opy (B:Op n)(k:Ket n): ‖acts B k‖≤ ‖B‖*‖k‖:=by nth_rw 1 [← Matrix.l2_opNorm_toEuclideanCLM B]; exact (acts B).le_opNorm _ -- nth
lemma mobA (L:Op n)(e: ‖L‖+1≤a)(q:List (Reader0 n)): ‖rollC (iceT L) q‖≤ unitsC n q * a^q.length :=by
 have hu:1≤a:=(le_add_of_nonneg_left (norm_nonneg L)).trans e
 induction q with
 | nil=> simp [rollC,unitsC]
 | cons i q H=>
   have ht: ‖iceT L i‖≤ a*‖i.2‖:=by
     unfold iceT; apply (cost_pe ..).trans; refine (opy ..).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)); cases h:i.1
     · refine (norm_sub_le ..).trans ?_; rw [norm_one,add_comm]; exact e
     refine (norm_add_le ..).trans ?_; rw [norm_one,norm_star,add_comm]; exact e
   rw [rollC,List.map_cons,List.prod_cons]; refine (norm_mul_le ..).trans ((mul_le_mul ht H (norm_nonneg _) ((norm_nonneg _).trans ht)).trans_eq ?_); simp only [unitsC,List.map_cons,List.prod_cons,List.length_cons,pow_succ]; ring
include h
lemma motto (p q:Wave n)(v:Sea P p)(u:Sea Q q)(L:List (Reader0 n))(e: ‖laneP Q T K‖+1 ≤ a): ‖inner ℂ q (acts (rollC ton L * quant T) p)‖ ≤ ‖skyGlow q T p‖*(unitsC n L*a^L.length):=by
 rw [read0 h p q v u L,norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); let R : FC n:=rollC (iceT (laneP Q T K)) L; have hQ:‖(acts R) q‖ ≤ ‖R‖*‖q‖:=by apply le_trans ((acts R).le_opNorm q); rw [show ‖acts R‖=‖R‖ from Matrix.l2_opNorm_toEuclideanCLM R]
 have hP:= norm_inner_le_norm (𝕜:=ℂ) q ((acts R) q); rw [u.2,one_mul] at hP; rw [u.2,mul_one] at hQ; exact hP.trans (hQ.trans (mobA _ e L))
end YM.CF.Flare
