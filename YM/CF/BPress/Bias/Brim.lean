import YM.CF.BPress.Bias.Summit
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Laurent Bloch Next.Free Fir Lat Spin Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Spin.Stride Dial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N: Side} {j:ℕ} {M:Jill.Male}
-- taper operator
abbrev LoomOp(f: Per N→ℝ):Op (Single N):=Matrix.diagonal (fun i:Single N=> (f (fog i):ℂ))
lemma loom_cost (f: Per N→ℝ): twist (Tang N) (LoomOp f)= LoomOp f:=by
 rw [twist_C]; unfold Commute SemiconjBy LoomOp; ext ⟨⟨x,b⟩,s⟩ ⟨⟨y,a⟩,t⟩; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; by_cases h:x 0=y 0
 · simp only [fog, penX,h]; ring
 rw [tang_exp]; simp [originM, scalarP,horiz N x y h]
lemma loom_plan (f: Per N→ℝ)(S: Finset (Single N)): Commute (LoomOp f) (cutM S):=by refine neComm S (LoomOp f) (fun i j h=>?_) |>.symm; rw [show i=j by contrapose! h; simp [LoomOp,h]]
variable (t:Finset (Per N))(k:Site N)
lemma loom_Y(f:Per N→ℝ): Commute (LoomOp f) (sectorY k):=by nth_rw 1 [← loom_cost f]; rw [← tangY]; exact (loom_plan f _).map (twist (Tang N))
private lemma H_cost : twist (Tang N) (Hloc N)=Hloc N:=by
 rw [twist_C]; apply neComm; rintro ⟨⟨x,b⟩,t⟩ ⟨⟨y,a⟩,k⟩ f; have he:b=a:=by contrapose! f; rw [tang_exp]; simp [originM,scalarP,f]
 simp only [tenureX,mem_univ,mem_filter,true_and,he]
private lemma cost_p : twist (star (Tang N)) (pos (Lower t))=pos (Lower t):=by rw [←shutter_plus,map_mul]; nth_rw 1 [←show twist (Tang N) (Hloc N)=tenureP N true from H_cost]; nth_rw 1 [← stays t]; rw [twist_inv,twist_inv]; rfl
private lemma boom(f:Per N→ℝ) (A:Op (Single N))(x y: Single N): (LoomOp f*A-A*LoomOp f) x y=(f (fog x)-f (fog y):ℂ)* A x y:=by unfold LoomOp; rw [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]; ring
lemma trigger (f:Per N→ℝ)(u:Per N)(n:ℕ)(p:f u=0)(q:f (u+(n:Per N))=1)(w: u ∉ t)(w': u+(n:Per N)∉ t) (a b:SpinIdx) (K:a∉plusHalf)(v:b∈plusHalf) : ‖Turn (graphX j M) k n a b‖ ≤ ‖LoomOp f*(restoration t j M*sectorY k) -restoration t j M*sectorY k*LoomOp f‖:=by
 let A:=restoration t j M*sectorY k; let U:=star (Tang N); let T:=twist U; let x:=u+(n:Per N); let B:=lens (graphX j M) N; let s:Slot:=Classical.arbitrary Slot; let i: Single N:=((needle k x,a),s); let o:Single N:= ((needle k u,b),s)
 have he: T (sectorY k)=region k:=by rw [←tangY]; exact twist_inv ..; -- canon
 have T_U(X:Op (Single N))(h:twist (Tang N) X=X):T X=X:=by nth_rw 1 [←h]; exact twist_inv ..
 have hp:=T_U _ H_cost; have hh: i∈shutters tᶜ:=by simp only [i,shutters, fog, penX, mem_filter, mem_univ, true_and,needle, update_self]; exact mem_compl.mpr w'
 have hv:o∈regions k:=mem_filter.mpr ⟨mem_univ _,mer_tick ..⟩; have ho:o∉Locks (Lower t) true:=by simp [Locks,o,Lower,needle,w]
 have hs:‖T A i o‖ = ‖Turn (graphX j M) k n a b‖:=by
    unfold A restoration GraphW.road; rw [map_mul,he,map_mul,map_mul,map_add,hp, shutter_empty,T_U _ (stays tᶜ),map_sub,hp,cost_p']; let L:=shutter (tᶜ); rw [region,slabR,if_pos hv,mul_sub,Matrix.sub_apply]
    rw [show Hloc N=cutM (tenureX N true) from rfl, show pos (Lower t)= cutM (Locks (Lower t) true) from rfl, slabR,slabR,if_neg ho,if_pos (show o∈tenureX N true from mem_filter.mpr ⟨mem_univ _,v⟩),sub_zero, shutter, slabL,if_pos hh, Matrix.add_apply,show cutM (tenureX N true) i o=0 from ?_,zero_add]; rw [show T (lens (graphX j M) N) i o= _ from block k _ a b s u n,norm_mul]; have hq:‖pinω u n‖=1:=fee_norm _; rw [hq,one_mul]
    unfold cutM; by_cases h:i=o; · exact False.elim (K ((show a=b from congrArg (fun i:Single N=> i.1.2) h) ▸ v))
    simp [h]
 rw [← hs, ← twist_norm U]; rw [map_sub,map_mul T (LoomOp f) A,map_mul (twist U) (restoration t j M*sectorY k) (LoomOp f),T_U _ (loom_cost f)]; have hk:=norm_entry ((LoomOp f)*(T A)-T A*LoomOp f) i o; rw [boom,show fog i=x by simp [fog,i,penX,needle],show fog o=u by simp [fog,o,penX,needle],q,p] at hk; simp only [Complex.ofReal_zero, Complex.ofReal_one, sub_zero, one_mul] at hk; exact hk
where cost_p': twist (star (Tang N)) (pos (Lower t))=pos (Lower t):= cost_p t
local notation "Aδ"=>nativeX j M N
local notation "Π(" N "," j "," M "," t ")"=>ramp (shutter ((t:Finset (Per N))ᶜ)) (pos (Lower t)) (nativeX j M N) -- unused
open Real
variable {t}
theorem sparkP (j d:ℕ) (h:1≤j) : ∃ η:ℝ, ∃ v:ℕ,0<η ∧ ∀ (M:Jill.Male)(N:Side),v≤N.val→∀ (f:Per N→ℝ)(t:Finset (Per N))(u:Per N)(n:ℕ), n≤d→u∉t→u+(n:Per N)∉t→ f u=0 → f (u+(n:Per N))=1→ ∀ {b:ℝ}, Pass (pos (Lower t)) (Hole.neg (Lower t)) (loose (Lower t)) (nativeX j M N) b → let W:=ramp (loose (Lower t)) (pos (Lower t)) (nativeX j M N); η < ‖W*LoomOp f-LoomOp f*W‖ :=by
 obtain ⟨r,m,u₀,g⟩:=turnsPrice h (d:ℝ) (Nat.cast_nonneg _); obtain ⟨a,p,S⟩:= gain_H j h u₀; let C:= Real.sqrt a⁻¹; have hz:0<C:= Real.sqrt_pos.mpr (inv_pos.mpr p); let c:ℝ:=1/(96*Real.pi)/2; have hc:0<c:=by unfold c; positivity
 let η:= c/(2*(1+C)*C); have he:0<η:=div_pos hc (by positivity); refine ⟨η,m,he,?_⟩; intro M N f0 B t u n w p0 q x x' b P W; obtain ⟨k,r1,i,i',i2,i1,hG⟩:= g M N f0 n (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast w); by_contra! H
 let Y:=sectorY k; let D:=restoration t j M; let R:= context_eq P; let E:= Hloc N+lens (graphX j M) N; let F:=C_base k
 have ht:= C_P k t; have hx:=sector_star k; have hw:Commute Y W:= R.commW hx.isSelfAdjoint ht (by rw [shutter_empty]; exact (going k tᶜ).symm) (goingLens ..)
 have he':= boundR k t P (R.ease F (goingLens ..) (C_E ..) hx p (S M N k r1)); -- order
 let Τ:=LoomOp B; have he₁: c≤ (1+C)*(η*C):=by apply hG.trans ((trigger t k B u n x x' p0 q i i' i1 i2).trans ?_); exact R.alert (F.sub_right ht) (C_D k t j M) hw hx ((loom_plan B _).sub_right (loom_plan B _)) (loom_Y k _) H he'
 rw [show (1+C)*(η*C)=c/2 by unfold η; field_simp] at he₁; linarith only [he₁,hc]
end YM.CF.BPress.Bias
