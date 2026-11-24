import YM.CF.BPress.Bias.Ledger
/- Use actual bar and timing masks. Overall obstruction as norm on full torus independently of seam alignment and mark lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Laurent Bloch Next.Free Fir Lat Spin Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Spin.Stride Dial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side} {j:ℕ} {M:Jill.Male} {p:Site N} {v:ℝ}
def Hloc(N:Side):=tenureP N true
def nativeX(j:ℕ)(M:Jill.Male)(N:Side):= Blank.lens (bent true j M.val) N
lemma nativeEq (h:1≤j): nativeX j M N=spar j M (1:Bkg (Cube.More N)):= (nativeP N true j M h).symm -- tune

local notation "H"=> Hloc N
local notation "A"=> nativeX j M N
local notation "E"=> (H+lens (graphX j M) N) -- explicit for tactic
lemma addL(f g:Momentum→Op SpinIdx) : lens f N + lens g N=lens (fun i=> f i + g i) N:=by rw [← eq_sub_iff_add_eq,l_sub]; congr; funext p; rw [add_sub_cancel_right]
lemma context_eq {S:Support N} (g: Pass (pos S) (Hole.neg S) (loose S) A v): GraphW (pos S) (Hole.neg S) (loose S) A H E v:=by
 let B:=angle true; let f:=bent true j M.val; let A':Momentum → Op SpinIdx:=fun i=> B+graphX j M i; let X:=cutM (cup true); have ht:IsStarProjection B:=by unfold B; rw [lid]; exact cutM_idp _
 have he(p:Momentum):B+graphX j M p=(1-Fir.zen (mixL j M.val p))*B:=by unfold graphX; rw [sub_mul,one_mul,neg_mul,sub_eq_add_neg] -- tune
 have hz(i:Site N): let x:=mel i; f x*A' x=A' x ∧ A' x*f x=f x:=by
    intro x; let a:=base_subset_realCube zone_pos (mel_h i); let Z:=Fir.zen (mixL j M.val x); let k:=shell j M.val x; let U:=A' x; have hx:=aspTrace true j M.val M.property (p:=x) a (mel_away i); change f x=k • ((1-Z)*B*(1+Z)) at hx
    let z:= prodM (mixL j M.val x) (mixL j M.val x); have hp:(1+Z)*(1-Z)=(1+z) • (1:Op SpinIdx):=by rw [add_mul,one_mul,mul_sub,mul_one,show Z*Z=_ from zenSq _]; module
    have hk:k=(1+z)⁻¹:=shell_inv j _ a (mel_away _); have hc:=graphs_ne (phys_mix j M.val M.property _ a.1); have hV: U=(1-Z)*B:= he x; have hu:B*(1-Z)*B=B:=by
       rw [mul_assoc B,sub_mul,one_mul,mul_sub,ht.isIdempotentElem.eq,show Z*B=(1-B)*Z from zenAngle ..,←mul_assoc, Porth ht,zero_mul,sub_zero]
    change f x*U=U∧U*f x=f x; rw [hV,hx]; set X:=1-Z; constructor
    · rw [Matrix.smul_mul,mul_assoc _ (1+Z),←mul_assoc (1+Z),hp, Matrix.smul_mul, Matrix.mul_smul,one_mul,mul_assoc X,ht.isIdempotentElem.eq,hk]; exact inv_smul_smul₀ hc _
    rw [Matrix.mul_smul, ←mul_assoc, ←mul_assoc (X*B)]; have he':X*B*X*B=X*B:=by rw [mul_assoc X B X,mul_assoc X,hu ]
    rw [he'] -- tune
 have locEq (f g:Momentum→Op SpinIdx)(h:∀ i:Site N,f (mel i)=g (mel i)): lens f N=lens g N:=by rw [l_spectral,l_spectral]; unfold mark; exact congrArg _ (congrArg _ (congrArg (jump _) (funext h)))
 have hE:E=lens A' N:=by unfold Hloc; rw [t_lamp,addL]
 refine ⟨g,cutM_idp _, cut_inside _ _ (filter_subset ..),?_,?_,?_,?_ ,?_⟩
 · ext i k; unfold Hloc tenureP Hole.neg Lock; rw [slabL]; unfold cutM; by_cases x:i=k; subst i; all_goals simp [*,Locks,tenureX,cup] <;> tauto -- tune
 · rw [hE,Hloc,t_lamp,l_mul]; unfold A'; apply congrArg (fun (f:Momentum→Op SpinIdx)=> lens f N); ext1 x; change (B+_)*B=_; rw [he,mul_assoc,ht.isIdempotentElem.eq]
 · rw [hE,Hloc,t_lamp,l_mul]; unfold A'; simp_rw [he]; congr; ext1 p; let z:=Fir.zen (mixL j M.val p); change B*((1-z)*B)=B; rw [sub_mul,one_mul,mul_sub,ht.isIdempotentElem.eq,show z*B=(1-B)*z from zenAngle ..,←mul_assoc,Porth ht,zero_mul,sub_zero] -- tune congr
 · rw [hE,nativeX,l_mul]; exact locEq _ _ fun i=>(hz i).1
 rw [hE,nativeX,l_mul]; exact locEq _ _ fun i=>(hz i).2

section slope
-- precise slice support
variable (k: Site N)
def PCube (p: Momentum): Prop := ∀ a:Axis, a≠0 → p a= mel k a
local instance (k:Site N)(p:Momentum): Decidable (PCube k p):= Classical.propDecidable _
def fish : Momentum→ Op SpinIdx:= fun b=> if PCube k b then 1 else 0
lemma catch_at {i:Site N}: mer i=mer k ↔ PCube k (mel i):=by
 constructor; · intro p a h; have he:=congrFun p a; simp only [mer, needle,update_of_ne h] at he; exact congrArg (fun i:Per N=> (Lat.principal i:ℂ)) he
 intro p; ext1 a; by_cases ha:a=0; simp [mer,needle,ha]; have he:= congrArg Complex.re (p _ ha); simp only [mer,needle,update_of_ne ha]; exact prin_inj _ _ he
lemma inLens : sectorY k=lens (fish k) N:=by
 rw [l_spectral]; apply congrArg (twist (Full N)); ext ⟨⟨i,b⟩,v⟩ ⟨⟨j,a⟩,t⟩; by_cases h:i=j<;> by_cases u:b=a<;> by_cases w:v=t<;> by_cases f:PCube k (mel i)<;> simp_all [region, cutM,regions,scalarP,jump_apply,mark,penX, fish,catch_at]

-- $\sqrt d$ purchase. H on plus only, projection symbol price `shell` independent of time.
variable (s:1≤j) {r:ℝ}
omit k in
lemma gain_H (j:ℕ)(s:1≤j)(p:0<r): ∃ a:ℝ,0<a ∧ ∀ M:Jill.Male,∀ N:Side,∀ k: Site N,r≤|pm k axisR|→ a • (Hloc N *sectorY k) ≤ Hloc N *nativeX j M N*Hloc N:=by
 obtain ⟨d,b,B⟩:= glens j s; refine ⟨d*r^2,mul_pos b (pow_pos p _),fun M N k t=>?_⟩; unfold Hloc nativeX; rw [t_lamp,inLens,l_mul,l_mul,l_mul,l_scale]; apply lens_m; intro i; rw [cube_law]; unfold fish; split; next hi =>
   rw [mul_one]; apply smul_le_smul_of_nonneg_right _ (by rw [lid]; exact IsStarProjection.nonneg (cutM_idp _)); refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p.le ?_ _) b.le).trans (B M N i); apply t.trans; have her:pm i axisR=pm k axisR:=congrArg Complex.re (hi axisR (by decide)); rw [← her]; exact norm_le_pi_norm (pm i) axisR
 next hi => rw [mul_zero,smul_zero,lid]; apply smul_nonneg (norm_nonneg _) (IsStarProjection.nonneg (cutM_idp _))

-- mask S concrete temporal layers of vacancy
abbrev Lower(t:Finset (Per N)):=univ.filter fun i:Site N=>i 0∈ t
abbrev chargeSet(t:Finset (Per N)) (u:Bool):=Locks (Lower t) u
lemma shutter_plus (t:Finset (Per N)): tenureP N true * shutter t = pos (Lower t):=by
 ext i j; unfold tenureP shutter; rw [slabL]; unfold Hole.pos Lock; by_cases h:i=j; swap; · simp [cutM,h]
 subst j; simp only [cutM,Matrix.diagonal_apply_eq]; simp only [Locks, Lower, fog, shutters, penX]; grind
lemma shutter_empty (t:Finset (Per N)): loose (Lower t)=shutter (tᶜ):=by
 rw [(plusMinus _).l0]; ext i j; unfold shutter; rw [Matrix.sub_apply,Matrix.add_apply]; unfold Hole.pos Hole.neg; by_cases h:i=j; swap; · rw [Matrix.one_apply_ne h]; simp [Lock,cutM,h]
 subst j; unfold Lock cutM; rw [Matrix.one_apply_eq]; simp only [Matrix.diagonal_apply_eq]; simp only [shutters, fog, penX, Locks, Lower, tenureX, cup]; split_ifs <;> simp_all -- tune

abbrev restoration(t :Finset (Per N))(j:ℕ)(M:Jill.Male):= GraphW.road (loose (Lower t)) (Hloc N + lens (graphX j M) N) (Hloc N) (pos (Lower t))
lemma C_base : Commute (sectorY k) (Hloc N):=by unfold Hloc; rw [t_lamp]; exact goingLens ..
lemma C_E (j M) : Commute (sectorY k) (H+lens (graphX j M) N):=(C_base k).add_right (goingLens ..)
lemma C_P (t:Finset (Per N)) : Commute (sectorY k) (pos (Lower t)):= by rw [←shutter_plus]; exact (C_base k).mul_right (going k t).symm
lemma C_D (t:Finset (Per N)) (j M):Commute (sectorY k) (restoration t j M):= by unfold restoration GraphW.road; rw [shutter_empty]; exact (((going k _).symm).mul_right (C_E k j M)).mul_right ((C_base k).sub_right (C_P k t))
lemma boundR (t:Finset (Per N)) (b:Pass (pos (Lower t)) (Hole.neg (Lower t)) (loose (Lower t)) A v) (h:‖E*sectorY k‖≤r): ‖restoration t j M*sectorY k‖≤ r:=by
 let S:=Lower t; let D:=loose S; let U:=pos S; let f:=context_eq b; let F:= H-U; have ht:= (C_base k).sub_right (C_P k t); change Commute (sectorY k) F at ht
 change ‖D*E*F*_‖≤_; rw [mul_assoc D E F, mul_assoc D, mul_assoc E, ←ht.eq,←mul_assoc E]; exact ( (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (IsStarProjection.norm_le D b.toEmpties.r))).trans (((norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (f.floor.norm_le F))).trans h)
end slope
end YM.CF.BPress.Bias
