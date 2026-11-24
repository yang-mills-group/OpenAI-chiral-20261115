import YM.CF.Hove.Canon
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

-- center coverlet supply zero physical jets. no lattice interpolation assumption
variable (b:Bool)(j:ℕ)(p:4≤j)(L M:Side)(h:Odd L.val)(v:Odd M.val)
def binV(b:Bool):Op SpinIdx:= 1-Fir.angle b
lemma c_phi : chief b j L M 0= (L.val:ℂ) • binV b:=by
 let H:Side:=L*M
 have ht(S:Side):Cminus S 0=(2:ℂ):=by norm_num [Cminus,narrow,rad,kin,pl,sine,mag]; -- tune
 have he(S:Side):Fir.bent b j S 0=binV b:=by cases b <;> simp [binV,Fir.bent,Fir.angle,bar_origin] -- angle ambiguity
 have hv(S:Side): ds S 0=0:=by simp [ds,sine,narrow]; ext; simp [sine] -- tune
 have hh(S:Side): Fir.bloom j S 0=1:=by simp [Fir.bloom,narrow]
 unfold chief; rw [show narrow L 0=0 by simp [narrow], he, mul_assoc (1-_), show Fir.angle b * binV b=0 by unfold binV; rw [mul_sub,mul_one,slabQ,sub_self],mul_zero,ht,hv, zen_zero,hh,hh,mass_origin]; simp only [zero_mul,zero_sub,mul_one,neg_inj]; unfold binV; module
include p h v
lemma arm_u : Fir.arm b j L M 0 0=(Real.sqrt (L.val:ℝ):ℂ) • binV b ∧∀ i:Site L,i≠0→Fir.arm b j L M i 0 =0:=by
 refine ⟨?_,fun i hi=>by unfold Fir.arm; rw [alias_muff _ (by omega) _ _ h hi, zero_smul,smul_zero]⟩
 unfold Fir.arm; rw [c_phi, if_pos rfl,alias_zero_eq,show narrow L 0=0 from (by simp [narrow]), muff_zero, one_smul,smul_smul]; congr 1; push_cast
 have ht:0 < Real.sqrt (L.val:ℝ):=Real.sqrt_pos.mpr (side_pos _); have hx : (Real.sqrt (L.val:ℝ):ℂ)≠0:=by exact_mod_cast ht.ne'
 field_simp; exact_mod_cast (Real.sq_sqrt (side_pos L).le).symm -- tune
local notation "o"=> (0: Site L)
local notation "I"=>Complex.I
abbrev palmV(V:ℝ):ℂ:=((Real.sqrt (L.val:ℝ):ℂ)) -- drop
local notation "A"=> Fir.paint b j L M o
lemma aim_o : A [] 0= (lace 0 L:ℂ) • binV b∧∀ a:Axis,A [a] 0=0:=by
 let J:=arm_u b j p L M h v; have he(D):A D 0=(listChip 0 D*toll L 2) • Fir.arm b j L M 0 0:=by
    unfold Fir.paint; rw [sum_eq_single o]; swap; · intro i _ p; simp only [J.2 i p,smul_zero]
    simp only [alias_zero_eq,show narrow L 0=0 from (by simp [narrow]), Laurent.mode_constant,one_smul]; simp
 refine ⟨?_, fun a=>by rw [he]; simp [listChip]⟩
 rw [he,J.1,smul_smul]; congr 1; unfold lace listChip toll; simp; ring -- tune
section diff
variable (i:Site L)(hx:i≠0)(a:Axis)
omit b j p L M h v in
private lemma glow_T {U:Type*}{F:U→Momentum→ℂ}{w:U→ℝ}(h:Moderate w F)(a:Axis)(i:U): DifferentiableAt ℝ (fun x:ℝ=>F i (bout a x)) 0:=by
 obtain ⟨t,C,e,D,h'⟩:=h; have he:DifferentiableAt ℂ (F i) (bout a 0):=(h' i).1 _ (by rw [bout_zero]; exact cube_zero _ e)
 apply (he.restrictScalars ℝ).comp _; unfold bout; fun_prop
include hx
lemma arm_P {r s:SpinIdx}:HasDerivAt (fun x=>Fir.arm b j L M i (bout a x) r s) 0 0:=by
 obtain ⟨n, hn⟩:=Nat.exists_eq_add_of_le (show 2 ≤ j by omega)
 let F(x:ℝ):= aliasAt (bout a x) i; let f(x:ℝ):= muff 1 L (F x)
 have he(x): muff j L (F x) = f x * (f x * muff n L (F x)):= by unfold f muff; rw [hn,pow_add]; simp only [pow_two,pow_one,mul_assoc] -- tune
 have h0:f 0=0:=by unfold f F; rw [bout_zero,alias_muff 1 (by decide) L i h hx]
 have ht: DifferentiableAt ℝ f 0:=glow_T (muff_pay 1 (fun _=>L) (fun _=>h) (fun _=>i)) a ()
 let g(x):= muff n L (F x); have hz:DifferentiableAt ℝ g 0:=glow_T (muff_pay n (fun _=>L) (fun _=>h) (fun _=>i)) a ()
 let W(x):ℂ:= Fir.ray b j L M (bout a x) i r s; have hp:DifferentiableAt ℝ W 0:=glow_T ((rosePay b j (by omega) (fun _ : Unit=>L) (fun _=>M) (fun _=>h) (fun _=>v) (fun _=>i) (fun _=>hx)).tap _ _) a ()
 unfold Fir.arm; simp_rw [if_neg hx,Matrix.smul_apply,smul_eq_mul]; change HasDerivAt (fun x=> _ * (muff j L (F x)* W x)) _ _; simp_rw [he]; have hu:= ((ht.hasDerivAt.mul (ht.hasDerivAt.mul hz.hasDerivAt)).mul hp.hasDerivAt).const_mul (((Real.sqrt (L.val:ℝ))⁻¹:ℝ):ℂ); exact hu.congr_deriv (by rw [h0]; simp [h0])
end diff
def snub(a s:Axis): Pal:= (if a=s then 1 else 0:ℂ) • baseF b
variable (x y:Axis)
lemma dusk_i : HasDerivAt (fun s=>A [x] (bout y s)) ((if x=y then Complex.I else 0:ℂ) • (lace 1 L:ℂ) • binV b) 0:=by
 apply op_deriv.mpr; intro r s
 let F (i:Site L) (t:ℝ):= aliasAt (bout y t) i; let G(i:Site L)(t:ℝ):ℂ:= listChip (F i t) [x]*toll L 2; let Z(i:Site L)(t:ℝ):ℂ:=Fir.arm b j L M i (bout y t) r s
 let Y(t:ℝ):= if x=y then Complex.I else 0 -- dummy
 have ht(o':Site L)(z:o' ≠0): HasDerivAt (fun s=>G o' s * Z o' s) 0 0:=by
    have hv:DifferentiableAt ℝ (G o') 0:=glow_T (pen (fun _=>L) (fun _=>h) (fun _=>o') [x] 2) y ()
    have hp:= (hv.hasDerivAt.mul (arm_P b j p L M h v o' z y (r:=r) (s:=s))); apply hp.congr_deriv
    simp only [bout_zero,(arm_u b j p L M h v).2 o' z, Matrix.zero_apply, mul_zero, add_zero]
 let T':=univ.erase (0:Site L); let H:ℂ:= if x=y then I else 0; let K(i:Site L)(s):=G i s* Z i s
 have hh: HasDerivAt (fun x=>∑ i∈T',K i x) 0 0:= (HasDerivAt.fun_sum (fun i (x:i∈ T')=>ht i (mem_erase.mp x).1)).congr_deriv (sum_const_zero)
 have h0: Lattice.lift (0:Site L)=(0:Cover):= by simp [Lattice.lift] -- drop p
 have he(t): A [x] (bout y t) r s = K 0 t+∑ i∈T',K i t:=by
    unfold Fir.paint; rw [Matrix.sum_apply]; simp_rw [Matrix.smul_apply, smul_eq_mul]; simp_rw [h0,mode_zero, one_mul]; rw [add_comm]; exact (Finset.sum_erase_add _ (fun i=> K i t) (mem_univ (0:Site L))).symm
 have hZ : DifferentiableAt ℝ (Z 0) 0:=glow_T ((armPay b j (by omega) (fun _=>L) (fun _=>M) (fun _=>h) (fun _=>v) (fun _=>0)).tap _ _) y ()
 have hp0 :F 0 0=0:=by unfold F; rw [bout_zero,alias_zero_eq]; simp [narrow]
 let k':ℂ:=toll L 2; have hg :G 0 0= 0:=by simp [G,hp0,listChip]
 have hu: HasDerivAt (G 0) (H/(L.val:ℂ)*k') 0:=by
    unfold G; simp_rw [listChip]; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; apply HasDerivAt.mul_const
    unfold F; simp_rw [alias_zero_eq,chip,narrow,bout,Pi.smul_apply,smul_eq_mul]; apply HasDerivAt.sub_const
    by_cases hz:x=y; swap
    · simp [hz,H]; exact hasDerivAt_const ..
    subst x; simp only [Lattice.step_apply, if_true,mul_one,H]; let L' := (L.val:ℂ)
    have hp:= Complex.hasDerivAt_exp 0; let Q(t:ℂ):= I*(L'⁻¹*t)
    have hh: HasDerivAt (Complex.exp ∘ Q) (I/L') 0:=by
       have ht: HasDerivAt Q (I*L'⁻¹) 0:=by simpa only [mul_one] using (((hasDerivAt_id' (0:ℂ)).const_mul L'⁻¹).const_mul I)
       have hb: HasDerivAt Complex.exp (Complex.exp 0) (Q 0):=by change HasDerivAt _ _ (I*(L'⁻¹*0)); simp only [mul_zero]; exact hp
       exact (hb.comp _ ht).congr_deriv (by rw [Complex.exp_zero,one_mul,div_eq_mul_inv])
    have hW:HasDerivAt (fun i:ℝ=> (i:ℂ)) 1 0:= Complex.ofRealCLM.hasFDerivAt.hasDerivAt; exact ((show HasDerivAt (Complex.exp ∘ Q) (I/L') ((↑(0:ℝ)):ℂ) from by rwa [Complex.ofReal_zero]).scomp 0 hW).congr_deriv (by simp [L']) -- scomp as former
 simp_rw [he]; apply (((hu.mul hZ.hasDerivAt).add hh)).congr_deriv
 have hh :Z (0: Site L) 0=(Real.sqrt L.val:ℂ)*binV b r s:=by unfold Z; rw [bout_zero,(arm_u b j p L M h v).1]; rfl
 rw [hh,hg]; unfold H lace; simp only [zero_mul,add_zero,Matrix.smul_apply, smul_eq_mul]; unfold k' toll; push_cast; ring_nf
end YM.CF.Hove
