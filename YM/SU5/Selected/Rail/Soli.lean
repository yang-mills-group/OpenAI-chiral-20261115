import YM.SU5.Selected.Rail.Drum
/-! # Synthetic stencil. Circle units. Rectangles; buys same contact matrix requested. Gram with
actual finite Male. rank cost can be buffered across moments using Kap.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
open Finset Lat
variable {n:ℕ}{q h:Type*}[Fintype q][DecidableEq q][Fintype h][DecidableEq h]
def stick(W:FaceL)(t:ℕ)(v:Fin n):Cover:= Ε W (↑(t+v.val:ℕ))
def pick(v:ℕ):Cover:= Ε 0 (v:ℤ)
def lacuna (w:Coast):ℂ:=1-prefixG (pick 1) w
def tilt(st:SpinIdx)(F: q→ℂ): WRect SpinIdx q:= Matrix.of fun i j=> if st=i then F j else 0
@[fun_prop] lemma tilt_c(t:SpinIdx): Continuous (tilt t (q:=q)):= continuous_matrix fun i j=>by unfold tilt; simp only [Matrix.of_apply]; split_ifs <;> fun_prop
def hull(k:ℕ)(f:q→ℕ→₀ℂ)(w:Coast)(j:q):ℂ:= lacuna w ^ k * ∑ i ∈ (f j).support,f j i * prefixG (pick i) w
abbrev basisRule:= ℕ→₀ℂ
lemma lacuna_h(x:Bin):lacuna (harbor x)= fade (x 3):=by
 have he:= Fin.snoc_init_self x; let y:=fun i:Fin 3=> x i.castSucc; let t:=x 3; nth_rw 1 [← show Ε y t=x from he]; unfold lacuna pick fade; rw [harbor_join,tintMono,prefix_zero,one_mul,soldier]; norm_num [t]
lemma hull_f (k:ℕ)(f:q→ℕ→₀ℂ)(x:Bin)(j:q):hull k f (harbor x) j=fleece k x * ∑ i∈(f j).support, f j i*prefixG (pick i) (harbor x):=by unfold hull fleece; rw [lacuna_h]
def Spouse (W:FaceL)(n t:ℕ)(w:Coast) :WRect SpinIdx (Fin n):= tilt 2 (fun i=> prefixG (- (stick W t i)) w)
def ShiftY (k:ℕ)(f:q→ℕ→₀ℂ)(w:Coast): WRect SpinIdx q:=tilt 0 (hull k f w)
@[fun_prop] lemma spouse_c (W:FaceL)(t:ℕ): Continuous (Spouse W n t):= (tilt_c _).comp (continuous_pi (fun i=> prefix_c _)) -- UU pi expects fun w→ f ... atom rewrite
@[fun_prop] lemma shift_c (k:ℕ)(f:q→ℕ→₀ℂ): Continuous (ShiftY k f):= by
 have h: Continuous lacuna:=continuous_const.sub (prefix_c _); refine (tilt_c _).comp (continuous_pi (fun i=>?_)); unfold hull; fun_prop
lemma stitch_x (W:FaceL)(t n:ℕ)(w:Coast): (1-Aop)*Spouse W n t w= Spouse W n t w:=by
 rw [Adef,← Lat.raising,← dim_cut]; ext i j; rw [cutM,Matrix.diagonal_mul]; fin_cases i <;> simp (config:={decide:=true}) [Spouse,tilt]
lemma stitch_y (k:ℕ)(f:q→basisRule)(w:Coast): Aop*ShiftY k f w=ShiftY k f w:=by
 rw [Adef,← Lat.raising]; ext i j; rw [cutM,Matrix.diagonal_mul]; fin_cases i <;> simp (config:={decide:=true}) [ShiftY,tilt]
def Deep (M:Maj) (k:ℕ)(f:q→basisRule)(x:Bin): WRect SpinIdx q:= wagon M x * ShiftY k f (harbor x)
lemma conceal (M:Maj)(k:ℕ)(f:q→basisRule)(x:Bin) : Aop*Deep M k f x=ShiftY k f (harbor x):=by
 unfold Deep wagon; simp_rw [Matrix.mul_assoc (1-zen _)]; rw [stitch_y,←Matrix.mul_assoc Aop,mul_sub,mul_one,zenA, Matrix.sub_mul,Matrix.mul_assoc,Matrix.sub_mul,Matrix.one_mul,stitch_y,sub_self,Matrix.mul_zero,sub_zero] -- tune
lemma projection (M:Maj)(k:ℕ)(f:q→basisRule)(x:Bin)(p:x∈stemGuard)(e:x≠0) : bar 4 M.val (tmap x)*Deep M k f x=Deep M k f x:=by
 unfold Deep; rw [←Matrix.mul_assoc]; congr 1; exact lead true 4 M.val M.property (base_subset_realCube zone_pos (b_base (stemG.mp p))) (gentil p e)
lemma entertains (M:Maj)(k:ℕ)(Z:q→basisRule)(W:FaceL)(t n:ℕ)(x:Bin)(i:Fin n)(j:q) : ((Spouse W n t (harbor x))ᴴ*Deep M k Z x) i j=∑ u∈(Z j).support, Z j u * hood k M (Ε W (↑(t+u+i.val:ℕ))) x:=by
 let z:=harbor x; let f:= wagon M x; let ℓ:=hull k Z z j; unfold Deep; rw [Matrix.mul_apply]; rw [sum_eq_single 2]; rw [Matrix.mul_apply]; rw [sum_eq_single 0];
 · have he(u:ℕ): stick W t i+pick u= Ε W (↑(t+u+i.val:ℕ)):=by rw [stick,pick,picked]; rw [add_zero]; congr 1; push_cast; ring
   simp only [Matrix.conjTranspose_apply,Spouse,tilt,ShiftY,Matrix.of_apply,if_true,prefix_neg,star_star,hull_f,hood,carillon,Matrix.smul_apply,smul_eq_mul]; simp_rw [mul_sum]; apply sum_congr rfl; intro k _; rw [←he,prefix_add]; ring
 -- nonzero off
 · intro b _ h; simp only [ShiftY,tilt,Matrix.of_apply,if_neg (Ne.symm h),mul_zero];
 · simp
 · intro b _ h; simp only [Matrix.conjTranspose_apply,Spouse,tilt,Matrix.of_apply,if_neg (Ne.symm h),star_zero,zero_mul]
 simp
lemma feasible_cost(M:Maj)(k:ℕ)(Z:q→basisRule)(W:FaceL)(t n:ℕ)(N:Side)(i:Fin n)(j:q) : packA N (fun x:Site N=> ((Spouse W n t (brim N x))ᴴ*Deep M k Z (pm x)) i j)= ∑ u∈(Z j).support, Z j u * packA N (hood k M (Ε W (↑(t+u+i.val:ℕ))) ∘ pm):=by
 let T:=fun u:ℕ=> (hood k M (Ε W (↑(t+u+i.val:ℕ)))) ∘ (@pm N); let X(u:ℕ)(a:Site N):= Z j u*T u a
 let V(x:Site N):= ((Spouse W n t (brim N x))ᴴ*Deep M k Z (pm x)) i j; change packA N V = ∑ u∈(Z j).support, Z j u * packA N (T u)
 have ht: V = fun x=> ∑ u∈(Z j).support, X u x:=funext (fun x=> entertains M k Z W t n (pm x) i j); rw [ht,pack_sum]; refine sum_congr rfl (fun u _ => pack_smul N (T u) (Z j u))

end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms entertains
#print axioms conceal
#print axioms shift_c
#print axioms feasible_cost
#print axioms projection
