import YM.CF.Haro.Level
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
open Scree
variable{n:Side}{P:RG.BudgetPoint}{h v:ℝ}(X:Hub n)(F:InkD n)
variable (k:Finset (Dwell n)→ℝ)(hp:∀ i,0 ≤ k i)(p:BedP P 1 F X k)
omit hp
include p
lemma ortho_l(U V:Single n): ‖orbitPH (F 1) U V‖ ≤ k {(true,U),(false,V)}:=by
 let r: Dwell n:=(true,U); let s: Dwell n:=(false,V); have hv:=Prism.sig0 (p (ping_f P _) {r,s}); unfold orbitPH; rw [Matrix.of_apply,Prism.port_eq,if_neg,norm_mul,show ‖parity r {s}‖=1 from (by simp [parity])]; simpa [r,s] using hv
 rintro h; simpa using h
include hp
lemma biph(U V:Single n): perk P.power U V ≤ (2:ℝ)^P.power*(1+(endL X.val.1 (tray U V):ℝ))^P.power:=by
 let z:= tray U V; let x:= X.val.1; let W:=endL x z
 have h(a:Dwell n): a∈ z→ separation x (place_x a.2) ≤ W:=fun t=> Finset.le_sup (f:=fun i:Dwell n=>separation X.val.1 (node i.2.1.1)) t -- tune
 have ht : separation (place_x U) (place_x V)≤ W+W:=by
    refine (separation_triangle ..).trans (add_le_add ?_ (h (false,V) (by simp [z,tray]))); rw [separation_comm _ x]; exact h (true,U) (by simp [z,tray])
 rw [←mul_pow]; unfold perk; apply pow_le_pow_left₀ (by positivity); have hx :(separation (place_x U) (place_x V):ℝ) ≤ W+W:=by exact_mod_cast ht
 change _≤2*(1+(W:ℝ)); linarith only [hx]
lemma shade(p':0<h)(hk:∑ i: Finset (Dwell n),sheet (P:=P) k h X.val.1 i≤ v):
 (∑ i: Single n,rakeV (orbitPH (F 1)) P.power i) ≤ (2:ℝ)^P.power*v/h^2:=by
 have hf(i j:Single n):let w:= tray i j; perk P.power i j*‖orbitPH (F 1) i j‖*h^2 ≤ 2^P.power * sheet (P:=P) k h X.val.1 w:=by
    intro w; have hv:= ortho_l X F k p i j; have hg:0 ≤ h^2:=sq_nonneg _; have he:=biph X F k hp p i j
    have ht:0 ≤ (1+(endL X.val.1 w:ℝ))^P.power:=by positivity
    refine (mul_le_mul_of_nonneg_right (mul_le_mul he hv (norm_nonneg _) (mul_nonneg (by positivity) ht)) hg).trans ?_; unfold sheet Scree.tariff; rw [show w.card=2 from ?_]; swap; simp [w,tray]
    apply le_of_eq; unfold w tray; ring
 apply (le_div_iff₀ (by positivity)).mpr; refine le_trans ?_ (mul_le_mul_of_nonneg_left hk (by positivity)); simp_rw [Finset.sum_mul,rakeV,paidX,Finset.sum_mul]; rw [Finset.mul_sum]; refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s:= (univ:Finset (Single n ×Single n)).image (fun i=> tray i.1 i.2)) (subset_univ _) (fun i _ _=> mul_nonneg (by positivity) (mul_nonneg (by unfold Scree.tariff; positivity) (hp i)))); conv_rhs=> rw [sum_image tray_in.injOn,Fintype.sum_prod_type]
 exact sum_le_sum fun i _=> sum_le_sum fun j _=>hf i j
omit hp p
def StackL (A:Hub n→ InkD n)(S:Finset (Hub n)):Op (Single n):= ∑ i∈ S,orbitPH (A i 1)
lemma mono_l(A:Hub n→InkD n)(S:Finset (Hub n))(B:Hub n→ℝ)(p:∀ i∈ S,PressB P i (A i) h (B i)): Monos (StackL A S):=by
 intro i g; let z:= wrap n i; let V:= StackL A S; let f(x y:SpinIdx):=∑ j∈S,CharM (A j) ((0:Site n),x) (z,y) 1
 have hx(x): (gauge (fun _:Seat n=>g) (1:Pane n)) x=(1:Pane n) x:=by simp [Lattice.gauge]
 have hv(x y:SpinIdx): Commute (f x y) (mater g):=by
    unfold Commute SemiconjBy f; rw [Matrix.sum_mul,Matrix.mul_sum]; refine sum_congr rfl fun j h=> ?_ ; have hh:= char_g j _ (p _ h) 1 (r:=((0:Site n),x)) (s:=(z,y)) (fun _=>g); rw [funext hx] at hh; let U:=CharM (A j) (0,x) (z,y) 1; calc
      _ = (mater g *U*star (mater g))*mater g := congr_arg (·* mater g) hh
      _ = _ := by rw [mul_assoc,show star (mater g)*_=1 from (matter g).property.1,mul_one]
 let T:=matPH V 0 z
 have he (x y: SpinIdx)(a b:Slot): T (x,a) (y,b)= f x y a b:=by change V ((0,x),a) ((z,y),b)= _; unfold f V StackL; simp_rw [Matrix.sum_apply]; rfl
 have hm:Commute T (KinX g):=by
    unfold Commute SemiconjBy; ext ⟨x,a⟩ ⟨y,b⟩; rw [Matrix.mul_apply, Matrix.mul_apply]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type (fun l:SpinIdx ×Slot=> (KinX _) _ l * T l (y,b))]; rw [sum_eq_single y,sum_eq_single x]; -- rhs tune
    · simp only [KinX, Matrix.kronecker_apply,Matrix.one_apply_eq,one_mul,he]; exact Matrix.ext_iff.mpr ((hv x y).eq) a b
    · intro i _ h; simp [T,KinX,Matrix.one_apply,h,Ne.symm h] -- tune
    · simp
    · intro i _ h; simp [T,KinX,Matrix.one_apply,h,Ne.symm h]
    simp
 unfold tapH Commute SemiconjBy; rw [Matrix.smul_mul,Matrix.mul_smul,show matPH _ _ _*KinX g= KinX g*T from hm.eq]
lemma shadeH(A:Hub n→InkD n)(S:Finset (Hub n))(T:Hub n→ ℝ)(p:∀ i∈ S,PressB P i (A i) h (T i))(b:∑ i∈S,T i≤ v)(hp:0<h): (∑ i:Single n,rakeV (StackL A S) P.power i) ≤ (2:ℝ)^P.power*v/h^2:=by
 let F(x:Single n)(i:Hub n):=rakeV (orbitPH (A i 1)) P.power x; have hx(i: Single n): rakeV (StackL A S) P.power i ≤∑ j∈S,F i j:=by
    unfold F rakeV paidX StackL; rw [sum_comm]; apply sum_le_sum; intro j _; simp_rw [Matrix.sum_apply,←mul_sum]; exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (by unfold perk; positivity)
 have hq(x:Hub n)(b:x∈ S): (∑ i:Single n,F i x)≤ (2:ℝ)^P.power*T x/h^2:=by
    obtain ⟨k,hk,H,V⟩:= (p x b).worth; exact shade x (A x) k hk (H _) hp V
 apply (sum_le_sum (fun i _=>hx i)).trans; rw [sum_comm]; refine (sum_le_sum hq).trans ?_; rw [←sum_div, ←mul_sum]; gcongr
end YM.CF.Haro
