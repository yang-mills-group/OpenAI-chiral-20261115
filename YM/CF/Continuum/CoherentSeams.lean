import YM.CF.Continuum.FibreCone
import YM.CF.Continuum.Algebra
import YM.CF.Spark.Org
import YM.CF.Reflect.Reuse

/-! Intertwine reflection for genuine occupancy stencils in the native `anticut`
    ABI with that for tests in the special reflection seam ABI. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Lattice Wilson Lat SU Fock Phase Mir Cube Mir.Trip RP Reflect Finset Spire Brace Spark Scroll Tulip Dial
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
section index
variable {I J : Type*}[LinearOrder I][LinearOrder J][Fintype I][Fintype J](U:I≃J)
local notation "R"=> crossL U

def continuityAtCross : FC J→L[ℂ] FC I :=
  { toFun:=R
    map_add' a b:=cx_eq U _ _ fun x=>by rw [act_add,act_add, ←crossed, ←crossed]; exact map_add (Fock.hoist U.toEmbedding ∅) _ _
    map_smul' c y:=cx_eq U (c • y) (c • crossL U y) fun x=> by rw [act_smul,act_smul,carts_s,crossed]
    cont:= cxC .. }
lemma cross_add (a b:FC J) : R (a+b)=R a+R b := map_add (continuityAtCross U) a b
lemma cross_scalar (c:ℂ)(a:FC J) : R (c•a)=c • R a:=map_smul (continuityAtCross U) c a
lemma cross_one : R 1=1:=cx_eq U _ _ fun x=>by rw [act_one,act_one]
lemma cross_zero : R 0=0:=map_zero (continuityAtCross U)
lemma cross_sigma {K:Type*}(S:Finset K)(A:K→ FC J) : R (∑ i∈S,A i)=∑ i∈S,R (A i):= map_sum (continuityAtCross U) ..
lemma cross_reflect (A:UNI J)(B:UNI I)(h:∀ i j, A.val (U i) (U j) = B.val i j) {P: FC J}{o:Finset J}{b:Bool} (p:Sector o b P) : R (theta A P)=theta B (R P) := by
  induction p with
  | zero=> rw [theta_zero,cross_zero,theta_zero]
  | one=> rw [theta_one,cross_one,theta_one]
  | up i p=>
    obtain ⟨i,rfl⟩:=U.surjective i; rw [(cx_p ..).1,theta_up,theta_up, cross_scalar]; congr 1; simp_rw [remove_def,cross_sigma,cross_scalar,basis_act]; rw [←Equiv.sum_comp U]; exact sum_congr rfl fun j _=>by rw [h,(cx_p ..).2]
  | down i p=>
    obtain ⟨i,rfl⟩:=U.surjective i; rw [(cx_p ..).2,theta_down,theta_down,cross_scalar]; congr 1; simp_rw [create_def,cross_sigma,cross_scalar,basis_act]; rw [←Equiv.sum_comp U]; exact sum_congr rfl fun j _=>by rw [h,(cx_p ..).1]
  | add _ _ h g => rw [theta_add,cross_add,cross_add,h,g,theta_add]
  | mul _ _ h g => rw [theta_mul,cx_m,cx_m,h,g,theta_mul]
  | scale _ q h=> rw [theta_smul,cross_scalar,cross_scalar,h,theta_smul]
lemma cross_sector {S:Finset J}{T:Finset I}(h:∀i: I,U i∈S ↔ i∈T){X: FC J}{b:Bool}(p:Sector S b X):Sector T b (R X):=by
  induction p with
  | zero=> rw [cross_zero]; apply Sector.zero
  | one=> rw [cross_one]; apply Sector.one
  | up i p=> obtain ⟨j,rfl⟩:=U.surjective i; rw [(cx_p ..).1]; exact Sector.up j ((h j).1 p)
  | down i p=> obtain ⟨j,rfl⟩:=U.surjective i; rw [(cx_p ..).2]; exact Sector.down j ((h j).1 p)
  | add _ _ h g=> rw [cross_add]; exact Sector.add h g
  | mul _ _ h g=> rw [cx_m]; exact Sector.mul h g
  | scale _ q h=> rw [cross_scalar]; exact h.scale q
lemma twist_sector {S:Finset I}(A:UNI I) (p: twist A (cutM S)=cutM S) {X: FC I}{b:Bool}(h:Sector S b X): Sector S b (twist (quantU A) X):=by
  have he i (v:i∈S) : Sector S true (twist (quantU A) (put i)) := by
    rw [←create_put,twist_create]; apply Sector.makeP; nth_rw 1 [←p]
    rw [←Fock.swivel,cut_basis]; rw [if_pos v]
  induction h with
  | up i h=> exact he i h
  | down i h=> rw [takeF,map_star]; exact (he i h).contr
  | zero=> rw [map_zero]; apply Sector.zero
  | one=> rw [map_one]; apply Sector.one
  | add _ _ a b=> rw [map_add]; exact a.add b
  | mul _ _ a b=> rw [map_mul]; exact a.mul b
  | scale _ c a=> rw [twist_scalar]; exact a.scale c

lemma twist_inter (A B C: UNI I)(p:A.val * B.val=C.val*A.val){S:Finset I}{b:Bool}{T:FC I}(h:Sector S b T): twist (quantU A) (theta B T) = theta C (twist (quantU A) T) := by
  have up (i:I): twist (quantU A) (theta B (put i))=theta C (twist (quantU A) (put i)):=by
    rw [←create_put, twist_create, theta_upV, theta_upV, twist_scalar, twist_remove, ←act_mul, ←act_mul,p]
  induction h with
  | zero => simp [theta_zero]
  | one => simp [theta_one]
  | up i _ => exact up i
  | down i _ => rw [takeF,theta_star,map_star,up,map_star,theta_star]
  | mul _ _ a b=> rw [theta_mul,map_mul,map_mul, a,b,theta_mul]
  | add _ _ a b=> rw [theta_add,map_add,map_add, a,b,theta_add]
  | scale _ c a=> rw [theta_smul,twist_scalar,twist_scalar,a,theta_smul]
end index

section reflection
variable {N m B : Side}
local notation "Λ"=>CSide m B
local notation "Ω"=>Xmind m B
local notation "β"=>northZ m B
local notation "Xskin"=> Skin m B
variable (i:Axis)
/-- seam rephasing --- from native anticut to the link reflection seam. -/
def seamShift (m B:Side)(i:Axis) := fringe (northZ m B) (axisCut m B i (northZ m B))

def negFinger (m B:Side)(i:Axis): UNI (Xmind m B) :=
   ⟨-(finger m B i).val,by
    constructor
    · rw [star_neg,neg_mul_neg]; exact (finger m B i).property.1
    rw [star_neg,neg_mul_neg]; exact (finger m B i).property.2⟩
lemma seam_sign (t : Foot m B) : edging β (axisCut m B i β) t=if t∈posY m B i then -1 else 1:= by
  unfold edging; rw [prod_eq_single i]; swap; · intro j _ h; rw [axisCut, update_of_ne h]; rw [edgeF,sub_self,ZMod.val_zero]; rw [if_neg (by omega)]
  swap; · intro h; exact False.elim (h (mem_univ _))
  let η := oddSize m B
  let K := CSide m B; let n := K.val; let x:=t i; let v:=x.val
  have hn:n=2*η:= suff m B; have he : 0<η:= oddP
  have hk : η<n:=by omega
  have ha := (ZMod.val_lt x); change v<n at ha
  unfold edgeF; rw [show β i= -1 from rfl,cbase,sub_neg_eq_add,sub_neg_eq_add,sub_add_cancel, ZMod.val_natCast_of_lt hk, ZMod.val_add, ZMod.val_one_eq_one_mod,Nat.add_mod_mod]
  simp only [posY,mem_filter,mem_univ,true_and]
  change (if 0< (v+1)%n ∧ (v+1)%n≤ η then _ else _) = if v<η then _ else _; by_cases p:v+1=n
  · rw [p,Nat.mod_self]; rw [if_neg (by omega),if_neg (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]; by_cases h:v<η; rw [if_pos (by omega),if_pos h]; rw [if_neg (by omega),if_neg h]
lemma seam_keeps : twist (seamShift m B i) (cutM (colony m B i))= cutM (colony m B i):=by
  apply Mir.twist_comm; ext x y; rw [cutM, Matrix.mul_diagonal,Matrix.diagonal_mul]; change jump (Equiv.refl _) _ _ _ * _ = _*jump (Equiv.refl _) _ _ _; by_cases h:x.1=y.1
  · by_cases p:x∈colony m B i
    · simp only [colony_at,h] at *; rw [if_pos p,mul_one,one_mul]
    simp only [colony_at,h] at *; rw [if_neg p,mul_zero,zero_mul]
  rw [jump_apply]; simp [h]
lemma seam_turn : (seamShift m B i).val*(negFinger m B i).val=(finger m B i).val * (seamShift m B i).val:=by
  unfold seamShift fringe negFinger; simp only [seen, ←jump_neg]; rw [jump_mul, jump_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext x
  rw [seam_sign,seam_sign]; by_cases k:x∈posY m B i
  · rw [if_pos k, if_neg fun p=> (((tiltSide ..).1 p) k)]; simp
  rw [if_neg k, if_pos ((tiltSide ..).2 k)]; simp

def toSeam (m B:Side)(i:Axis) (A:FC (Single (CSide m B))) : FC (Xmind m B) := twist (quantU (seamShift m B i)) (crossL (helix (CSide m B)).symm A)
lemma toSeam_prod (A C:FC (Single Λ)) : toSeam m B i (A*C)=toSeam m B i A * toSeam m B i C:=by unfold toSeam; rw [cx_m,map_mul]
lemma toSeam_scalar (a:ℂ)(A:FC (Single Λ)) : toSeam m B i (a•A)=a•toSeam m B i A:=by unfold toSeam; rw [cross_scalar,twist_scalar]
lemma toSeam_one : toSeam m B i 1=1:=by unfold toSeam; rw [cross_one,twist_formula,mul_one]; exact (quantU (seamShift m B i)).property.2 -- ]
lemma toSeam_forward {A : FC (Single Λ)}{M:Finset (Site Λ)}{b:Bool}(h:Sector (matterSet Λ M) b A) (e:M=posY m B i): Sector (colony m B i) b (toSeam m B i A):=by
  apply twist_sector (seamShift m B i) (seam_keeps i); apply cross_sector _ ?_ h; intro j; rw [colony_at,mem_matterSet,e]; rfl
lemma toSeam_turn {A: FC (Single Λ)}{b:Bool}(h:Sector (matterSet Λ (posY m B i)) b A) : toSeam m B i (theta (fullTurn m B i) A)=theta (finger m B i) (toSeam m B i A):=by
  let U: UNI Ω:=negFinger m B i; let E:= (helix Λ).symm
  have hh(j k:Ω):(fullTurn m B i).val (E j) (E k)=U.val j k:=by
    rw [fullTurn_matrix]; change U.val (helix Λ (E j)) (helix Λ (E k))= _; unfold E; rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] -- E defs need
  unfold toSeam; rw [cross_reflect E _ _ hh h]; exact twist_inter (seamShift m B i) U _ (seam_turn i) (cross_sector E (S:=matterSet Λ _) (T:=colony m B i) (fun i=> by rw [mem_matterSet,colony_at]; rfl) h)
lemma toSeam_fiscal {F : Evaluation Λ} (h : F∈nonnegativeTime m B i) (x: Xskin) :
   toSeam m B i ((flipTime m B i F * F) x)= theta (finger m B i) (toSeam m B i (F (mirrorPane m B i x))) * toSeam m B i (F x):= by
   rw [Pi.mul_apply, flipTime,toSeam_prod]; exact congrArg (fun z=> z * _) (toSeam_turn i (((mem_localObs ..).1 h).2.2.1 _).sector)

end reflection
end YM.CF.Window
