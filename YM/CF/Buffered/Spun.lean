import YM.CF.Buffered.Duels
/-!
# Elementary Wilson graphs and channels in a tile
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Mil
open Function Fock NormedSpace SU Lat Lattice Cube Finset Mir Branch Reflect RP MeasureTheory Cin
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
abbrev Spin := SpinIdx × Slot
-- local avoids order on native product system
scoped instance spinOrder : LinearOrder Spin := pickOrd _
variable (i j: Axis)
local notation "st" x => (x ⊗ₖ (1:Op Slot))
lemma twist_atom (F:Op SpinIdx)(U V:Op Slot)(X:Op SpinIdx) : (F ⊗ₖ U)*(X ⊗ₖ V)=(F*X) ⊗ₖ (U*V) := op_kron_mul ..

def mirrorSpin (i:Axis): UNI Spin := ⟨st (pin i), Matrix.kronecker_mem_unitary (pin_U i) (one_mem (unitary (Op Slot)))⟩
local notation "Jp" => mirrorSpin
lemma glass_sq : (Jp i).val*(Jp i).val= -1:=by change (st (pin i))*(st (pin i))=_; rw [op_kron_mul,pin_square,one_mul,op_kron_neg,Matrix.one_kronecker_one]
lemma glass_mp (X X':Op SpinIdx)(U:Op Slot)(h:pin i*X=X'*pin i): twist (Jp i) (X ⊗ₖ U)=X' ⊗ₖ U:= by apply twist_comm; change (st (pin i))*(X ⊗ₖ U)=(X' ⊗ₖ U)*(st (pin i)); rw [op_kron_mul,op_kron_mul,h,one_mul,mul_one]
lemma anti : pin i *grading= (-grading)*pin i:=by rw [pin,neg_mul,←mul_assoc, gradingSwap,neg_mul,neg_neg]
lemma mirror_gamma : pin i* gammaOp i=(-gammaOp i)* pin i:=by rw [pin,mul_assoc,gradingSwap,mul_neg,neg_mul]
lemma mirror_others (p:i≠j): pin i* gammaOp j=gammaOp j * pin i:=by rw [pin,mul_assoc,gradingSwap,mul_neg,←mul_assoc,gammaSwap i j p,neg_mul,neg_neg,mul_assoc]
lemma mirror_low : pin i*lowB i= highB i * pin i:=by rw [lowB,highB,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, mul_sub,add_mul,mirror_gamma,neg_mul,one_mul,mul_one,sub_neg_eq_add]
lemma mirror_pass (p:i≠j): pin i*lowB j=lowB j*pin i:=by rw [lowB,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,sub_mul,mul_sub,one_mul,mul_one,mirror_others i j p]

def above := univ.filter (fun i:Spin=> i.1 ∈ plusHalf)
lemma above_grade : twist (Jp i) (cutM aboveᶜ)=cutM above:=by
 have he : (cutM above:Op Spin)=(1/2:ℂ) • (1+(st grading)):=(show (cutM above:Op Spin)=(st (cutM plusHalf)) by
   ext ⟨x,u⟩ ⟨y,v⟩; by_cases p:x=y <;> by_cases h:u=v <;> simp [p,h,cutM,above]).trans (by rw [raising]; ext ⟨x,u⟩ ⟨y,v⟩; by_cases p:x=y <;> by_cases h:u=v <;> simp [p,h,mul_add])
 rw [dim_cut,he,map_sub,map_one,twist_scalar,map_add,map_one,glass_mp _ _ (-grading) _ (anti i),op_kron_neg,smul_add,smul_add,smul_neg]; module -- tune

-- unit supplied on tally at the site paint. allow zero action for forbidden tile.
def seed (v:Vect): FC Spin:= seedR above (localPair v)
lemma seed_turn (v:Vect)(p:‖v‖=1) : theta (Jp i) (seed v)=seed v:=by
 rw [seed,theta_seed _ (Jp i) _ (above_grade i) (localPair_skew v p), show congrC (Jp i) (localPair v)=(localPair v) from ?_]
 let U:=Jp i
 have he : pin i * spinJ=spinJ * cc (pin i):=by rw [pin,mul_assoc,spinJ_grading, ←mul_assoc, spinJ_inter,cc_mul,mul_assoc]
 have hx : U.val*localPair v=localPair v*(ccU U).val:=by
    unfold localPair; change (st (pin i))*_=_*cc (st (pin i)); rw [op_cc_kron, op_kron_mul,op_kron_mul, he,cc_one,mul_one,one_mul]
 rw [congr_form,hx,mul_assoc, show (ccU U).val*star (ccU U).val=1 from (ccU U).property.2,mul_one]

local notation "D" => matter
def rest : FC Spin := dg ((3:ℝ) • (st grading))
lemma rest_turn : theta (Jp i) rest=rest := by
 have ht: Matrix.trace (st grading)=0:=by rw [Matrix.trace_kronecker]; simp [grading,SpinIdx,Matrix.trace,Fin.sum_univ_succ,Matrix.diag]
 rw [rest,dg_scale,theta_rsmul]; apply congrArg; rw [theta_dg,ht,star_zero, zero_smul,op_star_kron,gradingAdj.star_eq,star_one,glass_mp i _ (-grading) _ (anti i), op_kron_neg,dg_neg]; abel
lemma repr_inv (U:E): star (D U).val=(D U⁻¹).val:=by rw [map_inv]; rfl
lemma repr_mul (U V:E): (D (U*V)).val=(D U).val*(D V).val:=by rw [map_mul]; rfl

def velocity (i:Axis)(U:E): Op Spin:= (grading * lowB i) ⊗ₖ (D U).val
lemma velocity_cont : Continuous (velocity i):= continuous_matrix fun _ _=> continuous_const.mul (matter_cont.matrix_elem _ _)
lemma velocity_x (U:E): twist (Jp i) (velocity i U)= - star (velocity i U⁻¹):=by
 unfold velocity; rw [op_star_kron, repr_inv,inv_inv,star_mul,flatL,gradingAdj.star_eq, ←op_kron_neg]; apply glass_mp; rw [←mul_assoc, anti,neg_mul,neg_mul,mul_assoc (grading),mirror_low,neg_mul,flipCl,mul_assoc] -- tune
lemma velocity_tr (U:E)(p:i≠j) : twist (Jp i) (velocity j U)= -velocity j U:=by
 unfold velocity; rw [←op_kron_neg]; apply glass_mp; rw [←mul_assoc,anti,neg_mul,neg_mul,mul_assoc,neg_mul,mirror_pass i j p,mul_assoc] -- tune

-- actual geometric bond ε • coupled. ε NOT included. left to right.
variable {I K:Type*}[Fintype I][LinearOrder I][Fintype K][LinearOrder K] (f g:Spin↪I)
def coupled (i:Axis)(U:E) := -(slip f g (velocity i U)+star (slip f g (velocity i U)))
lemma coupled_cont : Continuous (coupled f g i):= let e:Continuous _ := (slip_cont f g).comp (velocity_cont i); (e.add e.star).neg
lemma coupled_into (e:I↪K)(f' g':Spin↪K)(a:∀ i,e (f i)=f' i)(b:∀ i,e (g i)=g' i)(U:E): into e (coupled f g i U)=coupled f' g' i U:=by simp_rw [coupled,map_neg,map_add,into_star,slip_into f g e a b]
lemma coupled_sector (U:E) : Sector univ false (coupled f g i U):= by simpa only [coupled,neg_smul,one_smul] using ((slip_sector f g (velocity i U)).add (slip_sector f g _).contr).scale (-1:ℂ)
lemma theta_neg (V:UNI I)(A:FC I): theta V (-A)= -theta V A:=by simpa only [theta_zero,zero_sub] using theta_sub V 0 A
lemma slip_neg (A:Op Spin): slip f g (-A)= - slip f g A:=by simpa only [neg_smul,one_smul] using slip_scale f g A (-1:ℂ)
lemma edge_turn {V:UNI I}{f' g':Spin↪I}(h:Framed f f' V (Jp i))(p:Framed g g' V (Jp i))(v:Disjoint (lows f') (lows g'))(U:E) : theta V (coupled f g i U)=coupled g' f' i U⁻¹:=by
 rw [coupled,theta_neg,theta_add,theta_star,slip_theta _ _ h p v,map_star,velocity_x,star_neg,star_star,slip_neg,neg_neg]; rfl
lemma transverse {V:UNI I}{f' g':Spin↪I}(h:Framed f f' V (Jp i))(p:Framed g g' V (Jp i))(v:Disjoint (lows f') (lows g'))(U:E)(e:i≠j) : theta V (coupled f g j U)=coupled f' g' j U:=by
 rw [coupled,theta_neg,theta_add,theta_star,slip_theta _ _ h p v,map_star,velocity_tr i j U e,star_neg,slip_neg,neg_neg,←slip_star,star_star,add_comm]; rfl

-- mg channel alphabet. incoming from LEFT seam, oriented U⁻¹
-- outgoing on RIGHT seam follows half-spin send.
abbrev Mouth:=Bool × Spin
def inlet (i:Axis)(V:E)(b:Mouth): FC Spin:= let x:=acts (lowB i ⊗ₖ (matter V⁻¹).val) (basisKet b.2); if b.1 then create x else remove x
def outlet (i:Axis)(V:E)(b:Mouth): FC Spin:= theta (Jp i) (inlet i V⁻¹ b)
lemma inlet_sector (V:E)(b:Mouth): Sector univ true (inlet i V b):=by unfold inlet; dsimp only; split; apply uncreate; apply unremove
lemma outlet_sector (V:E)(b:Mouth): Sector univ true (outlet i V b):= untheta (Jp i) (inlet_sector ..)
lemma inlet_cont (b:Mouth): Continuous fun V:E=> inlet i V b:= by
 have he:Continuous fun V:E=> (lowB i ⊗ₖ (matter V⁻¹).val):= continuous_matrix fun x y=> continuous_const.mul ((matter_cont.comp continuous_inv).matrix_elem _ _)
 have hx : Continuous _ := create_cont.comp ((acts_cont.comp he).clm_apply (continuous_const (y:=basisKet b.2)))
 unfold inlet; dsimp only; split; exact hx; exact hx.star
lemma outlet_cont (b:Mouth): Continuous fun V:E=> outlet i V b:= (theta_cont _).comp ((inlet_cont i b).comp continuous_inv)
lemma outlet_turn (u:E)(b:Mouth): theta (Jp i) (outlet i u b)= inlet i u⁻¹ b:= theta_twice _ (glass_sq i) (inlet_sector ..)
lemma bond_value (U V:E) (h:Disjoint (lows f) (lows g)):
    coupled f g i (U*V)= ∑ b:Mouth, Complex.I • (into f (outlet i U b)*into g (inlet i V b)):=by
 let J₀: UNI Spin:= Jp i; let A:Op Spin:= lowB i ⊗ₖ (D U).val; let B:Op Spin:= lowB i ⊗ₖ (D V⁻¹).val
 have he: velocity i (U*V)=J₀.val*A*star B:=by
    unfold A B velocity; rw [op_star_kron,flatL, repr_inv,inv_inv]; change _=(st (pin i))*_*_; rw [op_kron_mul,op_kron_mul,Pinlow,mul_assoc grading,twol,repr_mul,one_mul]
 rw [coupled,he,slip_factor,star_sum,←sum_add_distrib,←sum_neg_distrib]
 conv_rhs => rw [Fintype.sum_prod_type_right]
 refine sum_congr rfl fun b _=>?_; rw [Fintype.sum_bool]; dsimp only [inlet,outlet]; rw [inv_inv]; -- tune
 simp only [ite_true,Bool.false_eq_true,ite_false]; rw [theta_downV, theta_upV,star_mul,←into_star,←into_star,show ∀ v:Ket Spin,star (remove v)=create v from fun v=>star_star _, act_mul]
 change -(into f (create _) * into g (remove _) + into g (create _) * into f (remove _))=_
 rw [map_smul,map_smul,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,smul_smul,smul_smul, mul_neg,Complex.I_mul_I,neg_neg,one_smul,neg_smul,one_smul,interchange f g _ _ h]; abel -- tune
-- native site assembly
section pixel
variable {n : Side} (F:Bkg (More n)) (x:Site n)
def due (n:Side) : Installed (Site n) Spin (Model n) := Equiv.refl _
def side (u: Site n): Spin ↪ Model n := Installed.point (due n) u
lemma edge_energy (c:Site n) :
 dg ((frame matter (links F) c).H) = (∑ i:Site n,into (side i) rest)+
 ∑ i:Axis, ∑ p:Site n,seam c p i • coupled (side p) (side (p+step i)) i (links F (p,i)):=by
 have he : (3:ℂ) • spin n Slot grading=jump (Equiv.refl _) (fun _=> (3:ℝ) • (st grading)):=by rw [spin,←jump_smul]; congr
 rw [supportH, he, dg_add,installed_self (due n) _ _ (show ∀ i j x y, _ from ?_)] -- tune
 · -- i sum
   apply congrArg
   rw [show ∀ (f: Axis→Op (Model n))(S:Finset Axis), dg (∑ i∈S,f i)=∑ i∈S,dg (f i) from ?_]
   swap
   · intro f S; induction S using Finset.induction_on with
     | empty=> simp [dg,dyad] -- tune
     | insert i S p ih=> rw [sum_insert p,sum_insert p,dg_add,ih]
   refine sum_congr rfl fun i _=> ?_
   rw [dg_add,dg_star,plus_block]; let j(p:Site n):Op Spin:= -(seam c p i • velocity i (links F (p,i)))
   have hk : (fun p:Site n=> -(((grading*lowB i) ⊗ₖ 1)*hop matter (links F) c i p))=j:=funext fun p=>by rw [hop, color,Algebra.mul_smul_comm,op_kron_mul,one_mul,mul_one]; rfl
   rw [hk, installed_dg (due n) (advance i) j _ (fun _ _ _ _=> jump_apply ..),star_sum,←sum_add_distrib]
   refine sum_congr rfl fun p _=>?_ ; unfold j side coupled; rw [slip_neg,slip_scale,star_neg,star_smul, seam_real, smul_neg,smul_add,neg_add]; rfl
 · exact fun _ _ _ _=> jump_apply ..
end pixel
end YM.CF.Buffered.Mil
#print axioms YM.CF.Buffered.Mil.edge_energy
#print axioms YM.CF.Buffered.Mil.bond_value
#print axioms YM.CF.Buffered.Mil.edge_turn
