import YM.CF.DPress.Chess.Green.Edge
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Green
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube RP Phase Branch Mir Mir.Trip Brace Nacre Window Tenant
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m B:Side}{l':Site (More m)}
local notation "V_"=> CSide m B
local notation "I_"=> northTrip m l'
local notation "α_"=> W.i
local notation "J_"=>costarU m B l' (northZ m B) W.i
local notation "κ_"=> mealU (lagX W.od) 1 inert (V_)
local notation "Λξ"=> mealU W.shape (Fixed.pinSpin W.i) inert (V_)
local notation "Θc"=> seamShift m B W.i
variable (p: Attend W B l')
include p
-- prove inter exactly using covariance of physical cut and anti signs.Epoch.
lemma mass : ∃ z:ℂ,(J_).val=z • ((Θc).val*(κ_).val):=by
 obtain ⟨k,h⟩:= prince W p; refine ⟨k,?_⟩; unfold costarU; rw [φ_v W p]; let J:=fperm m B (I_); change (fringe _ _).val * jump J _=k • ((fringe _ _).val * jump (Tofu (lagX W.od) V_) (_:Site V_→_)); unfold Mir.fringe; dsimp only; rw [tof_v W p,jump_mul,jump_mul]; simp only [Equiv.refl_trans]; rw [←jump_smul]; apply congrArg (jump J); ext1 x
 change (edging (far B (I_) _) _ x • (1:Op (SpinIdx × SU.Slot)))*1=k • ((edging _ _ x • 1)* ((lagX W.od).payA x • ((1:Op SpinIdx) ⊗ₖ (1:Op SU.Slot))))
 rw [h x,Matrix.one_kronecker_one, Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,one_mul,smul_smul,smul_smul,mul_assoc]
omit p
lemma field : (κ_).val*(Λξ).val=(negFinger m B W.i).val*(κ_).val:=by
 apply (fun e=>(love (V_)).injective (show ((love (V_)).toRingEquiv) _=(love (V_)).toRingEquiv _ from e)); rw [map_mul,map_mul]; rw [show (love (V_)).toRingEquiv (negFinger ..).val=_ from (Window.fullTurn_matrix (m:=m) (B:=B) W.i).symm]; -- tune
 let X:=lagX W.od; let J:=Fixed.pinSpin W.i; let N:=V_; change (prepU X 1 inert N * prepU W.shape J inert N).val=(prepU (Window.shape W.i) J inert N * prepU X 1 inert N).val; rw [Nacre.kio ..,Nacre.kio ..,mul_one,one_mul]; unfold X; rw [meet W] -- too many args kio? 
include p
lemma krot : (J_).val*(Λξ).val=(finger m B W.i).val*(J_).val:=by
 obtain ⟨v,h⟩:= mass W p; rw [h,Matrix.smul_mul,Matrix.mul_smul,mul_assoc,field W,←mul_assoc,seam_turn,mul_assoc]
-- twist sector generalized helper.
omit p W
open Spark
lemma twist_Ty {I:Type*}[LinearOrder I][Fintype I]{S T:Finset I} (Y:UNI I)(p:twist Y (cutM S)=cutM T){A:FC I}{b}(h:Sector S b A): Sector T b (twist (quantU Y) A):=by
 have he(i)(v:i∈ S) : Sector T true (twist (quantU Y) (put i)):=by
    rw [← create_put,twist_create]; apply Sector.makeP; nth_rw 1 [← p]; rw [←Fock.swivel, cut_basis,if_pos v]
 induction h with
 | up i h=> exact he i h
 | down i h=> rw [takeF,map_star]; exact (he i h).contr
 | zero=> rw [map_zero]; apply Sector.zero
 | one=> rw [map_one]; apply Sector.one
 | add _ _ a b=>rw [map_add]; exact a.add b
 | mul _ _ a b=>rw [map_mul]; exact a.mul b
 | scale _ c a=>rw [twist_scalar]; exact a.scale c
include p W
lemma inter_κ {A:FC (Single V_)}{S:Support (More V_)}{b:Bool}(v: Sector (Fixed.matterRegion V_ S) b A) : twist (quantU (J_)) (Spark.crossL (helix _).symm (W.θ _ A)) = theta (finger m B W.i) (twist (quantU (J_)) (Spark.crossL (helix _).symm A)):=by
 let U:= Λξ; let σ:= (helix V_).symm; have ht(i j:Xmind m B): (W.Ζ V_).val (σ i) (σ j)=U.val i j:= by change U.val (helix V_ (σ i)) (helix V_ (σ j))=_; unfold σ; rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
 have he: Sector (Finset.univ.filter fun i: Xmind m B=> node i.1 ∈ S) b (crossL σ A):= Window.cross_sector (helix _).symm (by intro i; rw [Fixed.mem_matterRegion, mem_filter]; exact (and_iff_right (mem_univ _)).symm) v -- tune newline
 rw [Wall.θ,Window.cross_reflect (helix _).symm (W.Ζ _) _ ht v]; exact Window.twist_inter (J_) U _ (krot W p) he
end YM.CF.DPress.Chess.Green
