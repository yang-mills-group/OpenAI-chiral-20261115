import YM.CF.Buffered.Form
import YM.CF.Continuum.Target

/-!
# Apply to one word of the fixed family. Part 1: the actual input to the test.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 530000
noncomputable section
namespace YM.CF.Buffered.Bilinear
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Lifted Heat Advance
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable (K : Calibration)
def creatorSite : Cover:= 1
def removerSite : Cover:= creatorSite + K.vertex • step 3
def segment : Walk := List.replicate (2*K.vertex) (posDir 3)
def support : Finset Cover := (visits (nodeC creatorSite) (segment K)).toFinset
abbrev five := Window.colors (0,false)
def D5 (p q : SU.Slot) (V : LinksC) := (matter (travel V (nodeC creatorSite) (segment K))).val p q
-- minus removal as stated (coefficient). Five colors of generation 0's \bar5.
def word : Buffered.Family K := - ((K.vertex:ℂ)^3 / 5) • ∑ p∈ five,∑ q∈ five,
   Buffered.scalar K ((D5 K p q) ∘ Prod.fst) * (removal K (removerSite K) 2 q * creation K creatorSite 0 p)
lemma end_node : stop (nodeC creatorSite) (segment K)=nodeC (removerSite K) := by
 rw [segment, Sods.swifts]; unfold nodeC removerSite; rw [smul_add,mul_smul (2:ℕ)]; abel
private lemma line_lower : K.plane0+(K.ℓ:ℤ)≤0 := by
 let V:=K.vertex/(2*K.B.val); have ht: 2*K.ℓ ≤ 4*K.B.val*V := K.line
 have hv: K.plane0 = -(↑(4*K.B.val*V):ℤ) := by unfold Calibration.plane0 gaugeShift; unfold Calibration.ζ V; simp only [Nat.cast_mul,Nat.cast_ofNat]; ring
 rw [hv]; omega
private lemma end_X : nodeC (removerSite K)∈support K := by
 rw [←end_node,support,List.mem_toFinset]; apply show ∀ s : Cover, ∀ l:Walk, stop s l∈visits s l from ?_
 intro s l; induction l generalizing s <;> simp_all [stop,visits]
private lemma birth_X : nodeC creatorSite∈support K := by cases he : segment K <;> simp [support,he, visits]
private lemma clear_support : goodSet K (support K) := by
 intro x p; obtain ⟨r,_,rfl⟩:= Cube.range_leg _ (posDir 3) (2*K.vertex) _ (List.mem_toFinset.mp p); apply (line_lower K).trans; simp [nodeC,creatorSite]; omega
private lemma prodWord (wide : Bool) : InTest K wide (support K) false (word K) := by
 refine .smul _ (InTest.sum _ _ fun p _=> InTest.sum _ _ fun q _ =>.mul (.seed (Coeff.fromC _ _ ?_ ?_)) (.mul (.remover q (by decide) (end_X K)) (.creator p (by decide) (birth_X K))))
 · exact (matter_cont.comp (Wilson.continuous_travel _ _)).matrix_elem p q
 intro X Y h; unfold D5; exact congrArg (fun t:SU.E=> (matter t).val p q) (travel_local _ _ X Y (fun e u v=> h e (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v)))
-- pointwise gauge law of the contraction, before common-field integral
section contraction
variable {n : Side} (U : Pane n)
local notation "Z" => cutM five
-- link transporter, as evaluated on the cover at a period.
def D₁ := travel (onC n U) (nodeC creatorSite) (segment K)
def internal (u : SU.E) : Op SU.Slot := Z * (matter u).val * Z
def matrix5 (x y : Site n × SpinIdx) (u : SU.E) : Op (Single n) := Matrix.of fun i k=> if i.1=x ∧ k.1=y then internal u i.2 k.2 else 0
lemma transports (g : Seat n→SU.E) : D₁ K (gauge g U)=g (node (wrap n creatorSite))* D₁ K U * (g (node (wrap n (removerSite K))))⁻¹ := by
 have hx (v:Pane n):D₁ K v=travel v (node (wrap n creatorSite)) (segment K):=by rw [D₁,onC, travel_at,add_zero,node_of]
 rw [hx, travel_gauge,hx,node_of,node_of, ← wrap_stop_cover,end_node]
lemma matrix5_law (x y : Site n × SpinIdx) (V : SU.E) (g : Seat n → SU.E) :
    twist (tradew n g) (matrix5 x y V) = matrix5 x y (g (node x.1)*V*(g (node y.1))⁻¹) := by
  let H := tradew n g; let W:= g (node x.1)*V*(g (node y.1))⁻¹
  have he(V:SU.E)(a b:Site n × SpinIdx) : tap (matrix5 x y V) a b= if a=x ∧ b=y then internal V else 0:= by ext i j; by_cases p:a=x∧ b=y <;> simp [matrix5,tap,p]
  have hp (a b: Site n × SpinIdx) : tap (sings false H (matrix5 x y V)) a b=tap (matrix5 x y W) a b := by
    change tap (sings false (portX (Equiv.refl (Site n × SpinIdx)) (fun i=> matter (g (node i.1)))) _) _ _= _; rw [tap_sg (p:=Equiv.refl (Site n × SpinIdx)) (F:=fun i=> matter (g (node i.1))),he,he]
    by_cases h:a=x ∧ b=y; swap; · simp only [Equiv.refl_apply,if_neg h,win_z,mul_zero,zero_mul]
    obtain ⟨rfl,rfl⟩:= h; simp only [Equiv.refl_apply, true_and, if_true]; unfold W internal; rw [map_mul,map_inv,map_mul]
    let X:=matter (g (node a.1)); let Y:=matter (g (node b.1))
    change X.val*(Z*(matter V).val*Z)*star Y.val=Z*(X.val*(matter V).val*star Y.val)*Z
    have ht:X.val*Z=Z*X.val:= (matter_block ..).eq; have hu:star Y.val*Z=Z*star Y.val:= by
      have he:= (matter_block (0,false) (g (node b.1))⁻¹).eq; rw [map_inv] at he; exact he
    simp_rw [mul_assoc] at *; rw [←mul_assoc X.val Z,ht,mul_assoc]; simp only [mul_assoc,←hu]
  ext ⟨x,a⟩ ⟨y,b⟩; exact congr_fun (congr_fun (hp x y) a) b
private lemma internal_index (V : SU.E) (x y : SU.Slot) : internal V x y = if x∈ five ∧ y∈ five then (matter V).val x y else 0 := by by_cases h:x∈ five<;> by_cases k:y∈ five<;> simp [internal,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,h,k]
private lemma gDyad (x y : Site n × SpinIdx) (V : SU.E) : dg (matrix5 x y V)=∑ i∈five, ∑ j∈ five,(matter V).val i j • (put (x,i)*takeF (y,j)) := by
 let f(i j:Single n):= (matrix5 x y V) i j • (put i * takeF j)
 change ∑ i,∑ j, f i j=_
 have hp (a : Site n × SpinIdx) (i : SU.Slot) : ∑ t : Single n, f (a,i) t= ∑ j:SU.Slot, f (a,i) (y,j):=by
    rw [show (∑ t : Single n, f (a,i) t)=_ from Fintype.sum_prod_type (fun k : (Site n × SpinIdx) × SU.Slot=> f (a,i) k), sum_eq_single y]
    all_goals simp_all [f,matrix5]
 rw [show (∑ i,∑ j,f i j)=_ from Fintype.sum_prod_type (fun k : (Site n × SpinIdx) × SU.Slot=> ∑ j, f k j)]; simp_rw [hp]
 rw [sum_eq_single x]; simp [f,matrix5,five,internal_index, colors, ite_smul, ite_and,sum_filter]; all_goals simp_all [f,matrix5]
private def Sfactor (K : Calibration) (n : Side) : ℂ := winding n (removerSite K) * winding n creatorSite
def lineOp (K : Calibration)(U : Pane n) : Op (Single n) := matrix5 (wrap n creatorSite,0) (wrap n (removerSite K),2) (D₁ K U)
private lemma orderWord (x : Site n × SpinIdx) (y : Site n × SpinIdx) (p : x≠ y) (i j : SU.Slot) : takeF (y,j)*put (x,i)= -(put (x,i)*takeF (y,j)) := eq_neg_of_add_eq_zero_left ((mixed _ _).trans (if_neg (fun u=>p (congrArg Prod.fst u).symm)))
end contraction
lemma reads (m : Side) (U : Fields (K.c m)) : word K m U = (((K.vertex:ℂ)^3/5)*Sfactor K (K.c m)) • dg (lineOp K U.1) := by
 let n:=K.c m; let x:Site n×SpinIdx:= (wrap n creatorSite,0); let y: Site n×SpinIdx:=(wrap n (removerSite K),2); have he:x≠y:=fun w=> (by decide : (0:SpinIdx)≠2) (congrArg Prod.snd w)
 unfold word lineOp; rw [gDyad]; simp_rw [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, smul_sum]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ;
 change _ • ((D5 K i j (onC n U.1)) • (1:FC _) * (Fock.remove _ * create _)) = _
 unfold Fock.remove; simp only [basisC,map_smul,star_smul,create_put]
 rw [Algebra.smul_mul_assoc,one_mul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]; let c:=(K.vertex:ℂ)^3/5; let W:= D5 K i j (onC n U.1); let l:=Lifted.winding n (removerSite K); let k:= Lifted.winding n creatorSite
 change -c • (W • (star l • (k • (takeF (y,j)*put (x,i))))) = (c*(l*k)) • (W • (put (x,i)*takeF (y,j)))
 rw [orderWord x y he, show star l=l from fee_real _, smul_neg,smul_neg,smul_neg,neg_smul, smul_neg,neg_neg]; simp only [smul_smul]; congr 1; ring
lemma word_covariant (m : Side) : covariant (word K m) := by
 intro g x; rw [reads,reads, twist_scalar,dg_cov]; unfold lineOp; rw [matrix5_law, show (simultaneous g x).1= gauge g x.1 from rfl, transports]
lemma allowed (wide : Bool) : Eligible K wide (word K) := ⟨⟨support K,prodWord K wide, clear_support K⟩,fun _=> Eventually.of_forall fun m _=> word_covariant K m⟩
end YM.CF.Buffered.Bilinear
