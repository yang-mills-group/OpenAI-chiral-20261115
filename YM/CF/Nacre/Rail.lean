import YM.CF.Nacre.Chair
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
def incX (s:Signed):Shape:=⟨s,0⟩
def lagX (t:Cover):Shape:=⟨1,t⟩
def joinX(a b:Shape):Shape:=⟨a.s*b.s,a.s.act b.t+a.t⟩
def spinX(s:Signed):UNI SpinIdx:= (det_sub false s).choose
lemma bud_s(s:Signed):JetS s false (detX s) (spinX s):=(det_sub false s).choose_spec
def Yg(a:Shape)(U:Bkg (More n)):=stir inert a U
lemma palm(a b:Shape)(x:Cover): (joinX a b).motion x=a.motion (b.motion x):=by
 unfold Shape.motion joinX; simp only [Signed.act_mul,Signed.act_add]; rw [smul_add, show a.s.act (2 • b.t)= 2 • a.s.act b.t from map_nsmul (a.s.actEquiv (R:=ℤ)) _ _]; abel
lemma plait(a b:Shape)(x:Cover): (joinX a b).flee x=a.flee (b.flee x):=by
 apply nsmul_right_injective (M:=Cover) (show (2:ℕ)≠0 by decide); change (2:ℕ) • _= 2 • _; apply add_right_cancel (b:= (_:Cover)) (a:= (2:ℕ) • (joinX a b).flee x) (show (2:ℕ) • (joinX a b).flee x +1=2 • a.flee (b.flee x)+1 from by rw [← Shape.mote,←Shape.mote,palm,b.mote]) -- tune
lemma yen(a b:Shape)(x:Site n): (joinX a b).mills n x= a.mills n (b.mills n x):=by rw [←nat_true x, Shape.mill, plait,← Shape.mill, ← Shape.mill]
lemma kor(a b:Shape)(x:Bkg (More n)): Yg (joinX a b) x=Yg b (Yg a x):=by
 funext ⟨i,j⟩; have ht:Shape.anon (joinX a b) n i=a.anon n (b.anon n i):=by rw [←nat_true i, Shape.anno,palm,← Shape.anno,←Shape.anno]
 change (posDir j).read (Yg _ _) i=(posDir j).read (Yg _ _) i; unfold Yg; rw [veil_x,veil_x,veil_x,show (joinX a b).s= _ from rfl] -- tune
 rw [show (joinX a b).s=a.s*b.s from rfl,Step.rotate_mul,ht]; rfl
lemma nyt(a b:Shape)(x:Site n): (joinX a b).payA x=b.payA x*a.payA (b.mills n x):=by
 suffices h: (joinX a b).rent x=a.rent (b.mills n x)+ a.s.act (b.rent x) by rw [Shape.payA,h,dues, dueShape,mul_comm]; rfl
 apply nsmul_right_injective (M:=Cover) n.property.ne'
 change n.val • _= n.val • _; apply add_left_cancel (a:= natural ((joinX a b).mills n x)); rw [Shape.vibes, plait, ← Shape.vibes b, Shape.flee_p,show a.s.act (n.val • b.rent x)= n.val • a.s.act (b.rent x) from map_nsmul (a.s.actEquiv (R:=ℤ)) _ _, ← Shape.vibes, yen, add_assoc, smul_add]
lemma Ygs(a:Shape)(U V:UNI SpinIdx){z:ℂ}(h:U.val=z • V.val):(prepU a U inert n).val=z • (prepU a V inert n).val:=by
 have he:(mealU a U inert n).val=z • (mealU a V inert n).val:=by change jump (Tofu a n) (fun i=> (milU a U inert i).val)= z • jump (Tofu a n) (fun i=> (milU a V inert i).val); rw [←jump_smul]; apply congrArg (jump (Tofu a n)); ext1 x; change a.payA x • (U.val ⊗ₖ (1:Op Slot))= z • (a.payA x • (V.val ⊗ₖ (1:Op Slot))); rw [h,Matrix.smul_kronecker,smul_comm z]
 ext i j; exact Matrix.ext_iff.mpr he _ _ -- tune
lemma kio(n:Side)(a b:Shape)(U V:UNI SpinIdx): prepU b V inert n * prepU a U inert n =prepU (joinX a b) (V*U) inert n:=by
 apply Subtype.ext; change love n _ *love n _ = _; rw [← map_mul]; apply congr_arg (love n)
 have h: (Tofu b n).trans (Tofu a n) = Tofu (joinX a b) n:= Equiv.ext fun x=> (yen a b x).symm
 change jump (Tofu b n) (fun i=>(milU b V inert i).val)*jump (Tofu a n) (fun i=>(milU a U inert i).val)= jump (Tofu (joinX a b) n) (fun i=> (milU (joinX a b) (V*U) inert i).val); rw [jump_mul,h]; apply congrArg (jump _); ext1 i; change (b.payA i • (V.val ⊗ₖ (1:Op Slot)))*(a.payA (b.mills n i) • (U.val ⊗ₖ (1:Op Slot))) = (joinX a b).payA i • (((V.val*U.val) ⊗ₖ (1:Op Slot)))
 rw [nyt,Matrix.smul_mul,Matrix.mul_smul,smul_smul,op_kron_mul, mul_one]

def ape (n:Side)(a:Shape)(X: Op (Single n)):= twist (prepU a (spinX a.s) inert n) X
lemma apes (a b:Shape)(X:Op (Single n)): ape n b (ape n a X)=ape n (joinX a b) X:=by
 let U:=spinX a.s; let V:=spinX b.s; obtain ⟨z,hx,hz⟩:= kits (joinX a b).s (V*U) (spinX (joinX a b).s) (by change JetS (a.s*b.s) false (detX (a.s*b.s)) _; rw [det_p]; exact jet_add _ _ _ _ _ U V (bud_s _) (bud_s _)) (bud_s _)
 unfold ape; rw [← twin,kio,twist_formula,twist_formula,Ygs (joinX a b) _ _ hx,star_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (star z),hz,one_smul]
end YM.CF.Nacre
