import YM.SU5.Diva.Balm
import YM.SU5.Six.PairChoices
/-! CP13. Genuine matter slots — use physicist's column labels indexed by slot family and a SECOND generation. -/
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Mir.Trip Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology Kronecker
attribute [local instance] opCStarAlgebra
open Py.Rate.LocalLimit.Papal (Weaver household)
open YM.CF.Lamour YM.CF.Velvet YM.CF.Lamour.Bridge.Celeste
open Twah
namespace Chalice
abbrev Ruby := Window.Family × Fin 3 -- creation color block, removal generation (uses same species)
abbrev Stone := Ruby × Twah.DirSpin
abbrev modes (Z:Ruby):=Window.colors Z.1
abbrev setRuby (Z:Ruby) (s:Slot) : Slot:= (Z.2,s.2) -- no conditions yet
-- new label action, one permit
variable (N:Side) (x:Site N)(i j:SpinIdx)(A:Ruby)
def seatGate (b:Bool):Op SU.Sheet:=cutM (univ.filter fun i:SU.Sheet=> i.isLeft=b)
def glazeA(A:Ruby):Op SU.Slot:= (Matrix.single A.1.1 A.2 1:Op (Fin 3)) ⊗ₖ seatGate A.1.2
lemma ruby_diag (V:SU.E)(b:Bool): Commute (each (fund V)) (seatGate b):=by
 ext a e; rw [seatGate,cutM,Matrix.mul_diagonal, Matrix.diagonal_mul]; cases a <;> cases e <;> cases b <;> simp [each,Join.both] -- try
lemma ruby_color (V:SU.E): Commute (matter V).val (glazeA A):=by rw [commute_iff_eq,matter_matrix]; simp only [triple,glazeA,op_kron_mul,mul_one,one_mul,(ruby_diag V _).eq] -- op
lemma glazeU (p q:Slot): glazeA A p q=if p∈modes A ∧ q=setRuby A p then 1 else 0:=by
 rcases p with ⟨t,p⟩; rcases q with ⟨u,q⟩; have hv : ((t,p):Slot)∈ modes A ↔ t = A.1.1 ∧ p.isLeft=A.1.2:=by simp [modes,colors,family, Prod.ext_iff];
 simp only [hv]; by_cases h:t=A.1.1 <;> by_cases e:u=A.2 <;> by_cases z:p=q <;> simp [setRuby,h,e,z,glazeA,Matrix.single,seatGate,cutM, Eq.comm (a:=A.1.1),Eq.comm (a:=A.2)]
 all_goals first | simp_all | rfl
 all_goals exact fun _=> fun w=> z w.symm
noncomputable def goblet : Op (Single N) := love N (jump (Equiv.refl (Site N)) fun u=> if u=x then (Matrix.single i j 1:Op SpinIdx) ⊗ₖ glazeA A else 0)
lemma keeps (g:Seat N→SU.E):twist (tradew N g) (goblet N x i j A)=goblet N x i j A:=by
 apply Mir.twist_comm; rw [tradew_eq_love,goblet,←map_mul,←map_mul]; unfold conjG Lat.color; simp only [jump_mul,Equiv.refl_apply]; apply congrArg (love N); congr 1; funext u; split_ifs; · rw [op_kron_mul, op_kron_mul, one_mul,mul_one,(ruby_color A _).eq]
 rw [mul_zero,zero_mul]
lemma goblet_entry (u v : Site N × SpinIdx) (c d:Slot) : goblet N x i j A (u,c) (v,d)=if u=(x,i) ∧ v=(x,j) ∧ c∈modes A ∧ setRuby A c=d then 1 else 0:=by
 obtain ⟨y,a⟩:=u; obtain ⟨z,b⟩:=v; by_cases t:y=z; swap
 · by_cases h:y=x; subst y; simp [goblet,loveAt,unityP,Matrix.submatrix_apply,helix,jump_apply,t,Ne.symm t]
   simp [goblet,loveAt,unityP,Matrix.submatrix_apply,helix,jump_apply,t,h]
 subst z; unfold goblet; by_cases h:y=x
 · subst y; by_cases p:a=i<;>by_cases q:b=j<;>simp [p,q,loveAt,unityP,Matrix.submatrix_apply,helix,jump_apply,Matrix.single,glazeU,_root_.eq_comm (a:=i), Eq.comm (a:=j), Eq.comm (a:=d)]
 simp [loveAt,unityP,Matrix.submatrix_apply,helix,jump_apply,h]
lemma goblet_words : dg (goblet N x i j A)= ∑ c∈modes A, put ((x,i),c) * takeF ((x,j),setRuby A c):=by
 unfold modes colors; rw [sum_filter]; unfold dg dyad; simp_rw [Single,Fintype.sum_prod_type,goblet_entry]; simp [ite_and,modes,colors] -- try
-- Twah born at one matter point.
variable (o:Cover)(a:Stone)
def pitcher (o:Cover)(S:DirSpin):Twah:= ⟨o,o,S.1,S.2,[],rfl⟩
def honey (o:Cover):Finset Cover:={nodeC o}
lemma cupArea(S:DirSpin): (pitcher o S).patio=honey o:=by simp [patio,pitcher,visits,honey]
variable (R:ℕ)
def Wort (o:Cover)(s:Stone)(R:ℕ): Weaver := Twah.gold R • ∑ c∈modes s.1, Gemini.trailC (pitcher o s.2) c (setRuby s.1 c)
lemma words (X: Fields N) : Wort o a R N X= Twah.gold R • ∑ c∈modes a.1, Fock.remove ((pitcher o a.2).lower N (setRuby a.1 c))*create ((pitcher o a.2).upper N c):=by simp_rw [Wort,Pi.smul_apply,Finset.sum_apply]; rfl
lemma dgGroundC (X:Fields N): Wort o a R N X=(-Twah.gold R* Lifted.winding N o* Lifted.winding N o) • dg (goblet N (wrap N o) (upSpin a.2.1) (dnSpin a.2.2) a.1):=by
 let P:Site N × SpinIdx:=(wrap N o,upSpin a.2.1); let Q:Site N × SpinIdx:=(wrap N o,dnSpin a.2.2)
 rw [words,goblet_words]; simp_rw [smul_sum]; refine sum_congr rfl fun i h=>?_
 unfold pitcher Twah.lower Twah.upper basisC Fock.remove; dsimp only; rw [map_smul,map_smul,star_smul,create_put,create_put,Lifted.index, Lifted.index, Matrix.smul_mul,Matrix.mul_smul, show star (Lifted.winding N o)=_ from fee_real (Rush.periods N _)]
 let D:=takeF (Q,setRuby a.1 i); let J:= put (P,i); change _ • (_ • (_ • (D*J)))= _ • (J*D); rw [show D*J= -(J*D) from (eq_neg_of_add_eq_zero_left ((mixed _ _).trans (if_neg ?_)))]; swap
 · intro v; exact dn_half a.2.2 (by rw [show dnSpin a.2.2=upSpin a.2.1 from congrArg (fun t:Single N=> t.1.2) v]; exact up_half _)
 simp only [smul_smul,smul_neg,neg_mul,neg_smul]; congr 2 <;> unfold Lifted.winding <;> ring
lemma audience (R:ℕ): Voice (Wort o a R) (honey o):=by
 constructor
 · rw [← cupArea o a.2]; exact (Passion.weaveSum (modes a.1) _ (fun i _=>Gemini.trail_pass (pitcher o a.2) i (setRuby a.1 i))).haze _
 intro N g u; rw [dgGroundC,dgGroundC,twist_scalar,dg_cov,keeps] -- lhs
end Chalice
end YM.CF.Buffered.Ballad
