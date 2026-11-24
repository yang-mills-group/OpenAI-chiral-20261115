import YM.CF.Exa.Blade
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro -- tune
variable (e:ℝ)(N:Side){κ:Type}[TopologicalSpace κ]
abbrev Milli (V:κ→Raw (Chin N) (Single N))(u a:ℝ):Prop:=Vista (badge _) (bail N e) (bail N e) (fun i X=> V i X.val) u a
variable {X:κ→Raw (Chin N) (Single N)}{e' a b z:ℝ}
lemma sail(p:Milli e N X z a):Milli e N (fun i=>pale (X i)) z a:=by
 let f(x:↥(Openc (More N) e)):↥(Openc (More N) e):= ⟨ice x.val,ice_o x.val e x.property⟩; let b:=forum N e
 refine p.impose f ((burnOut.comp continuous_subtype_val).subtype_mk _) (fun g x=>Subtype.ext (icy_g ..)) ?_ ?_
 · intro S x y; change fare S (ice x.val) (ice y.val)/_=_; rw [ice_f]; rfl
 intro g h; exact realigns h f fun V e γ p=> snowy e (fun z=>(γ z).val) p
lemma convert_l (x y:SpinIdx)(V:κ→Op Slot)(K:ℝ)(p:0≤K)(h:Continuous V)(u:∀ i,‖V i‖ ≤ K)(v:∀ i g,mater g*V i= V i*mater g): Milli e N (fun i _=>∑ b:Site N,panel (b,x) (b,y) (V i)) ((Fintype.card Slot)*(Tap.Br a*K)) a:=by
 let F(t:Site N):=(t,x); let Y(t:Site N):=(t,y); let R(t:Site N): Finset (Site (More N)):={node t}; let X(b):= reed (F b) (Y b) K; let A(t:Site N)(i:κ)(_ : Openc (More N) e):=panel (F t) (Y t) (V i)
 have he(i:Site N): pendB (badge _) (bail N e) (bail N e) (A i) (R i) (X i):=by
    constructor
    · intro l; exact panel_ticket (s:=bail N e) (t:=bail N e) (p:=fun g v=>matter (g (node v.1))) (q:=fun g v=>matter (g (node v.1))) (fun _=> rfl) (fun _=> rfl) _ _ _ _ (fun _=>V l) (.single _) (fun k=>show node i∈ R i from mem_singleton_self _) (fun k=>show node i∈ R i from mem_singleton_self _) (fun g x=> (v l (g (node i))).symm) p ((badge _).base (V l)) continuous_const (fun x=>u _) (fun x y=> (by rw [sub_self,norm_zero]; exact mul_nonneg p ((forum N e).pos ..)))
    intro z; apply continuous_matrix; intro a b; unfold A panel; simp only [Matrix.of_apply]; split; exact h.matrix_elem ..; exact continuous_const
 have hv :0 ≤ Br a*K:=mul_nonneg (by unfold Br; positivity) p
 have hx i k l: Branch.rent a (R i)*X i k l=reed (F i) (Y i) (Br a*K) k l:=by simp [R,Branch.rent,Br,X,reed,mul_ite]
 refine Vista.bundle _ (by positivity) R A X he ?_ ?_ _ (fun _ _=>rfl)
 · intro i; simp_rw [hx]; exact wheel F (fun a b h=> congr_arg Prod.fst h) Y _ _ (fun _=> le_rfl) hv _
 intro i; simp_rw [hx]; have hh t l k : reed (F t) (Y t) (Br a*K) l k=reed (Y t) (F t) (Br a*K) k l:=by unfold reed; simp only [and_comm]
 simp_rw [hh]; exact wheel Y (fun a b h=>congr_arg Prod.fst h) F _ _ (fun _=>le_rfl) hv _
lemma barK [Nonempty κ] (V:κ→Op Slot)(K:ℝ)(T:Op SpinIdx)(p:0≤K)(h:Continuous V)(u:∀ i,‖V i‖ ≤ K)(v:∀ i g,mater g*V i= V i*mater g): Milli e N (fun i _=>headW N T (V i)) (wingRent T a * K) a:=by
 have hx(i j:SpinIdx):let c:= T i j; Milli e N (fun x _=> ∑ b:Site N,panel (b,i) (b,j) (c • V x)) ((Fintype.card Slot)*(Br a*(‖T i j‖*K))) a := convert_l e N i j _ _ (by positivity) ((continuous_const (y:=T i j)).smul h) (fun i'=>by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (u i') (norm_nonneg _)) (fun i g=> by rw [Matrix.mul_smul,Matrix.smul_mul, v])
 have he(z:Op Slot):headW N T z=∑ i:SpinIdx,∑ j:SpinIdx,∑ b:Site N, panel (b,i) (b,j) (T i j • z):=by ext ⟨⟨x,i⟩,b⟩ ⟨⟨y,j⟩,l⟩; change jump (Equiv.refl (Site N)) (fun _=>T⊗ₖ z) (x,i,b) (y,j,l)=_; rw [jump_apply]; by_cases h:x=y <;> simp [panel,h,Matrix.sum_apply,Prod.mk_inj,ite_and] <;> grind
 simp_rw [he]; apply Vista.tall (Vista.markL _ Finset.univ _ (fun i _=> Vista.markL _ Finset.univ _ (fun j _=>hx i j))); unfold wingRent; simp_rw [sum_mul, mul_assoc]; rfl
end YM.CF.Exa
