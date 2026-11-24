import YM.SU5.Selected.Lantern.Therm
import YM.SU5.Selected.Twirl.Fab
import YM.SU5.Selected.Twirl.Tide
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
-- Wlog one prepared tender. any eventual t foothold s, m on SAME Y.
namespace Tender

-- cyc uniform Gram independent period. Gather `Curtain` all chronological requirements.
variable {A:ℝ}{δ:ℝ} (Ω:ℝ)

-- grant a stipend at physical Mesh. step h divisible by ruler in Fermi units.
def stint (L:Side)(p:ℕ) := p/(8*L.val)+1
def rapids (L:Side)(p:ℕ) := 8*L.val * stint L p
lemma swift (L:Side)(p:ℕ): p< rapids L p∧rapids L p ≤ p+8*L.val:=by
 let S:=8*L.val; have he:0<S:= Nat.mul_pos (by omega) L.property
 have h:= Nat.mod_add_div p S; have ht:= Nat.mod_lt p he; have hw:rapids L p=S*(p/S)+S:=by unfold rapids stint S; ring
 change p<rapids L p ∧ rapids L p≤p+S; omega
structure CloudBank (L:Side)(T:ℝ)(ℓ:ℕ) (E:ℝ) (B:Side) : Prop where
 active : ∃ (G:Side)(b p':ℕ) (w:ℕ), L^ (2:ℕ)= G ∧ p'=folio G T ∧ ∃ (C:ℝ),C ≥ 1 ∧
    let D:= fundD L b; let R:= 10000* C^ (4:ℕ); let J:= Station.tollK (dueW R)
    let η:= tightH D R; let n:=nudge ℓ; let p:=10*p'
    8≤ G.val ∧ n + 2*harbor n p + 100*ℓ ≤ D.val ∧ E=clouds D ∧ J*(clouds D*(2*R+3)) ≤ Real.exp (-2*(rentL D+J)) ∧
       ∃ X Y Z: Coast → Wq p, Crest.Airy.Lift p (rapids B p) X Y ∧ TideFrame (G:=G) n p X Z D w η η C ∧ TideFrame (G:=G) n p Y Z D w η η C -- tune Wq arg type 

#check CloudBank.mk
#print TideFrame.mk
private lemma fusion_f (L G:Side)(u:L.val≥3)(g:G.val≥8)(T:ℝ)(ℓ:ℕ)(B:Side)(h:8*B.val≤ℓ)(t:L^ (2:ℕ)=G):∃ E:ℝ, CloudBank L T ℓ E B:=by
 let n:=nudge ℓ; have hn: n≥4:=by unfold n nudge; omega
 let p':=folio G T; let p:=10*p'
 let k:= rapids B p; have h1:p≤k:= (swift B p).1.le; have h2 : p+k ≤ harbor n p := by have hK:= (swift B p).2; unfold harbor; unfold k n nudge; omega
 obtain ⟨C,hC,K,hk,v⟩:= eros n p k G g h1 hn h2; let A:=C; let R:=10000* A^ (4:ℕ); have hA:1≤A:=by unfold A; linarith
 have hR:1≤R:= one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hA)
 let J:=Station.tollK (dueW R); let D:= fundD L; have ht:Tendsto (fun i=>(D i).val) atTop atTop:=by
    have h(i:ℕ):(D i).val=L.val^i:= by unfold D fundD; rfl -- tune
    simp_rw [h]; exact tendsto_pow_atTop_atTop_of_one_lt (by omega)
 obtain ⟨i,⟨za,zk⟩,w⟩:= ((objectives D ht R J K hR).and (ht.eventually_ge_atTop (n+2*harbor n p+100*ℓ))).exists
 let η:= tightH (D i) R; have hg : 0<η:= mugs hR (D i); have hCp:0<C:=by linarith
 let ε:=min 1 (min (η/4) ((η/2)/(2*C))); have he : 0< ε:= by unfold ε; positivity
 have hy:ε ≤ (η/2)/(2*C):= le_trans (min_le_right ..) (min_le_right ..)
 have hx :=(le_div_iff₀ (by positivity)).1 hy; have hz:ε ≤ η/4:=le_trans (min_le_right ..) (min_le_left ..)
 obtain ⟨l,X,Y,Z,W,V,P⟩:=v (D i) ε he (min_le_left ..)
 have ev:4*ε ≤η:=by linarith only [hz]
 have ej : K* Real.exp (-(1/2))^(D i).val+ε*(2*C) ≤ η:= by change K* _≤η/2 at zk; linarith only [hx,zk];
 refine ⟨_,⟨G,i,p',l,t,rfl,A,hA,g,w,rfl,za,X,Y,Z,W,V.weaker n p le_rfl ej ev,P.weaker n p le_rfl ej ev⟩⟩
lemma breeze (L: Side)(T:ℝ)(ℓ:ℕ)(B:Side)(p:3≤L.val)(w:8*B.val≤ℓ): ∃ E:ℝ, CloudBank L T ℓ E B:= fusion_f L _ p (by change 8 ≤ (L^ (2:ℕ)).val; change 8 ≤ L.val^ (2:ℕ); nlinarith) T ℓ B w rfl
end Tender
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Tender
#print axioms breeze
