import YM.SU5.Selected.Lantern.Card
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
lemma objectives {ι:Type*}{F:Filter ι} (D:ι→Side) (t:Tendsto (fun i=>(D i).val) F atTop)(R J K:ℝ)(p:1≤R) :
    ∀ᶠ i in F, J*(clouds (D i)*(2*R+3)) ≤ Real.exp (-2*(rentL (D i)+J)) ∧ K* Real.exp (-((1:ℝ)/2))^(D i).val ≤ tightH (D i) R/2 := by
 let x:= fun i=>(D i).val; have hp(c:ℝ)(p:c<0)(d:ℝ): Tendsto (fun i=> Real.exp (x i*c)*d) F (𝓝 0):=by
    simpa only [zero_mul,Function.comp_apply,x] using (Real.tendsto_exp_atBot.comp (((tendsto_natCast_atTop_atTop.comp t).atTop_mul_const_of_neg p))).mul_const d -- names tune
 let T:=2*R+3; let b:=Real.exp (-2*J); have hR:0<R:=(by linarith)
 filter_upwards [(hp (-(1/100)+2/1000) (by norm_num) (T*J)).eventually (ge_mem_nhds (show 0<b from Real.exp_pos _)), (hp (-(1/2)+3/100) (by norm_num) K).eventually (ge_mem_nhds (show (0:ℝ)<1/(100*R^2)/(100*R^4)/2 by positivity))] with i e g
 unfold clouds tightH levyH at *
 -- clouds may fail occurrence due nested `unfold` ; syntax
 constructor
 · let n:=(D i).val; unfold rentL; rw [← Real.exp_nat_mul, show (-(2:ℝ)*( (n:ℝ)/1000+J)) = ((n:ℝ)*(-(1/100)) - (n:ℝ)* (-(1/100)+2/1000))+ -2*J by ring, Real.exp_add]; -- ex
   nth_rw 1 [show (↑(D i).val:ℝ)*-(1/100) =(↑(D i).val:ℝ)* (-(1/100)+2/1000)+ (( (n:ℝ)*(-(1/100))) - (n:ℝ)* (-(1/100)+2/1000)) by unfold n; ring]; rw [Real.exp_add]
   refine ( (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left e (Real.exp_pos _).le) ) -- `i`
   unfold x T; ring
 rw [← Real.exp_nat_mul,clouds,← Real.exp_nat_mul]; rw [←Real.exp_nat_mul]; let a:ℝ:= ↑(D i).val* (-(1/2)+3/100); let u:ℝ:= ↑(3:ℕ)* (↑(D i).val* (-(1/100):ℝ)); change _ ≤ Real.exp u /_ /_ /2; rw [show (↑(D i).val:ℝ)* (-(1/2))= a+u by unfold a u; push_cast; ring,Real.exp_add];
 calc _ = Real.exp u *(Real.exp a*K) := by ring
      _ ≤ Real.exp u * (1/(100*R^2)/(100*R^4)/2) := mul_le_mul_of_nonneg_left g (Real.exp_pos _).le
      _ = _:=by ring -- denominators
-- C bound chosen BEFORE D, pay choose folio n before $C. witness same Fire ordering.
-- Width parameter ℓ caller uses addgap bound through Supplier.
def nudge (ℓ:ℕ):= 100*(ℓ+1)
def fundD (L:Side)(b:ℕ):= L^b -- maybe elaboration
structure Curtain (L:Side)(T:ℝ)(ℓ:ℕ) (E:ℝ) : Prop where
 active : ∃ (G:Side)(b p':ℕ) (w:ℕ), L^ (2:ℕ)= G ∧ p'=folio G T ∧ ∃ (C:ℝ),C ≥ 1 ∧
    let D:= fundD L b; let R:= 10000* C^ (4:ℕ); let J:= Station.tollK (dueW R)
    let η:= tightH D R; let n:=nudge ℓ; let p:=10*p'
    8≤ G.val ∧ n + 2*harbor n p + 100*ℓ ≤ D.val ∧ E=clouds D ∧ J*(clouds D*(2*R+3)) ≤ Real.exp (-2*(rentL D+J)) ∧
       ∃ X Z: Coast → Wq p, Frame (G:=G) n p X Z D w η η C -- tune Wq arg type 

#check Curtain.mk
#print Frame.mk
private lemma costs (L G:Side)(u:L.val≥3)(g:G.val≥8)(T:ℝ)(ℓ:ℕ)(t:L^ (2:ℕ)=G):∃ E:ℝ, Curtain L T ℓ E:=by
 let n:=nudge ℓ; have hn: n≥4:=by unfold n nudge; omega
 let p':=folio G T; let p:=10*p'
 obtain ⟨C,hC,K,hk,v⟩:= looked n p G g hn; let A:=C+1; let R:=10000* A^ (4:ℕ); have hA:1≤A:=by unfold A; linarith
 have hR:1≤R:= one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hA)
 let J:=Station.tollK (dueW R); let D:= fundD L; have ht:Tendsto (fun i=>(D i).val) atTop atTop:=by
    have h(i:ℕ):(D i).val=L.val^i:= by unfold D fundD; rfl -- tune
    simp_rw [h]; exact tendsto_pow_atTop_atTop_of_one_lt (by omega)
 obtain ⟨i,⟨za,zk⟩,w⟩:= ((objectives D ht R J K hR).and (ht.eventually_ge_atTop (n+2*harbor n p+100*ℓ))).exists
 let η:= tightH (D i) R; have hg : 0<η:= mugs hR (D i); let ε:=min 1 (min (η/2) ((η/2)/(2*C+1))); have he : 0< ε:= by unfold ε; positivity
 have hy:ε ≤ (η/2)/(2*C+1):= le_trans (min_le_right ..) (min_le_right ..)
 have hx :=(le_div_iff₀ (by positivity)).1 hy; have hz:ε ≤ η/2:=le_trans (min_le_right ..) (min_le_left ..)
 obtain ⟨l,X,Z,V⟩:=v (D i) ε he (min_le_left ..)
 refine ⟨_,⟨G,i,p',l,t,rfl,A,hA,g,w,rfl,za,X,Z,V.late,V.early,?_⟩⟩ -- lighting tune
 apply V.ticket.mono; rintro M h N v _ _ x g; obtain ⟨x₀,z₀,h',v'⟩:=h N x g; change K* _≤ η/2 at zk; exact ⟨x₀,z₀,h'.trans (show _ ≤ η by linarith only [zk,hx]),v'.trans (by change _≤η; linarith only [hz])⟩
lemma curtain (L: Side)(T:ℝ)(ℓ:ℕ)(p:3≤L.val): ∃ E:ℝ, Curtain L T ℓ E:= costs L _ p (by change 8 ≤ (L^ (2:ℕ)).val; change 8 ≤ L.val^ (2:ℕ); nlinarith) T ℓ rfl
end Tender
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Tender
#print axioms curtain
