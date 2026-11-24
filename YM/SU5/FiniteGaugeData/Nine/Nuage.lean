import YM.SU5.FiniteGaugeData.Nine.Vole
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N:Side}(o:Cover)
open Brique Mir Phase RP Largo Spire
local notation "Μ"=> Single N
open Fock.Brique
section occ
variable {I:Type*}[Fintype I][LinearOrder I]{S P R T: Finset I}
variable {X Y A B:Op I}
def oasis (A B:Op I)(P:Finset I) := A*cutM P+B*cutM Pᶜ
lemma parkA (p:T⊆ S) : oasis A B S *cutM T=A*cutM T:=by rw [oasis,add_mul,mul_assoc A,cut_meet, inter_eq_right.mpr p,mul_assoc B,cut_air (Sᶜ) T ?_,mul_zero,add_zero]; exact Finset.disjoint_left.mpr fun _ h w=>mem_compl.mp h (p w)
lemma parkB (p:Disjoint S T) : oasis A B S*cutM T=B*cutM T:=by rw [oasis,add_mul,mul_assoc A,cut_air S T p,mul_zero,zero_add,mul_assoc B,cut_meet,inter_eq_right.mpr]; exact fun i v=> mem_compl.mpr fun q=> disjoint_left.mp p q v
lemma stah (A B:Op I)(S:Finset I)(i:I)(z:i∈ S) : acts (oasis A B S) (basisKet i)=acts A (basisKet i):=by simp only [oasis,act_add,act_mul,cut_basis,z,↓reduceIte, Finset.mem_compl, not_true_eq_false,map_zero,add_zero] -- notation
lemma stah2 (A B:Op I)(S:Finset I)(i:I)(z:i∉S): acts (oasis A B S) (basisKet i)=acts B (basisKet i):=by simp only [oasis,act_add,act_mul,cut_basis,z,↓reduceIte, Finset.mem_compl,not_false_eq_true,map_zero,zero_add] -- notation
local notation "E"=>cutM S
local notation "P₀"=>cutM T
local notation "W" => cutM P -- launch block, cert group
variable (S T)(A B)
-- average over sign array, order from ownership syntax
abbrev lodgeP (P: Finset I) : FC I:= star (starMark0 S (oasis A B P) T)
private abbrev mix_P (P:Finset I) := starMark0 S (oasis A B P) T
lemma lapse (P:Finset I)(x:I)(h:∀ j∈ T,x<j) : mix_P S (insert x T) A B P= starBoost S (oasis A B P) x*mix_P S T A B P:= by rw [mix_P,starMark0,column,sort_insert (·≤·) (fun i u=>(h i u).le) (fun v=> lt_irrefl _ (h x v)), List.map_cons,List.prod_cons]; rfl
private lemma star_hi (P:Finset I)(x:I)(p:x∈P): starBoost S (oasis A B P) x= starBoost S A x:=by unfold starBoost; rw [act_mul,stah _ _ _ _ p, ←act_mul]
private lemma star_lo (P:Finset I)(x:I)(p:x∉P): starBoost S (oasis A B P) x= starBoost S B x:=by unfold starBoost; rw [act_mul,stah2 _ _ _ _ p, ←act_mul]
lemma limber (P:Finset I)(x:I)(v:x∉T): mix_P S T A B P=mix_P S T A B (insert x P):=by
 induction T using Finset.induction_on_min with
 | empty=> simp [mix_P,starMark0,column]
 | insert j T h ih=>
    have hh:x∉ T:=fun t=>v (mem_insert_of_mem t)
    rw [lapse S _ A B _ _ h, lapse S _ A B _ _ h, ih hh]; by_cases t:j∈P; · rw [star_hi S A B _ _ t,star_hi S A B _ _ (mem_insert_of_mem t)]
    rw [star_lo S A B _ _ t,star_lo S A B _ _ (by rw [mem_insert]; exact not_or_intro (fun u=> v (mem_insert.mpr (Or.inl u.symm))) t)]
lemma sum_oasis (w:cutM Sᶜ *B = -(cutM Sᶜ*A)): (∑ p∈T.powerset,lodgeP S T A B p)=(2:ℂ)^T.card • (1:FC I):= by
 induction T using Finset.induction_on_min with
 | empty=> rw [powerset_empty,sum_singleton]; simp [lodgeP,starMark0,column]
 | insert x T h ih=>
    let T' := insert x T; have hx:x∉ T:= fun v=>lt_irrefl _ (h _ v); let F(p:Finset I)(V:Finset I):= starMark0 S (oasis A B p) V; let g(p:Finset I):=lodgeP S T A B p; let a:= starBoost S A x; let b:= starBoost S B x; have he:a+b=(2:ℂ)•(1:FC I):=by
       unfold a b starBoost; rw [w,act_neg, map_neg,neg_mul]; module
    have hp(P:Finset I)(v:P⊆ T): lodgeP S T' A B P+ lodgeP S T' A B (insert x P)=g P* star b+g P* star a:=by
       change star (F P _) + star (F (insert x P) _)=_
       change star (mix_P S (insert x T) A B P) +star (mix_P S (insert x T) A B (insert x P))= _; rw [lapse S T A B _ _ h,lapse S T A B _ _ h,← limber S T A B P x hx, star_mul,star_mul, star_hi S A B _ _ (show x∈insert x P from mem_insert_self ..),star_lo S A B _ _ (show x∉ P from fun t=>hx (v t))]

    rw [card_insert_of_notMem hx,pow_succ]; rw [sum_powerset_insert hx]; -- order terms sum then sum? inspect
    rw [←sum_add_distrib]; have h(i)(t:i∈T.powerset):g i *star b+g i*star a=(2:ℂ) • g i:=by rw [←mul_add,add_comm (star _),←star_add, he,star_smul]; simp [Algebra.mul_smul_comm]
    rw [sum_congr rfl (fun x hx=> (hp _ (mem_powerset.mp hx)).trans (h _ hx)),←smul_sum]; unfold g; rw [ih,smul_smul,mul_comm]
variable {A B S T}
lemma starMS (p:P⊆T)(t:T⊆S)(x:Wave I)(v:Sea E x)(h: P₀*A*W=W)(Ht:X*W=A*W): Full (Fock.Brique.Ortho (A * cutM P)) (acts (starMark0 S X T) x):=by
 intro y u; obtain ⟨z,r⟩:= refill (A*W) y; rw [u] at r; let k:=acts E y; have he:P₀*E=P₀:= cut_meet .. |>.trans (congrArg cutM (inter_eq_left.mpr t))
 have hv: y=k+acts ((cutM Sᶜ*X)*P₀) k:=by
    have ht: acts P₀ k=acts W z:=by unfold k; rw [←act_mul,he,←r,←act_mul,←mul_assoc,h]
    rw [show acts _ _=acts (cutM Sᶜ) y from (by rw [act_mul (cutM Sᶜ *X), ht,act_mul,←act_mul X,Ht,r]), dim_cut]; unfold k; rw [act_sub,act_one]; abel
 rw [hv,←act_mul,starM_weave S T X t,act_mul,(wore _ x (cutM_idp _) v) k (Cellar.stanch ..),map_zero]
variable {c:ℝ} (S) (p:P⊆T)(u:T⊆ S)(A B : Op I)
lemma oasis_norm (h:‖A‖ ≤ c)(t:‖B‖≤c)(P:Finset I): ‖oasis A B P‖ ≤ 2*c:= by
 have he (H:Op I)(S:Finset I)(p:‖H‖ ≤ c): ‖H*cutM S‖ ≤ c:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans p)
 exact (norm_add_le ..).trans ((add_le_add (he _ _ h) (he _ _ t)).trans_eq (two_mul c).symm)
lemma lodge_cost [Nonempty I] (c:ℝ) (p:0≤c)(T:Finset I)(P:Finset I)(h:‖A‖≤c)(u:‖B‖≤c):‖lodgeP S T A B P‖ ≤ (1+2*c)^ T.card := (norm_star ..).le.trans (starM_cost S T (oasis A B P) (by positivity) (oasis_norm A B h u P))
#print axioms sum_oasis
end occ
end YM.CF.Window.Pivot
