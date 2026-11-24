import YM.SU5.FiniteGaugeData.Nine.Sons
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
open Fock.Brique
variable (k:ℕ)(M:Male)(g:SU.Slot) {h w:ℕ}{P': Finset (Single N)} {T:Support (More N)}(S:Finset (Site N))
local notation "F"=> funde k M N 1
local notation "D"=> Θ N (3:SpinIdx) g
local notation "U"=> Θ N (0:SpinIdx) g
local notation "Τ"=> cutM (U)
local notation "Η"=> cutM (D)
local notation "W"=> preF k M N g
local notation "L"=> (toolP k M N)
local notation "X"=> piQu o N L
variable (T : Support (More N)){v c:ℝ}
section choose
variable {T}
-- Gram.Prescribes two.
local notation "Σ"=> cutM (peas g S)
local notation "P"=> cutM (volts g S)
local notation "Ξ"=> (1-emU k M g S)⁻¹
variable (W0:IsUnit (1-emU k M g S))
def kalem := preF k M N g*(1-emU k M g S)⁻¹* P
def ralem := -(X * Η * L *(1-emU k M g S)⁻¹*P)
local notation "A₀"=> kalem k M g S
local notation "B₀"=> ralem o k M g S
include W0
lemma pins_A : cutM (peas g S) * (kalem k M g S)= P:= by
 have he:Σ*W*Σ= Σ*(1-emU k M g S):=by rw [show emU k M g S=Σ*(1-W)*Σ from (jewel_c ..).symm,mul_sub Σ, ← mul_assoc Σ (Σ*(1-W)),←mul_assoc Σ Σ,show Σ*Σ=Σ from (cutM_idp _).1,mul_sub Σ,mul_one,sub_mul Σ,show Σ*Σ=Σ from (cutM_idp _).1]; abel
 have hv:= voltage g S; unfold kalem; rw [mul_assoc (W)]; nth_rw 1 [←hv]; rw [←mul_assoc Ξ, ←(excite k M g S W0).eq]; -- tune align
 rw [←mul_assoc,←mul_assoc,←mul_assoc,he]; rw [mul_assoc Σ,(live W0).1,mul_one,hv]
omit W0
lemma kalem_lower (p:1≤k)(v:Aptitude k N): cutM (Tset N)ᶜ*(A₀) = Η*(A₀):=by
 unfold kalem preF; have he:= low_sweep k M p v g; simp only [←mul_assoc]; rw [he]
lemma ralem_lower (p:1≤k)(v:Aptitude k N): cutM (Tset N)ᶜ*(B₀)= -(cutM (Tset N)ᶜ*A₀):=by unfold ralem kalem preF; rw [mul_neg]; simp only [←mul_assoc]; rw [← (low_agree o k M p v g)]
lemma ralem_upper (p:1≤k)(v:Aptitude k N): cutM (Θ N (0:SpinIdx) g)*(kalem k M g S)= cutM (Θ N 0 g)*(ralem o k M g S):=by
 unfold ralem kalem preF; rw [mul_neg]; simp only [←mul_assoc]; rw [tap_agree o k M p v g,neg_mul,neg_mul,neg_mul]
lemma linalg {X_ Y_:Op Μ} (S T:Finset Μ)(p:S⊆ T)(x:cutM T*X_ = cutM T*Y_): cutM S*X_=cutM S*Y_:=by nth_rw 1 2 [← (show cutM S*cutM T=cutM S from (cut_meet ..).trans (congrArg cutM (inter_eq_left.mpr p)))]; rw [mul_assoc,x,mul_assoc]
include W0
lemma gap_paid : P*(kalem k M g S)=P:=by nth_rw 1 [← (show P*Σ=P from (cut_meet ..).trans (congrArg cutM (inter_eq_left.mpr (peas_more ..))))]; rw [mul_assoc,pins_A k M g S W0,show P*P=P from (cutM_idp _).1]
lemma pins_B (p:1≤k)(v:Aptitude k N): P*(ralem o k M g S)=P:= (linalg _ _ (show volts g S⊆ Θ N 0 g from inter_subset_left) (ralem_upper o k M g S p v).symm).trans (gap_paid k M g S W0)
local notation "c₁"=> cutM (modesIn N T)
omit W0
-- chop both at T. lower agree exact orientation negative. 
def localP (T:Support (More N)):=cutM (modesIn N T) *kalem k M g S
def localM (T:Support (More N)):= cutM (modesIn N T) * ralem o k M g S
local notation "Q₀"=> localP k M g S T
local notation "Q₁"=> localM o k M g S T
lemma same_dual (p:1≤k)(v:Aptitude k N): cutM (Tset N)ᶜ * (localM o k M g S T)= -(cutM (Tset N)ᶜ*(localP k M g S T)):=by unfold localM localP; rw [←mul_assoc,(hat_cut ..).eq,mul_assoc,ralem_lower o k M g S p v,mul_neg,←mul_assoc, ←(hat_cut ..).eq,mul_assoc] -- orientation
include W0
variable (p:1≤k)(e:Aptitude k N)
include p e
lemma Peaked (u:S.image node⊆T): cutM (peas g S)*localP k M g S T=P ∧ P * localM o k M g S T=P ∧ P*localP k M g S T=P:=by
 have hw : peas g S⊆ modesIn N T:=by unfold peas; rw [shroom]; exact Subset.trans inter_subset_right (modes_monotone u)
 have hv : Σ*c₁=Σ:=(cut_meet ..).trans (congrArg cutM (inter_eq_left.mpr hw)); have ht:P*c₁=P:= (cut_meet ..).trans (congrArg cutM (inter_eq_left.mpr ((peas_more ..).trans hw)))
 unfold localM localP; simp_rw [← mul_assoc,hv,ht, gap_paid k M g S W0,pins_A k M g S W0,pins_B o k M g S W0 p e,and_self]
variable (L0:0<v)(v0:‖emU k M g S‖ ≤1-v)
include v0 L0
lemma diamond_cost : ‖W * (1-emU k M g S)⁻¹‖ ≤ v⁻¹ ∧ ‖X*Η*L* (1-emU k M g S)⁻¹‖ ≤ v⁻¹:= by
 have he:=moneyF k M g S W0 v0 L0; let h0:= (show ‖L‖ ≤1 from (tool_proj k M p).norm_le L); let v':=(show ‖X‖ ≤1 from (pi_norm o ..).trans_le h0)
 have hx (X_ Y:Op Μ)(e: ‖X_‖ ≤1){c:ℝ}(y:‖Y‖≤c): ‖X_*Y‖ ≤ c:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) e).trans y)
 exact ⟨hx _ _ (hx _ _ (hx _ _ h0 ((cutM_idp _).norm_le Η)) h0) he, hx _ _ (hx _ _ (hx _ _ v' ((cutM_idp _).norm_le Η)) h0) he⟩ -- bind P? W shadow
lemma cost_here : ‖localP k M g S T‖ ≤ v⁻¹ ∧ ‖localM o k M g S T‖ ≤ v⁻¹:=by
 have he(Y:Op Μ)(x:‖Y‖ ≤ v⁻¹): ‖c₁ *(Y*P)‖ ≤ v⁻¹:= le_trans (norm_mul_le ..) ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans x)))
 exact ⟨he _ (diamond_cost o k M g S W0 p e L0 v0).1,(by unfold localM ralem; rw [mul_neg,norm_neg]; exact he _ (diamond_cost o k M g S W0 p e L0 v0).2)⟩ -- WA argument order
-- cost leak tail. 
local notation "B"=>piQu o N (funde k M N 1)
omit W0 p e L0 v0 in
private lemma Op_F {I:Type*}[Fintype I][DecidableEq I]{A U' G Q J:Op I} (u:U'*A=0)(p: Q*G=G)(V:‖U'‖ ≤1)(K:‖(1-J)*A*Q‖ ≤ c)(W':‖G‖ ≤ v) : ‖U'*(J*(A*G))‖ ≤ c*v:=by
 have hx:U'*(A*G)=0:=by rw [←mul_assoc,u,zero_mul]
 rw [show U'*(J*(A*G))= -(U'*((1-J)*A*Q*G)) from ?_,norm_neg]; swap; · rw [mul_assoc ((1-J)*A),p,mul_assoc (1-J),sub_mul, one_mul, mul_sub, hx,zero_sub,neg_neg]
 exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) V).trans ((norm_mul_le ..).trans (mul_le_mul K W' (norm_nonneg _) ((norm_nonneg _).trans K))))
omit W0 p e L0 v0 in
private lemma shrinkF {A U' G:Op Μ}(t:Liquid (2*w) A (opt c))(q:Lattice.halo (2*w) (S.image node)⊆ T)(u: U'*A=0)(v₁: ‖U'‖ ≤1) (V₁:‖G‖ ≤v⁻¹)(hx₀: cutM (peas g S)*G*P=G*P): ‖U'*(cutM (modesIn N T)*(A*G * P))‖ ≤ opt c*v⁻¹:= by
 rw [mul_assoc A]; let Q:=cutM (peas g S); let J:= modesIn N T; have hz: ‖(1-cutM J)*A*Q‖≤ opt c:= by rw [←dim_cut]; exact liq_leak (S:=peas g S) t q (by rw [peas,shroom]; exact inter_subset_right)
 apply Op_F u ((mul_assoc (cutM (peas g S)) G P).symm.trans hx₀) v₁ hz; exact (norm_mul_le G P).trans ((mul_le_of_le_one_right (norm_nonneg G) ((cutM_idp _).norm_le P)).trans V₁)
private lemma loss {A U':Op Μ}(t:Liquid (2*w) A (opt c))(q:Lattice.halo (2*w) (S.image node)⊆ T)(u: U'*A=0)(v₁: ‖U'‖ ≤1) : ‖U'*(cutM (modesIn N T)*(A*(1-emU k M g S)⁻¹ * P))‖ ≤ opt c*v⁻¹:= by
 exact shrinkF g S t q u v₁ (moneyF k M g S W0 v0 L0) (show Σ*Ξ*P=Ξ*P from (by rw [(excite k M g S W0).eq,mul_assoc,voltage]))
lemma lossUse (x:Liquid w (funde k M N 1) c)(q:Lattice.halo (2*w) (S.image node)⊆T): ‖(funde k M N 1) *(Q₀)‖ ≤ opt c*v⁻¹∧‖(piQu o N (funde k M N 1))*(Q₁)‖ ≤opt c*v⁻¹:=by
 let t:= PeakP_pro (N:=N) k M p; obtain ⟨u',v'⟩:=ort_Flights o k M g x p e; have h':‖F‖ ≤1:= t.norm_le _; have hX: F*L=0:= Porth t; refine ⟨ loss k M g S W0 p e L0 v0 u' q ?_ h',?_⟩
 · unfold preF; rw [←mul_assoc,←mul_assoc,hX,zero_mul,zero_mul]
 unfold localM ralem; rw [mul_neg,mul_neg,norm_neg]; refine loss k M g S W0 p e L0 v0 v' q ?_ ((twist_norm ..).trans_le h'); rw [←mul_assoc,←mul_assoc,piQu, piQu, ←map_mul,hX,map_zero,zero_mul,zero_mul] -- tactic parse N
#print axioms lossUse
end choose
section local_row
open Function
variable (W0:IsUnit (1-emU k M g S)) (p:1≤k)(e:Aptitude k N)(x:S.image node⊆ T)
include W0 p e x
 include o
lemma gap_above {σ:Window.Family} (g0:family g= σ)(v:Ket Μ):withinM (lumen σ (T\S.image node)) (acts (cutM (Tset N)ᶜ*localP k M g S T) v) := by
 let Q:= cutM (Tset N)ᶜ; let H:= localP k M g S T; let Z:= cutM (modesIn N T); let P':= cutM (peas g S)
 have ht: Q*H=Η*H:=by unfold H localP; change Q*(Z*_)= Η*(Z* _); rw [←mul_assoc,(hat_cut ..).eq,mul_assoc,show Q*_=_ from kalem_lower k M g S p e, ←mul_assoc Z, (hat_cut ..).eq,mul_assoc] -- syntax
 let J:= Q*H; let B':= volts g S; let y:= acts J v
 have hx: withinM (modesIn N T) y:=by unfold y J withinM; rw [←act_mul, ←mul_assoc,(hat_cut ..).eq,mul_assoc, show Z*H=H from ?_]; unfold Z H localP; rw [←mul_assoc,(show cutM _*cutM _= _ from ((cutM_idp (modesIn N T)).1 : _=_))] -- W proof
 have hz: withinM D y:=by unfold y J withinM; rw [ht,←act_mul,←mul_assoc,(show Η*Η=Η from (cutM_idp _).1)]
 have hk(i: Μ)(t:i∈D): i∈ (Tset N)ᶜ∧family i.2=σ :=by
    obtain ⟨⟨t',v⟩,w⟩:= i; simp [Θ,loci] at t -- shadow t (warning)
    refine ⟨mem_compl.mpr (mt (grade_one ..|>.mp) ?_), ?_⟩; · rw [←t.1]; decide
    change family w=_; rw [←t.2,g0]
 have hl:B'⊆Tset N:= fun i v=> (grade_one ..).2 ((mem_singleton.mp (mem_product.mp (mem_product.mp (mem_inter.mp v).1).1).2).symm ▸ (by decide : (0:SpinIdx)∈ plusHalf))
 have h₀:P'*J=0:=by unfold J; rw [←mul_assoc,(hat_cut ..).eq,mul_assoc, (show P'*H=cutM B' from (Peaked o k M g S W0 p e x).1), (show Q*cutM B'=0 from cut_air _ _ (disjoint_left.mpr (fun _ t q=> (mem_compl.mp t) (hl q))))] -- include o
 change withinM _ y; apply (within_test ..).2; intro i w; by_cases t:i∈D
 · have he:= hk i t; by_cases u:i∈modesIn N T; swap; · exact (within_test ..).1 hx _ u
   have hz:i∈peas g S:=mem_inter.mpr ⟨mem_union.mpr (Or.inl t), (by rw [shroom, modes_at]; contrapose! w; exact (is_lumen ..).2 ⟨mem_compl.mp he.1, he.2,mem_sdiff.mpr ⟨(modes_at ..).mp u,w⟩⟩ )⟩; have hp: acts (cutM (peas g S)) y=0:=by unfold y; rw [←act_mul,h₀,act_zero] -- act_zero (on operator)
   have hh:=congrArg (fun x:Ket Μ=> x.ofLp i) hp; rwa [cut_apply, if_pos hz] at hh
 exact (within_test ..).1 hz _ t
end local_row
end YM.CF.Window.Pivot
