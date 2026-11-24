import YM.SatinExist.Pursuit
import YM.SU5.FiniteGaugeData.Stent.Quint
set_option autoImplicit false
set_option maxHeartbeats 370000
noncomputable section
namespace YM.CF.Buffered.Stent
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
open NormedSpace
namespace Rhoda
variable {N P:Side}(G:Ratio N P)(J:ℕ)(hj:4≤J)(k:Odd G.count.val)(e:3≤G.count.val)
private abbrev R:= Patch.mk G.count J hj e k
variable {d:ℕ} (q:LaurentRadius J G.count d) (t:2*d < N.val)
local notation "R"=> R G J hj k e
local notation "Λ"=> G.count
variable (y:Nom N P)(j:SpinIdx) (u:Site N)(s:SU.Slot)
local notation "L"=>LabelSet d
local notation "C" r:max z:max=>cash R (lift r) z
local notation "I" =>Iota G
local notation "A" i:max=>mosaic G true false (tub (brix J G.count)) (unionP y) i (patchQ G ((u,j),s))
include q
private lemma mosaicPrice (i:I): ‖A i‖ ≤ ∑ z∈ LabelSet d, if u=i.1.1+wrap N z then ‖cash (⟨G.count,J,hj,e,k⟩:Patch) (lift i.1.2.1) z‖ else 0:=by
 rw [mosaic_entry G J q]
 let U:=patchQ G ((u,j),s)
 let P':= i.1.2.1
 let S':= ∑ z∈ LabelSet d, if u=i.1.1+wrap N z then ‖C P' z‖ else 0
 let V:= (Fintype.card Lattice.Order:ℝ); have hv:0<V:=by unfold V; positivity
 rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hv).le]; refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_pos.mpr hv).le).trans ((mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>S') ?_) (inv_pos.mpr hv).le).trans_eq ?_)
 swap; · simp_rw [Finset.sum_const,card_univ,nsmul_eq_mul]; exact inv_mul_cancel_left₀ hv.ne' _
 intro o _; rw [sum_eq_single i.1.2]; swap
 · intro j' _ p; exact sum_eq_zero fun k' _=>sum_eq_zero fun z hz=> by rw [drag_entry,if_neg (fun h=> p h.1.symm)]
 swap; · simp
 rw [sum_eq_single U.1.2]; swap
 · intro j' _ p; refine sum_eq_zero fun z hz=>?_ ; rw [drag_entry,if_neg ?_]; exact fun h=> p (congrArg Prod.snd h.2).symm
 swap; · simp
 unfold S'; refine (norm_sum_le ..).trans (sum_le_sum fun z _=>?_); rw [drag_entry]; change ‖if _ = _∧ (u,(0,j)) = (i.1.1+wrap N z, U.1.2) then _ else _‖≤_; split
 next v=>
    have h: u=_:= (congrArg Prod.fst v.2); rw [if_pos h]; simp_rw [norm_mul,Rush.wind,Rush.fee_norm,one_mul]; refine (mul_le_of_le_one_right (norm_nonneg _) ((norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary (SU.matter _).property))).trans ?_
    change ‖tub _ z i.1.2 (0,j)‖≤_; rw [show tub (brix J G.count) z i.1.2 (0,j)=_ from correspondent R ..]; split; rfl; rw [norm_zero]; exact norm_nonneg _
 next h=> rw [norm_zero]; split <;> positivity
-- clock pursuit
private abbrev highQ (M:Male)(i:I):ℝ:= ‖cloth J M G (unionP y) i (patchQ G ((u,j),s))‖
local notation "D" m:max i:max=> highQ G J y j u s m i
lemma clothPrice (M:Male)(i:I): highQ G J y j u s M i ≤ 2*(∑ z∈ LabelSet d, if u=i.1.1+wrap N z then ‖cash (⟨G.count,J,hj,e,k⟩:Patch) (lift i.1.2.1) z‖ else 0):=by
 unfold highQ; rw [cloth_entry]; let W:=patchQ G ((u,j),s); have hl(x:I)(b):‖lobe G b x x‖≤1:= (norm_entry ..).trans (IsStarProjection.norm_le _ (lobe_sq ..))
 refine (norm_add_le ..).trans ?_
 let Z:= ∑ z∈ LabelSet d, if u=i.1.1+wrap N z then ‖cash R (lift i.1.2.1) z‖ else 0
 have he(b):‖lobe G b i i*(A i)* lobe G b W W‖≤ Z:= by
    rw [norm_mul,norm_mul]; exact ((mul_le_of_le_one_right (by positivity) (hl ..)).trans ((mul_le_of_le_one_left (by positivity) (hl ..)).trans (mosaicPrice G J hj k e q y j u s i)))
 rw [two_mul]; exact add_le_add (he true) (he false)
lemma large_sum (M: Male) : (∑ i:I, highQ G J y j u s M i) ≤ 2* (Fintype.card SpinIdx* (Fintype.card SU.Slot:ℝ))*funds (⟨G.count,J,hj,e,k⟩:Patch) := by
 let X(r:Site G.count)(x:Site N):= ∑ z∈LabelSet d, if u=x+wrap N z then ‖C r z‖ else 0
 let Y:ℝ:= Fintype.card SpinIdx* (Fintype.card SU.Slot:ℝ)
 calc
    _ ≤ ∑ i:Iota G, 2 * X i.1.2.1 i.1.1 := sum_le_sum (fun i _=>clothPrice G J hj k e q y j u s M i)
    _ = 2*(Y* ∑ i:Site G.count,∑ z∈ LabelSet d, ‖C i z‖) := by
       rw [←mul_sum]; apply congrArg; simp only [Iota,St,Fintype.sum_prod_type,Finset.sum_const,card_univ,nsmul_eq_mul]
       simp_rw [←mul_assoc, ←mul_sum]
       unfold Y; rw [sum_comm (f:=fun i j=> X j i)]; refine congrArg (fun v:ℝ=>Fintype.card SpinIdx * (Fintype.card SU.Slot:ℝ) * v) ?_ -- tune
       exact sum_congr rfl fun i _=> by unfold X; rw [sum_comm]; refine sum_congr rfl fun z _=>?_ ; rw [sum_eq_single (u-wrap N z)]; rw [sub_add_cancel,if_pos rfl]; intro j _ e; exact if_neg (fun h=> e (eq_sub_of_add_eq h.symm)); simp
    _ ≤ _ := by rw [←mul_assoc]; gcongr; exact Drop.paid_sums R (LabelSet d)
include t
lemma large_local (M:Male)(i:I): highQ G J y j u s M i ≤ 2*Drop.drop (⟨G.count,J,hj,e,k⟩:Patch):=by
 refine le_trans (clothPrice G J hj k e q y j u s M i) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
 by_cases h : ∃ z∈ LabelSet d,u=i.1.1+wrap N z
 · obtain ⟨z,hz,g⟩:=h; rw [sum_eq_single z]; rw [if_pos g]; exact Drop.paid ..
   · intro k g' e
     rw [if_neg (fun h=>e ?_)]
     have h:= add_left_cancel (h.symm.trans g)
     apply wrap_injOn N _ _ h
     all_goals first |(intro j; obtain ⟨p,v⟩:= box_test.mp ((mem_filter.mp hz).1); obtain ⟨p',v'⟩:=box_test.mp ((mem_filter.mp g').1); specialize p j; specialize p' j; specialize v j; specialize v' j; omega)
   exact fun g=>(g hz).elim
 push Not at h; rw [sum_eq_zero]; swap; · exact fun z g=> if_neg (h z g)
 unfold Drop.drop funds; positivity
include hj k e
lemma loan (M:Male): (∑ i:I, highQ G J y j u s M i ^ 2) ≤4* (Fintype.card SpinIdx* (Fintype.card SU.Slot:ℝ)):=by
 refine le_trans (sum_le_sum (g:=fun i:I=> (D M i)*(2*Drop.drop R)) (fun i _=> by rw [pow_two]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact large_local G J hj k e q t y j u s M i)) ?_
 rw [←sum_mul]
 calc
  _ ≤ (2* (Fintype.card SpinIdx* (Fintype.card SU.Slot:ℝ))*funds R)* _:=mul_le_mul_of_nonneg_right (large_sum G J hj k e q y j u s M) (by unfold Drop.drop funds; positivity)
  _ = 4 * _*(funds R* Drop.drop R):=by ring
  _ ≤ _:= mul_le_of_le_one_right (by positivity) (Drop.credit ..)
private abbrev load := 4*((Fintype.card SpinIdx:ℝ)*Fintype.card SU.Slot)
private lemma shelf (M:Male) : ‖trailK (switchG G).symm.toEmbedding (acts (cloth J M G (unionP y)) (basisKet (patchQ G ((u,j),s))))‖≤Real.sqrt load:=by
 apply (Real.le_sqrt (norm_nonneg _) (show 0≤load from by unfold load; positivity)).mpr
 rw [PiLp.norm_sq_eq_of_L2, ← Equiv.sum_comp (switchG G)]; simp_rw [seamK,Equiv.toEmbedding_apply,Equiv.symm_apply_apply,basis_act]
 exact loan G J hj k e q t y j u s M
omit q t hj k e
private lemma helm : ∃ K:ℝ,0<K ∧ ∀ (b:Bool)(Q:Op SU.Slot)(j:SpinIdx), ‖Q‖≤1→ ‖Lock Q b j‖ ≤ K:=by
 choose K hK using fun b:Bool=> fun j:SpinIdx=> ((isCompact_closedBall (0:Op SU.Slot) (1:ℝ)).image (Poleg (b:=b) j).norm).bddAbove -- name
 let Qq:= (∑ b:Bool,∑ i:SpinIdx, |K b i|)
 have ha:0≤Qq:=Finset.sum_nonneg fun _ _=>sum_nonneg fun _ _=>abs_nonneg _
 refine ⟨Qq+1,by positivity,fun b Q i e=> ?_⟩
 exact ((hK b i ⟨Q,mem_closedBall_zero_iff.mpr e,rfl⟩).trans (le_abs_self _)).trans ((le_trans (b:=∑ i:SpinIdx, |K b i|) (single_le_sum (fun i _=> abs_nonneg (K b i)) (mem_univ _)) (single_le_sum (fun b _=> sum_nonneg (f:=fun i:SpinIdx=> |K b i|) (fun i _=>abs_nonneg _)) (mem_univ b))).trans (by change Qq≤Qq+1; linarith))
abbrev allotQ :ℝ:= Classical.choose helm
abbrev spendU := Fintype.card SU.Slot*(allotQ*Real.sqrt load)
lemma spendHi: (0:ℝ) ≤ spendU:=by unfold spendU load; have hh:= helm.choose_spec.1; change 0<allotQ at hh; positivity
include q t hj k e
lemma wave_here (b:Bool)(M:Male)(Q:Op SU.Slot)(he:‖Q‖≤1) : ‖byMode G J Q M y b (basisKet ((u,j),s))‖ ≤ spendU:=by
 rw [byMode_eq,fee_work]
 simp_rw [map_sum,map_smul,basis_shell]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>allotQ*Real.sqrt load) ?_).trans_eq ?_)
 swap; · rw [sum_const,card_univ,nsmul_eq_mul]
 intro i _; rw [norm_smul]; exact mul_le_mul ((norm_entry ..).trans (helm.choose_spec.2 b Q j he)) (shelf G J hj k e q t y j u i M) (norm_nonneg _) (by change 0 ≤ allotQ; exact (le_of_lt helm.choose_spec.1))
#print axioms wave_here
end Rhoda
end YM.CF.Buffered.Stent
