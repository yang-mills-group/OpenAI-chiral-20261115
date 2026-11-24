import YM.CF.Buffered.Discourse
/-!
# Stencil overlay. Use padded support to cover the coat (entire decorated exterior
 hopping image within the first block). Then on those nodes equality over the
 addressed independent momenta (same periods pullback). Rescale only as power count.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 19000
noncomputable section
namespace YM.CF.Buffered.Mail
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson Branch
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Vale Skye Stencil
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid Push.GridApprox Tenant Laurent Bloch Next.Free Fir Peaks Scree Drapes Tap Dial Reflect Window
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K V C F k t p v N P D M B B' l c f: Side} {G:Gauge} {S:Patch}
lemma v_branch (A:Planck N P D){x:Site N}(g: node x∈blockF (gauge_plan A) 0):∃ y:Site P, x=pointO A 0 y:=by
 let y:=(slump A).cut x; have he:(slump (gauge_plan A)).cut (node x)=node y:=by
    nth_rw 1 [←Rush.nat_true x]; rw [node_of,show (slump _).cut _=wrap (More P) _ from Macrame.branch ..]; unfold y; nth_rw 2 [← Rush.nat_true x]; rw [show (slump _).cut _=wrap P _ from Macrame.branch ..,node_of]
 refine ⟨y,(Tenant.needle ?_).symm⟩; rw [modes_step,←he]; exact restep _ 0 g
lemma visitor (A:Planck N P D){x : Single N}(g: node x.1.1∈blockF (gauge_plan A) 0): x∈lows (modeO A 0):= by obtain ⟨⟨x,a⟩,l⟩:=x; obtain ⟨y,h⟩:= v_branch A g; exact Finset.mem_map.mpr ⟨((y,a),l),mem_univ _,congrArg (fun z=>((z,a),l)) h.symm⟩
variable (A:Planck N P D)(A':Planck F f D)
local notation "g" => modeO A 0
local notation "f'" => modeO A' 0
local notation "h" => pointO A 0
variable (J:Planck (More N) B' k)(E:Planck (More P) B' l)
variable {ℓ:F.val=N.val*S.L.val}{d:f.val=P.val*S.L.val}{w C:ℕ}
variable (j:ℕ)(Q:Op SU.Slot)(M:Male)(H:LaurentRadius j S.L C)(L:2*C+1≤w)
local notation "s" => decreed ℓ
local notation "d'"=> decreed d
local notation "t" => nearX (ℓ:=ℓ) (d:=d) A
local notation "N₀" => wallZ J 0 w
local notation "P₀" => wallZ E 0 w
local notation "Y" => Iota (decreed d)
local notation "Z" => Iota (decreed ℓ)
-- numeric fit by paying gauge widths later
variable (u:padded (decreed ℓ) (wallZ J 0 w) (clothRadius S.L C) ⊆ blockF (gauge_plan A') 0)

lemma pays (b:Bool)(x:Ket (Single P)): coat (patchQ s) (acts (feeL b N Q) (coat g x))=coat t (coat (patchQ d') (acts (feeL b P Q) x)):=by
 rw [←fee_equal]; let z:= acts (feeL b P Q) x; nth_rw 1 2 [←basis_expand (acts (feeL b P Q) x)]; simp_rw [map_sum,map_smul,basis_shell]; rfl
include L in
lemma sec( a:Single P)(v:a∈modesIn P (wallZ E 0 w)): modeO A 0 a∈modesIn N (wallZ J 0 w):=by
 obtain ⟨⟨k,s'⟩,v'⟩:=a; rw [modes_at]; rw [modes_at] at v; change node (pointO A 0 k)∈_; rw [modes_step]; exact inside_to (gauge_plan A) E J (by omega) v
include u H L
variable (U:Pane f)(V:Pane P)(b:Bool)
set_option quotPrecheck false
local notation "Kq" => unionP (show Nom N F from (weave (gauge_plan A') (show Config SU.group _ from U),weave (gauge_plan A) (show Config SU.group _ from V)))
local notation "Lq" => (show Nom N F from (weave (gauge_plan A') (show Config SU.group _ from U),weave (gauge_plan A) (show Config SU.group _ from V)))
local notation "K'"=> unionP (show Nom P f from (U,V))
lemma mode_equal (i:Single P)(v:i∈modesIn P P₀): byMode s j Q M Lq b (basisKet (g i))= coat f' (byMode d' j Q M (show Nom P f from (U,V)) b (basisKet i)) := by
 apply PiLp.ext; intro y
 by_cases p:y∈ lows f'; swap
 · rw [basin _ _ _ p]; have he:= mode_support s j Q M S.odd_side (wallZ J 0 w) H (z:=Lq) (within_basis _ (g i) (sec A J E L i v)) b; exact (within_test ..).1 he y (fun e=>p (visitor A' (u ((modes_at ..).1 e))))
 obtain ⟨l',hv,rfl⟩:= Finset.mem_map.mp p; nth_rw 2 [←seamK]; rw [trails]; obtain ⟨l,rfl⟩:= (switchG d').surjective l'
 let z:= coat (patchQ d') (acts (feeL b P Q) (basisKet i))
 rw [← switches (ℓ:=ℓ) A A',byMode_eq,byMode_eq, ← basis_shell _ i, pays A Q (d:=d) (ℓ:=ℓ)]; simp only [seamK,Equiv.toEmbedding_apply,Equiv.symm_apply_apply, act_at]
 let x(k: Z):= Peaks.cloth j M s Kq (t l) k * (coat t z).ofLp k; change ∑ k,x k= _
 calc
  _=∑ k∈lows t,x k:= (Finset.sum_subset (subset_univ _) (fun i _ v=> by unfold x; rw [basin _ _ _ v,mul_zero])).symm
  _=∑ k:Y,x (t k):= sum_map ..
  _=_:= sum_congr rfl fun k _=> by
    unfold x; rw [←seamK,trails]; by_cases p_:z.ofLp k=0; · change _*z.ofLp k= _*z.ofLp k; rw [p_,mul_zero,mul_zero]
    obtain ⟨ℓ',-,hx⟩:= Finset.mem_map.mp (show k∈ lows (patchQ d') from (by by_contra Y'; exact p_ (basin _ _ _ Y'))); subst k; rw [scurf A A' U V l (patchQ d' ℓ') j E L M H]
    by_contra v'; apply p_; unfold z; rw [←seamK,trails]; exact (within_test ..).1 (within_fee Q P₀ (within_basis _ _ v) b) ℓ' (fun k=>v' ((modes_at ..).1 k))
omit u H L
-- subFine
open Reed (Fine think)
private lemma seed_move (i: Single P): into g ((think (Tset P)).term i)=(think (Tset N)).term (modeO A 0 i):=by
 have ht:g i∈ Tset N ↔ i∈ Tset P:= (mem_Tset ..).trans (mem_Tset ..).symm -- tune
 unfold think; dsimp only; split_ifs with v p q; all_goals simp_all [put_in,take_in] -- tune
lemma enlarged {b:Bool}{F:FC (Single P)} (v:Fine (Tset P) (modesIn P P₀) b F): Fine (Tset N) univ b (into g F):=by
 induction v with
 | one=> rw [map_one]; exact Fine.one
 | empty=>rw [map_zero]; exact Fine.empty _
 | scale _ _ ih=>rw [map_smul]; exact ih.scale _
 | add _ _ p q=>rw [map_add]; exact p.add q
 | grow _ _ p q=>rw [map_mul]; exact p.grow q
 | seed i v'=>rw [seed_move]; exact Fine.seed _ (mem_univ _)
include u H L
lemma stitched {b:Bool}{W:FC (Single P)}(v:Fine (Tset P) (modesIn P P₀) b W): subF s j Q M S.odd_side Lq (into g W)=into f' (subF d' j Q M S.odd_side (show Nom P f from (U,V)) W):=by
 induction v with
 | one=>rw [map_one,sub_one,sub_one,map_one]
 | empty=>rw [map_zero,map_zero,map_zero,map_zero]
 | scale _ _ ih=>rw [map_smul,map_smul,map_smul,map_smul,ih]
 | add _ _ p q=>rw [map_add,map_add,map_add,map_add,p,q]
 | grow a b p q=>rw [map_mul,sub_mul _ _ _ _ _ _ (enlarged A E a) (enlarged A E b),sub_mul _ _ _ _ _ _ a b,map_mul,p,q]
 | seed i v'=>
   have ht:g i∈ Tset N ↔ i∈ Tset P:= (mem_Tset ..).trans (mem_Tset ..).symm; by_cases w':i∈ Tset P
   · rw [show (think (Tset P)).term i=put i from if_pos w',put_in,sub_put _ _ _ _ _ _ i w',sub_put _ _ _ _ _ _ _ (ht.2 w'),into_create]; exact congrArg _ (mode_equal A A' J E j Q M H L u U V true i v')
   rw [show (think (Tset P)).term i= -takeF i from if_neg w',map_neg,map_neg,map_neg,map_neg,take_in,sub_take _ _ _ _ _ _ _ w',sub_take _ _ _ _ _ _ _ (fun k=> w' (ht.1 k)),into_remove]; rw [mode_equal A A' J E j Q M H L u U V false i v']
end YM.CF.Buffered.Mail
#print axioms YM.CF.Buffered.Mail.stitched
