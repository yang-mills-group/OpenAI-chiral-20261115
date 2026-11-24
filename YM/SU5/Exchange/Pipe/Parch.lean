import YM.SU5.Exchange.Pipe.Reach
import YM.CF.Swell.Pod
import YM.CF.Hove.Prune
import YM.SU5.Exchange.Pilot.Herb
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open SU Prism Tap Levier Thera Moto Oath Font Haro
variable {N:Side}
-- Help extending a path coupon. vary contacts and root but NOT tilt rate per chip etc
lemma Suite.widen {d:ℝ}{A B:Sa N}{F:Raw (Openc (More N) d) (Single N)}{C:Toll (Single N)}(f:Suite (badge _) (bail N d) (bail N d) A C F)(p:A⊆B)(v:C≠0→Grove (terr _) B): Suite (badge _) (bail N d) (bail N d) B C F:=by
 by_cases h:C=0; swap; · exact ⟨⟨f.frame,fun i j=> Expo.weaken (f.expo i j) p (v h)⟩,f.fuel⟩
 have H:F=0:=by
    funext x; ext i j; apply norm_le_zero_iff.mp; exact ((f.expo i j).bounded _).trans_eq (by rw [h]; rfl)
 rw [H,h]; exact Suite.free _
-- general retarget cost exponential with angular tokens still at same Scale. burn root-placement, doesn't need coverN yet
variable {ι:Type*}[Fintype ι]{o o':Seat N}{X:SOp N}{a b c v d e:ℝ}{J:SOp N}
lemma soak_tr (p:Soak o X a v d)(h:0 ≤ a) : Soak o' X a (Real.exp (a*(4*(separation o o':ℝ)+1))*v) d:=by
 obtain ⟨F,W,x,u,P,g⟩:=p
 let L:=shiftH o o'; let S:=traceP o L; have hs:(S.card:ℝ) ≤ 4*(separation o o':ℝ)+1:=by exact_mod_cast (trace_k o L|>.trans (add_le_add_left (short o o') _))
 have hx:o'∈ S:=by simpa only [L,S,stopH o o'] using trace_last o (shiftH o o') -- simp backwards infinite
 refine arm_v (o:=o') (fun i:Sa N=> i∪S) F W (fun i=> Suite.widen (x i) subset_union_left (fun p'=>?_)) ?_ (fun i t=> False.elim (t (mem_union_right i hx))) g
 · have hp : o∈ i:=by contrapose! p'; exact u i p'
   obtain ⟨k,j,t⟩:∃ k j, W i k j≠0:=by by_contra! h; exact p' (funext fun x=>funext fun y=>h x y)
   exact ((x i).expo k j |>.triggered t).1.unite (trace_g o L) hp (trace_source ..)
 apply le_trans _ (mul_le_mul_of_nonneg_left P (Real.exp_pos _).le); rw [mul_sum]; apply sum_le_sum; intro i _; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right; swap; · exact sum_nonneg fun i' _=> sum_nonneg fun j _=>(x i).nonn _ _
 unfold Branch.rent; rw [←Real.exp_add,←mul_add]; refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ h); have hp: ↑((i ∪ S).card)≤ (i.card:ℝ) + S.card:=by exact_mod_cast Finset.card_union_le i S
 exact hp.trans (by linarith)
lemma soak_row (p:Soak o X a v d)(q:Soak o' J a b d) (h:0 ≤ a) (g:0 ≤ e)(k:e ≤ a) : Soak o (fun x=> X x*J x) (a-e) (Real.exp (-e*separation o o')*(2*(v*b))) d:=by -- decay before Leg
 obtain ⟨F,S,t,u,z,G⟩:=p; obtain ⟨Y,C,q,U,w,c⟩:=q
 let L(T: Sa N× Sa N):= T.1∪T.2; let M(T:Sa N×Sa N):= charge (S T.1) (C T.2); let B(T:Sa N× Sa N):= Suite.jointK (t T.1) (q T.2) -- kind.pay
 let D:=Real.exp (-e*separation o o'); have ht(T:Sa N× Sa N): Branch.rent (a-e) (L T)*ledgerV (M T) ≤ D * paceK a S C T:=by
    have hc:0 ≤ ledgerV (M T):=sum_nonneg fun i _=>sum_nonneg fun j _=> (B T).nonn i j
    change _≤D* (Branch.rent a (L T)*ledgerV (M T))
    by_cases p: ledgerV (M T)=0; · rw [p]; simp
    obtain ⟨i,hi,hm⟩:=exists_ne_zero_of_sum_ne_zero p; obtain ⟨j,hj,hv⟩:=exists_ne_zero_of_sum_ne_zero hm; have hl:= ((B T).expo i j).triggered hv; have hz:o∈L T:= mem_union_left _ (by by_contra k; change M T i j≠0 at hv; unfold M at hv; rw [u T.1 k] at hv; simp [Branch.charge] at hv)
    have hu:o'∈ L T:= mem_union_right _ (by by_contra k; change M T i j≠0 at hv; unfold M at hv; rw [U T.2 k] at hv; simp [Branch.charge] at hv)
    have hg: separation o o' < (L T).card:= hl.1.lim o hz o' hu
    rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hc; unfold Branch.rent D; rw [←Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hg.le : (separation o o':ℝ)≤ (L T).card) g])
 refine arm_v (o:=o) L _ _ B (le_trans (sum_le_sum fun i _=> ht i) ?_) ?_ ?_
 · rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (fleet_U (fun X=>(t X).nonn) (fun X=>(q X).nonn) h (tally_F (fun X=>(q X).nonn) w) z) (Real.exp_pos _).le
 · intro i k; rw [u _ (fun p=> k (mem_union_left _ p))]; funext x y; simp [Branch.charge] -- removed rfl
 intro i; rw [G i,show J i.val= _ from c i]; simp only [Fintype.sum_prod_type,sum_mul,mul_sum]; first|exact sum_comm|rfl

end YM.CF.Swell
