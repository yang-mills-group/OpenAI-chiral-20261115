import YM.CF.Fixed.Voltage.Grant
/-!
Authenticated reorganization across full address. Regular promotion (keep through long mask only). Cost always charged, not free. Never make input assumption holds in every volume; requires long enough.
-/
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Fixed.Voltage
open Function NormedSpace Filter Metric Finset Lattice Wilson SU Scree Skye Fock Lat Cube MeasureTheory Vow RG Rue Spire Scroll
open Vow Ione Beau Salt Push.BetaTransport
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{x a b h u v w:ℝ}(P:BudgetPoint)(D:Support (More n)){R Q:ForceBudget n}{E E':RegBudget n}
variable {K:ℕ}{τ:Sweep n→Prop}
local notation "N"=> More n
local notation "A"=> deck_F P D
abbrev fairH(n:Side):ℝ:= Fintype.card (Site (More n))
abbrev fareH(n:Side):ℝ:= (fairH n)⁻¹
lemma fareH_pos (n):0<fareH n:=inv_pos.mpr (show 0<fairH n from by unfold fairH; positivity)
noncomputable def fleetT(P:BudgetPoint)(F:InkD n)(U:Pane n):= (deck_F P (∅:Support N)).indicator F U
noncomputable def pipeline(P:BudgetPoint)(F:InkD n):RegBudget n:=fun i=>if i.val.2=univ then fareH n • fleetT P F else 0
lemma pipe_budget(F:InkD n)(g:Metered P ∅ (oV F) w b)(t:1≤w)(i:Hub n)(v:i.val.2=univ): PressB P i (pipeline P F i) w (fareX 0 P (univ: Support N)*(fareH n*b)):=by
 unfold pipeline; rw [if_pos v]; have he:Medal P univ (∅:Support N) (oV (fleetT P F)) w b:=by
    have vh(x:Orbit n):oV (fleetT P F) x=hours P ∅ (oV F) x:=by
      by_cases h:x.1∈ deck_F P (∅:Support N); · rw [unveil_F _ _ _ _ h]; exact Set.indicator_of_mem h _
      rw [shut_F _ _ _ _ h]; exact Set.indicator_of_notMem h _
    rw [funext vh]; exact g.meter
 have hx:= he.rum (fareH n); rw [Real.norm_of_nonneg (fareH_pos n).le,←v] at hx; rw [←v]; exact Medal.preservesE (Classical.arbitrary _) (G:=fareH n • fleetT P F) (U':=i) hx (zero_le_one.trans t) 0
abbrev pipeCost (P:BudgetPoint)(n:Side)(b:ℝ):= Fintype.card (Hub n) * P.mass (univ:Support (More n)) (fareX 0 P (univ:Support (More n))*(fareH n*b))
noncomputable def Vision (F:InkD n):Prop:= ∀ (s:Sweep n)(U:UNI SpinIdx), JetS s.s s.charge (detX s.s) U→∀ V:Pane n, F (flashA s V)=tintY s U (F V)
lemma full_K(s:Sweep n)(X:Support (More n)): actY s X=univ ↔ X=univ:=by
 have he:actY s univ=univ:=Finset.map_univ_equiv _
 nth_rw 1 [←he]; exact (Finset.map_injective _).eq_iff
lemma lord_pipe(F:InkD n)(g:Metered P ∅ (oV F) w b)(t:1≤w)(U:Vision F)(K:ℕ)(p:¬Pave P K (univ:Support N)):Lord P (pipeline P F) (pipeCost P n b) w K:=by
 let v:=fareX 0 P (univ:Support N)*(fareH n*b); have h:0≤v:=mul_nonneg (health_f ..) (mul_nonneg (fareH_pos _).le (g.holds (zero_le_one.trans t))); let Z(x:Hub n):ℝ:= if x.val.2=univ then v else 0; refine ⟨⟨⟨Z,fun i=>?_,fun i=>?_⟩,fun s S T u X V=>?_⟩,fun X _ i=>?_⟩
 · by_cases h:i.val.2=univ; · unfold Z; rw [if_pos h]; exact pipe_budget P F g t i h
   unfold pipeline Z; rw [if_neg h,if_neg h]; exact Vale.rinse ..
 · apply le_trans (b:=∑ _i:Hub n,P.mass (univ:Support N) v); swap; · exact Eq.le (by simp [pipeCost,v])
   refine sum_le_sum fun j _=>?_ ; split; swap; · exact mass_live _ _ h
   unfold Z; split; rename_i h; rw [h]; unfold BudgetPoint.mass; rw [mul_zero]; exact mass_live _ _ h -- tune
 · have he:(moveHub s X).val.2=univ ↔X.val.2=univ:=full_K s X.val.2; unfold pipeline; by_cases hp:X.val.2=univ; rw [if_pos hp,if_pos (he.2 hp),Pi.smul_apply,Pi.smul_apply,map_smul]; swap; · rw [if_neg hp,if_neg (mt he.1 hp)]; exact (map_zero _).symm
   unfold fleetT; have ht:=deck_work P (∅:Support N) s V; rw [actY,map_empty] at ht; by_cases hg: V∈ deck_F P (∅:Support N); rw [Set.indicator_of_mem (ht.2 hg), Set.indicator_of_mem hg,U s T u V]; rw [Set.indicator_of_notMem (mt ht.1 hg), Set.indicator_of_notMem hg,map_zero]
 · unfold pipeline; rw [if_neg (fun (e:X.val.2=univ)=> p (e ▸ i))]; exact Beau.none_q _
noncomputable def fullSlot (x:Seat n) : Hub n:=⟨(x,univ),mem_univ _⟩
lemma sum_slot {F: Hub n→ Cipher n} (p:∀ i:Hub n, i.val.2≠univ→ F i=0): (∑ i,F i)= ∑ i:Seat n,F (fullSlot i):=by
 symm
 let f:Seat n→ Hub n:= fullSlot; have he:Injective f:=fun i j e=>congrArg (fun v:Hub n=>v.val.1) e; let T:= univ.image f; rw [←Finset.sum_image (g:=fullSlot) (s:=univ) (f:=F) (by intro a _ b _ h; exact he h)] -- simp; use calc
 apply sum_subset (subset_univ _); intro i _ v; exact p i (fun h=> v (mem_image.mpr ⟨i.val.1,mem_univ _,Subtype.ext (Prod.ext rfl h.symm)⟩))
lemma pipe_T (F:InkD n)(V:Pane n) : exponentL P (pipeline P F) V=fleetT P F V:=by
 unfold exponentL; rw [sum_slot];
 · have he(i:Seat n): pipeline P F (fullSlot i)=fareH n • fleetT P F:= if_pos rfl
   simp_rw [he]; by_cases h:V∈ deck_F P (∅:Support N)
   · change (∑ i:Seat n,numbE P.threshold univ (fareH n • fleetT P F) V)=_; simp only [numbE, Set.indicator_of_mem (show V∈{i|pingS P.threshold univ i} from (deck_empty P V).1 h),Pi.smul_apply,sum_const,card_univ]; rw [←Nat.cast_smul_eq_nsmul ℝ]; apply smul_inv_smul₀ (show fairH n≠0 by unfold fairH; positivity)
   change (∑ i:Seat n,numbE P.threshold univ (fareH n • fleetT P F) V)=_; simp only [numbE,Set.indicator_of_notMem (show V∉{i|pingS P.threshold univ i} from mt (deck_empty P V).2 h),fleetT,Set.indicator_of_notMem h,sum_const_zero]
 intro i hp; unfold pipeline; rw [if_neg hp]; unfold numbE; simp -- indent tune
lemma pipe_rank (F:InkD n)(t:¬ Pave P K (univ:Support N)): Haro.StackL (pipeline P F) (Py.treeΘ P K)=0:=by
 unfold Haro.StackL; refine sum_eq_zero fun i u=>?_ ; unfold pipeline; rw [if_neg (fun (h:i.val.2=univ)=> t (h ▸ (mem_filter.mp u).2))]; have he:= Haro.orbP (n:=n) 0 (0:Cipher n); rw [zero_add] at he ; exact (add_eq_left.mp he.symm)
end YM.CF.Fixed.Voltage
