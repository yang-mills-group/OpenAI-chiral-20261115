import YM.CF.BProof.Stave.Mould
import YM.CF.BProof.Stave.Simplex
/-! Boundary gluing. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave.Sim
open Function Filter Topology Finset Metric Extension
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal
variable {I:Type*}[Fintype I][DecidableEq I]{E:Type*}[PseudoMetricSpace E]{S:Finset I}
def Wall(S:Finset I): Set (Pool I):= {x|∃ i∈S,Sim (S.erase i) x}
lemma wall_le {S:Finset I}: Wall S ⊆ Park S:=fun x ⟨_,_,g⟩=> g.mono (erase_subset ..)
lemma wall_iff {S:Finset I}{x:Pool I}(g:Sim S x): x∈Wall S↔ supp x ≠ S:= by
 constructor
 · rintro ⟨i,p,q⟩ h; exact mem_supp.mp (show i∈supp x from h.symm ▸ p) (q.vanish (by simp))
 intro p; obtain ⟨i,hi,hi'⟩:= not_subset.mp (show ¬ S ⊆ supp x from fun q=> p (Subset.antisymm g.box q)); exact ⟨i,hi,g.shrinks (of_not_not ((mem_supp.not).mp hi'))⟩
private lemma compactF {X:Type*}[MetricSpace X]{S:Set X}{F:X→ E}(h:S.Finite): Tame S F:=by
 classical
 letI:=h.fintype; let f(p:S×S):ℝ≥0:= nndist (F p.1.val) (F p.2.val) / nndist p.1.val p.2.val; let U:= univ.sup f
 refine ⟨U,LipschitzOnWith.of_dist_le_mul (fun x hx y hy=>?_)⟩; by_cases g:x=y; simp [g]; have hm:= le_sup (f:=f) (mem_univ ((⟨x,hx⟩,⟨y,hy⟩):S×S)); change f _≤ U at hm; have he : nndist (F x) (F y) ≤ U * nndist x y:= (div_le_iff₀ (lt_of_le_of_ne bot_le (Ne.symm (nndist_eq_zero.not.mpr g)))).mp hm; exact he
lemma rises {F: Pool I → E}(h:∀ i∈S,Tame (Park (S.erase i)) F): Tame (Wall S) F:=by
 classical
 by_cases g:3≤ S.card
 · choose K p using fun i:S => h i.val i.property
   let U := (univ:Finset S).sup K -- syntax
   have q(i)(u:i∈S): LipschitzOnWith U F (Park (S.erase i)):= (p ⟨i,u⟩).weaken (le_sup (f:=K) (mem_univ (⟨i,u⟩:S)))
   refine ⟨3*U,LipschitzOnWith.of_dist_le_mul (fun x hx y hy=>?_)⟩
   obtain ⟨i,s,hi⟩:= hx; obtain ⟨j,t,hj⟩:=hy
   by_cases z:i=j
   · subst j; apply ((q i s).dist_le_mul x hi y hj).trans; gcongr; exact le_mul_of_one_le_left (show 0≤U from bot_le) (by norm_num)
   obtain ⟨a,pA⟩:= card_pos.mp (show 0<((S.erase i).erase j).card from by rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm z,t⟩), card_erase_of_mem s]; omega); rw [mem_erase,mem_erase] at pA
   let Z:=gift i a y
   have hm:Sim (S.erase j) Z:=gift_sim hj (Ne.symm pA.2.1) (mem_erase.mpr ⟨pA.1,pA.2.2⟩)
   have hz : Sim (S.erase i) Z:= (hm.mono (erase_subset ..)).shrinks (coin (Ne.symm pA.2.1))
   have he : dist y Z ≤ dist x y:=by
     unfold Z; rw [gift_price hj (Ne.symm pA.2.1), dist_eq_norm]; apply le_trans (le_of_eq ?_) (norm_le_pi_norm _ i); change y i= ‖x i-y i‖; rw [hi.vanish (by simp)]; simp [Real.norm_of_nonneg (hj.pos i)]
   have hZ : dist x Z ≤ 2*dist x y:= (dist_triangle x y Z).trans (by rw [two_mul]; gcongr)
   apply (dist_triangle_right (F x) (F y) (F Z)).trans ((add_le_add ((q i s).dist_le_mul _ hi _ hz) ((q j t).dist_le_mul _ hj _ hm)).trans ?_); push_cast; nlinarith [U.coe_nonneg]
 apply compactF
 refine ((Set.finite_range (fun i:I=> Pi.single i (1:ℝ))).subset (fun x hx=>?_))
 obtain ⟨i,p,e⟩:=hx
 obtain ⟨j,hj⟩:= card_eq_one.mp (show (S.erase i).card=1 from by have z:=card_pos.mpr e.nonempty; rw [card_erase_of_mem p] at *; omega)
 exact ⟨j,(equal (hj ▸ e)).symm⟩
end YM.CF.BProof.Mesh.Stave.Sim
