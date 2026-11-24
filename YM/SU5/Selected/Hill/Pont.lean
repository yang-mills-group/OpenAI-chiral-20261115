import YM.SU5.Selected.Hill.Clou
import YM.SU5.Selected.Hill.Miss
/-! Witnesses on forests. Real determinant and card inequalities. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Filter Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus Next.Rank.Axial Chene.Perks
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
variable {G:Gauge}{n:Side}(r:Side)(S:Lots n)(B':ℕ){B R:ℕ}
abbrev FreeX (r n:Side) := (columbia r n).Free
abbrev Board(B:ℕ) := (univ:Finset (FreeX r n)).filter (fun i=> Light r S B i.val.1)
abbrev seat_set:= ↥(Board r S B')
abbrev outside:= Pad.forestFree (Board r S B') -- complement as type
abbrev distil (i:seat_set r S B') : EdgeT n:= i.val.val
theorem distil_inj: Injective (distil r S B'):=fun _ _ v=>Subtype.ext (Subtype.ext v)
abbrev leaves(r n: Side) : (FreeX r n)→ EdgeT n:= Subtype.val
lemma real_leaves : Fintype.card (FreeX r n)= Perks.shoots n:=by
 have p:= count_clear (columbia r n); have q:= count_clear (axle n); unfold FreeX shoots; omega
lemma outside_count : Fintype.card (outside r S B') ≤ 4*(12*(n.val/r.val+1)* B'*n.val^3+S.card*r.val^4):=by
 let X:= univ.filter (fun x:Site n=> ¬recess r B' x); let U:= S.biUnion fun i=> orbit r i.1; let D:= X∪U; let Z:=outside r S B'; let f:Z→ EdgeT n:=fun i=>i.val.val; have hf:f.Injective:=fun _ _ h=>Subtype.ext (Subtype.ext h); have he:Fintype.card Z ≤ D.card*(univ:Finset Axis).card:=by
    rw [←card_product,←card_univ]; refine card_le_card_of_injOn f (fun i h=> mem_product.mpr ⟨?_,mem_univ _⟩) hf.injOn
    have hp:= i.property; by_contra w; apply hp; refine mem_filter.mpr ⟨mem_univ _,Classical.byContradiction ?_,?_⟩; swap
    · intro a v p; exact w (mem_union_right X (mem_biUnion.mpr ⟨a,v,mem_filter.mpr ⟨mem_univ _,p⟩⟩))
    exact fun p=> w (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,p⟩))
 have ht:U.card ≤ S.card*r.val^4:= card_biUnion_le.trans ((sum_le_sum (fun i _=> orbit_bill i.1 r)).trans_eq (by simp))
 rw [card_univ,Fintype.card_fin] at he
 exact he.trans (le_trans (Nat.mul_le_mul_right 4 ((card_union_le X U).trans (add_le_add (count_edge ..) ht))) (Eq.le (Nat.mul_comm ..)))
def slant (S: Finset (FreeX r n)): S ⊕ Pad.forestFree S ≃ FreeX r n:= Equiv.sumCompl (·∈S)
lemma count_even : (Board r S B').card + Fintype.card (outside r S B')= shoots n:=by rw [←real_leaves r,Fintype.card_congr (slant r (Board r S B')).symm,Fintype.card_sum,Fintype.card_coe]
variable {r S B'} {W:PathData G}{C:Clip}{σ X D θ u A:ℝ}{H:Bed}
-- let `fare` scaled by (1-θ). hW binds clipping. no use phase assumptions
abbrev palace (r:Side)(S:Lots n)(B':ℕ) := vouch (distil r S B') G.ColorIndex
abbrev race (r:Side)(S:Lots n)(B' B R:ℕ)(h:W.Bounds C σ X D)(θ:ℝ):= (1-θ) • (flare R (lesson r S B) h).submatrix (palace r S B') (palace r S B')
variable (h:W.Bounds C σ X D)(g: Attached H W)(p: Floor H C n u A)
include g p
set_option maxHeartbeats 250000 in
lemma cusp_corner(r:Side)(S: Lots n)(hn:1<n.val)(q:0≤θ)(z:θ<1)(t:B+2*R+4 ≤ B')(d:0<u)(v:rate_ell σ X R / C.direct ≤ θ^2): let R':=race r S B' B R h θ; R'.PosDef ∧ Trunk.Chene n H (axle n).trunks ^ Fintype.card G.ColorIndex ≤ Real.exp ((Fintype.card (Pens G (outside r S B')) :ℝ)*dollar A) / (((1-θ)^3)^ Fintype.card (Pens G (seat_set r S B'))) * R'.det:=by
 intro K; let f:=distil r S B'; let M:=cred (leaves r n) G H; let X0:=cred f G H; let O:=Board r S B'; let Q:=slant r O; let h₀:=vouch (Subtype.val: O→ FreeX r n) G.ColorIndex; let e: Pens G O⊕ Pens G (outside r S B')≃Pens G (FreeX r n):=(Equiv.sumProdDistrib _ _ _).symm.trans (Equiv.prodCongr Q (Equiv.refl G.ColorIndex))
 have he(i:Pens G O):h₀ i=e (.inl i):=rfl
 have hp : M.PosDef:= inherit_d _ (above_pin H hn u d ⟨fun x=>(p.uniform.1 x).1⟩ p.symmetric.1 (columbia r n)) _
 have h𝔻:M.submatrix h₀ h₀=X0:=rfl
 have hq': Injective h₀:= fun i j d=>Prod.ext (Subtype.ext (congrArg Prod.fst d)) (show (h₀ i).2=(h₀ j).2 from congrArg Prod.snd d)
 have hv' : (M.submatrix h₀ h₀).PosDef:= hp.submatrix hq'
 rw [h𝔻] at hv'
 have hh: M.det ≤ ((M.submatrix h₀ h₀).det * Real.exp ((Fintype.card (Pens G (outside r S B')) :ℝ)*dollar A)):= Miss.block_b e hp h₀ he (fun i=> dollar_pass H _ _ _ p i) -- tune dollar_pass args
 have hs:0<1-θ:=sub_pos.mpr z; have hP:= comparison f h g p (distil_inj ..) q z.le t (fun i:↥O=> (mem_filter.mp i.property).2) v; have hk:0<(1-θ)^3:=pow_pos hs _
 rw [h𝔻] at hh
 have hw:= Miss.scale_b (D:=K) M _ 1 X0 _ hv' hs hP _ hh rfl; rw [← cred_det H p.symmetric.1 (columbia r n)]; exact hw
end YM.Hill.Box
#print axioms YM.Hill.Box.cusp_corner
