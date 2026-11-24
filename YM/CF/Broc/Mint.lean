import YM.CF.Broc.Wage
/-! Final real field currency. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}
lemma visit_v (x:Site N)(w:Walk)(z)(p:z∈visits x w): separation x z ≤ w.length:=by
 induction w generalizing x with
 | nil=> simp [visits] at p; simp [p]
 | cons i l ih=> rcases List.mem_cons.mp p with g|g
                 · subst z; simp
                 have hx : separation x (x+i.vec) ≤1:=leakspan (a:=x) [i] -- tune
                 exact (separation_triangle x _ z).trans ((Nat.add_le_add hx (ih _ g)).trans_eq (by simp [add_comm]))
variable (G: Ratio N P)
lemma scale_span (x y:Fend N)(w:ℕ)(h:separation x y≤w):separation ((ratio G).embed x) ((ratio G).embed y)≤ G.count.val*w :=by
 rw [separation,← Ratio.root_embed, ← Ratio.root_embed,← map_sub,Ratio.root_embed]; apply Finset.sup_le; intro i _
 have ht:= (component_le _ i).trans h; rw [Ratio.lift_embed]; change Int.natAbs _ ≤_; rw [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ ht
abbrev Rent0(e:ℝ):= {U:Nom N P|JointB G U e}
lemma open_tr(e:ℝ) : CompactSpace (Rent0 G e):=by
 let S:= {x:Nom N P|∀ i:Guy (N:=N),‖brand (x.2 i)-brand (travel x.1 ((ratio G).embed i.1) (pathL G i.2))‖ ≤ e}
 have he:IsClosed S:=by
   unfold S; simp_rw [Set.setOf_forall]; apply isClosed_iInter; intro i; apply isClosed_le _ continuous_const
   apply Continuous.norm
   exact (Dial.spinD.comp ((continuous_apply i).comp continuous_snd)).sub (Dial.spinD.comp ((travel_cont _ _).comp continuous_fst))
 have h:Rent0 G e=(Prod.fst ⁻¹' {x|Guard x e}) ∩ Prod.snd ⁻¹' {x|Guard x e}∩ S:=by ext i; exact ⟨fun h=> ⟨⟨h.fg,h.cg⟩,h.follow⟩,fun ⟨⟨g,p⟩,k⟩=>⟨g,p,k⟩⟩
 apply isCompact_iff_compactSpace.mp
 rw [h]; exact ((IsClosed.inter ((cover_closed (More P) e).preimage continuous_fst) ((cover_closed (More N) e).preimage continuous_snd)).inter he).isCompact

def dressL(e:ℝ):Light (Fend P) ↥(Rent0 G e) (Fend P→SU.E) where
 frame:=terr _
 dress t x:=⟨july G t x.val, joint_g G _ x.property t⟩
 rel S x y:= Agrees S x.val.1 y.val.1 ∧ Agrees (cloudG G S) x.val.2 y.val.2
 expands _ _ h _ _ q:= ⟨fun i a b=> q.1 i (h a) (h b),fun i u v=>q.2 i ((cloud_grows G h) u) ((cloud_grows G h) v)⟩

def popV(K B:Side):ℕ:= 4*K.val+K.val*(8*B.val)
lemma acorn(p:ℕ)(B:Side)(S:Seal (Fend P)): foam _ (8*B.val) (cloudG G (foam _ (4*G.count.val) S))⊆ cloudG G (foam _ (popV G.count B) S):=by
 intro i hi; obtain ⟨y,h,e⟩:=mem_biUnion.mp hi; obtain ⟨v,h,g⟩:= mem_biUnion.mp (mem_filter.mp h).2; refine mem_filter.mpr ⟨mem_univ _, mem_biUnion.mpr ⟨v,h,(bay_mem _).mpr ?_⟩⟩
 exact (separation_triangle v _ _).trans (add_le_add ((bay_mem _).mp g) (scale_span _ _ _ _ ((bay_mem _).mp e)))
end YM.CF.Broc
