import YM.CF.BProof.Rhythm.Pizza
import YM.CF.Skye.Pine
/-! Exact flag support to identify which links can need repair. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Rhythm.Lease
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth Trek Gates
open RG Wilson Mapping.House Pricing Gates.Stage Gates.Stage.Setup Skye
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v} {L:Side} {a:ℕ}{y:ℝ}{d:ℕ}(P:Gates.Stage.Entice S L a d y){s:Side}(Y:S.Setup L a (More s) d y)
variable (T:PathData SU.group)(θ:ℝ)(x:Pawn Y.yard)(h:T.Bounds c w R v)(k:θ∈Set.Icc (1/2) 2)(hx:Along P Y T θ x)
variable {u v':ℝ}(H:Herald u v') {t:ℕ}(C:Sized t H.whole) (Q:Pad Y.yard H C Y.g.count.val) {ν:ℝ}
local notation "V₀"=> area P Y T θ x
local notation "B₀" => Y.bad x
local notation "Y₀" => Y.yard
include h k hx Q
lemma flag_here (p:thresh y≤ ν)(i:Site (More s))(t':i∈RG.flags ν V₀): Y.yard.Gap (tag Y₀ i) (time i) ∧ ¬distant Y₀ Y.g B₀ i 1:=by
 obtain ⟨j,f,h,t⟩:= Pflag h k hx i t'; -- local lemma? below
 let A:= tag Y₀ i; have he:A=j.1:= Posts.gap Y₀ _ _ h; refine ⟨show Y.yard.Gap A _ from he ▸ h,fun x'=>?_⟩; let Z:= hide Y₀ Y.g j; have hz: Z ∈ B₀:= mem_image_of_mem _ (mem_union_left _ f);
 apply disjoint_left.mp x' hz; apply (House.ray_spec ..).2; refine ⟨?_,he.symm⟩; change Grid.dist (House.hide Y₀ Y.g (A, BProof.space i)) _≤1; rw [he]; refine Trek.hide_close Y₀ Y.g j.1 ?_; simp only [one_mul]; exact t.trans (by have ht:=Q.high; omega)
where
 Pflag (h k x' j) (t': j∈RG.flags ν V₀): ∃ k∈x.sev, Y.yard.Gap k.1 (time j) ∧ Grid.dist (BProof.space j) k.2 ≤4 := by
    refine Y.flags P T θ x h k x' j ?_; obtain ⟨t,h,e⟩:= (RG.flags_spec ..).1 t'; exact (RG.flags_spec ..).2 ⟨t,h,p.trans_lt e⟩ -- h implicit Binder inference tune
lemma roof_mask (p:thresh y≤ ν){t':ℕ}(tY:t'≤C.blockY)(i j:Site (More s))(hi:j∈RG.flags ν V₀)(he: separation i j ≤ t'): i∉ChillF Y₀ Y.g B₀ C.blockY:=by
 intro h'; obtain ⟨ha,hb⟩:=flag_here P Y T θ x h k hx H C Q p j hi; have hz: Y.yard.Vic (tag Y₀ j) C.blockY (time i):=⟨_,ha,(((Angular.Yard.time_jump j i).trans ((separation_comm ..).trans_le he)).trans tY)⟩
 have hu:tag Y₀ i= tag Y₀ j:=Posts.vic _ _ _ (Q.suff (le_refl _)) hz; apply hb; exact near_clear Y₀ Y.g B₀ i j (r:=1) (spinChill Y₀ Y.g B₀ _ i h' (hu ▸ hz)) hu (by rw [one_mul]; apply (he.trans tY).trans; have ht:= C.near; have hx:= Q.high; omega)
lemma lineLamp (p:thresh y≤ ν){t':ℕ}(tY:t'≤C.blockY)(δ:ℝ)(u:0≤δ)(v:δ≤ H.calm)(U:Skye.Orbit s→ Skye.Pane s)(roof:Roof s ν δ t' U)(Z:Skye.Ids s): Trek.Lamp (Y:=Y₀) C Y.g B₀ δ V₀ (U (V₀,Z)):=by
 refine ⟨?_,roof.paid _,u,v⟩; intro b u v; symm; apply roof.lamp; apply disjoint_left.mpr; intro i j w; obtain ⟨t,w,e⟩:= halo_spec.mp w; have hp:= roof_mask P Y T θ x h k hx H C Q p tY t i j e; rcases mem_insert.mp (show t∈ insert b.1 ({b.1+step b.2}: Finset _) from w) with w|w; exact hp (w ▸ u); exact hp (mem_singleton.mp w ▸ v)
end YM.CF.BProof.Rhythm.Lease
