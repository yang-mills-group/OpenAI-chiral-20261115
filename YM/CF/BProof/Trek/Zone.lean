import YM.CF.BProof.Trek.Wings
import YM.CF.BProof.Mapping.Plate
/-! Prices near P. Keep comparisons even if position p is in another Mark from origin.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c a:Side}{Y:Yard s}{D:Script Y}{u v d:ℝ}{H:Herald u v}{t:ℕ}{C:Sized t H.whole}{g:Ratio c s}{B:Blocks Y c}{U F:Bkg s}{f:Ratio a s}
local notation "CC" => ChillF Y g B C.blockY

namespace Permit
variable (L:Pad Y H C g.count.val) (p: Permit D C U g B d)(S:Sound Y H C d)(T:4≤a.val)(W:f.count=H.whole){r:ℝ}(e:Lamp C g B r U F)
include p
-- constant orientation on r=1 tangent patch about g-center of p, no diagonal step assumption, uses Plate.
lemma appoint (i:Y.Index)(x y:Space s)(h:ClearB Y g B i x 3)(t:Grid.dist (Grid.elder g x) (Grid.elder g y)≤1) : D.label i x=D.label i y:=by
 let a:=Grid.elder g x; have he(b:Space s)(t:Grid.dist a (Grid.elder g b)≤1): ClearB Y g B i b 2:= clear_panel Y g B i _ _ t (by decide) h
 refine Plate.ticket g x y (D.label i) 1 a ?_ t (fun i n u v=> ?_); unfold a; simp
 rw [Face.slide_t] at v ⊢; exact p.coherent _ _ _ (he i u) (he _ v)
include L
lemma into (x y:Site s){i:Y.Index}(h:x∈Y.gap i)(g':distant Y g B x 6)(t':separation x y ≤ t): tag Y x=i∧ tag Y y=i∧ distant Y g B y 3 ∧ D.code x=D.code y ∧ Y.Vic i t (time y):=by
 have hp:=Y.outside_gap i 0 _ (mem_strip.mp h); have hu:Y.Vic i t (time y):=by simpa only [Nat.zero_add] using along_t Y x y i hp t'
 have hv:= code_gap Y h; have ht: tag Y y=i:=Posts.vic Y i _ (r:=t) (by have hp:=L.slim; have :=L.reach_l; omega) hu; unfold Script.code; unfold distant at *; rw [hv] at g'; have hz: Grid.dist (Grid.elder g (BProof.space x)) (Grid.elder g (BProof.space y)) ≤1:=by
    apply Posts.elder_lip; rw [one_mul]; apply le_trans (spaceClose ..) (t'.trans (Nat.le_trans L.reach_l (le_trans _ L.high))); omega -- tune
 refine ⟨hv,ht, ht ▸ clear_panel Y g B _ _ _ hz (by decide : 1+3 ≤ 6) g',?_, hu⟩; rw [hv,ht]; exact p.appoint i _ _ (clear_weaker Y g B _ _ g' (by decide : 3≤6)) hz -- pass h weaker
include e S T W
lemma expand_true (x: Site s)(h:¬Y.Vic (tag Y x) C.nearM (time x) ∨ distant Y g B x 3): x∈ ChillF Y g B C.blockY ∧ D.XX C g B F f x=D.over x∧D.HH C g B F f x=D.port C x:=by
 have he:= p.rise_fin D C g B F L e S x h; have hp : C.live (ChillF Y g B C.blockY) x>0:= by rw [he]; exact zero_lt_one
 obtain ⟨hq,v⟩:= p.awake_here D C g B F f L T W e S x x hp (by simp); refine ⟨hq,v,?_⟩; unfold Script.HH; rw [if_pos hp]; simp_rw [he,one_mul]
lemma vision (x:Site s)(h:distant Y g B x 3)(q:Y.Vic (tag Y x) t (time x)) {v:ℝ}(t':v≥1): ∃ u'∈Zone,
    ‖D.HH C g B F f x v-Gig (D.code x) u'‖ ≤ 2*xm*d∧ (v=1 → u'=0):= by
 have he:= p.expand_true L S T W e x (.inr h); rw [he.2.2]; by_cases hp:dark Y x; swap
 · unfold Script.port; rw [if_neg hp,TG_Gig _ _ t']; let z:=ease (dial Y (tag Y x) x); let F:=tertiary v; have ht:F∈ Zone:= easeZ _; have hp:z∈Zone:=easeZ _; refine ⟨z*F,⟨mul_nonneg hp.1 ht.1,(mul_le_of_le_one_left ht.1 hp.2).trans ht.2⟩,?_,fun e=>?_⟩; rw [sub_self,norm_zero]; exact (mul_nonneg (mul_nonneg zero_le_two xm_p.le) S.fields.le); unfold F; rw [e,ter_down (by norm_num),mul_zero]
 let i:= hr Y x; have hx:x∈ Y.band i:= band_pick Y x hp; by_cases p': Y.D i; · refine ⟨0,z0,?_,fun _=>rfl⟩; rw [(p.levelD C L hx p').2,BM_1 (by linarith),Gig_0,sub_self,norm_zero]; exact (mul_nonneg (mul_nonneg zero_le_two xm_p.le) S.fields.le)
 have ht: chip (Y.u i) Y.long x≤ t:= vic_chip Y hx (by have :=L.slim; have hp:=L.reach_l; omega) q; have hz:=p.Promise C L (clear_weaker Y g B _ _ h (by decide : 2≤3)) hx p' (by have hp:= L.long; have e:= L.reach_l; omega) v; rw [entryR C ht] at hz; skip
 -- rather use factorQ via amend_late
 refine ⟨factorQ 0 v, fQ_p 0 v z0, ?_,fun hp=>?_⟩; have hp:= hz.1; rw [amend_late _ _ (by linarith)] at hp; exact hp; rw [hp]; unfold factorQ; rw [second_up (by norm_num),ter_down (by norm_num), mul_zero,sub_zero,mul_one,add_zero,sub_self]
lemma zero_f (x:Site s)(h:distant Y g B x 3)(q:Y.Vic (tag Y x) t (time x)): ‖D.HH C g B F f x 1-BB‖ ≤2*xm*d:=by obtain ⟨v,r,h,e⟩:= p.vision L S T W e x h q (le_refl (1:ℝ)); rwa [e rfl,Gig_0] at h
end Permit
end YM.CF.BProof.Trek
