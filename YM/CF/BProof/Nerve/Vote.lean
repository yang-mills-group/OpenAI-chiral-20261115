import YM.CF.BProof.Nerve.Around
/-! Use weighted Voronoi gaps instead of Delaunay lemma. This surrogate has
 dimension-4 *abstract simplices of barycentric weights*, used only in making
 the Basic maps. No eta' for other distances needed: can use any MinAbs tie lift beyond.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4800
set_option maxHeartbeats 780000
noncomputable section
namespace YM.CF.BProof.Mesh.Nerve
open Lattice Function Finset Equiv Regard Rows Sleet
open scoped BigOperators Classical
variable {n:Side}{C A:Type*}{s z l k R d:ℕ}
namespace Pie
open Guard Sleet
-- dummy inserted.Pay all fields undefined outside; helpers only Work.
variable {U : Field n A Prop}{g:Field n A (Fin z)}{F:Field n A ℝ}
variable (U F s) -- binder order l,s before. avoid
def capX (w:A)(i:Site n): Finset ℝ:= insert Guard.crown ((crowd U w).image (soil s (F w) i))
def rim (w:A)(i:Site n):ℝ:= (capX s U F w i).min' (insert_nonempty ..)
def valueU (z:ℕ)(w:A)(i x:Site n):ℝ:= if U w x then max 0 (rim s U F w i+alpha z-soil s (F w) i x) else 0
variable {U F s}
local notation "S_"=> crowd U
local notation "φ_"=> soil s
local notation "Xκ"=> Site n
local notation "R_"=> rim s U F
local notation "π↑"=>valueU s U F z
lemma rim_a {w:A}(x i:Site n)(t:U w x): rim s U F w i ≤ soil s (F w) i x:=min'_le _ _ (mem_insert_of_mem (mem_image_of_mem _ ((crowd_in ..).2 t)))
lemma self_a(w:A)(i:Site n): rim s U F w i ≤ Guard.crown:=min'_le _ _ (mem_insert_self ..)
lemma decide_a(w:A)(i:Site n): rim s U F w i=Guard.crown∨∃ x:Site n,U w x∧ rim s U F w i=soil s (F w) i x:=by
 rcases mem_insert.mp (min'_mem (capX s U F w i) (insert_nonempty ..)) with h|h; exact Or.inl h; obtain ⟨x,g,t⟩:= mem_image.mp h; exact .inr ⟨x,(crowd_in ..).1 g,t.symm⟩
abbrev Birthday(s:ℕ)(U : Field n A Prop)(F : Field n A ℝ):Prop:= ∀ w:A, (∀ x:Site n,U w x→ 0 ≤ F w x ∧ F w x≤1)∧∀ x:Site n,x∈halo (Bary*s) (crowd U w)
variable (D:Birthday s U F)
include D
lemma cost_c(w:A)(i:Xκ): R_ w i ≤Head:=by
 obtain ⟨x,hx,p⟩:=(halo_spec).mp ((D w).2 i); have h:U w x:=(crowd_in ..).1 hx; refine ((rim_a x i h).trans (min_le_left ..)).trans ?_; exact add_le_add (power_le p) ((D w).1 x h).2
lemma win_c(w:A)(i:Xκ):∃ x: Site n,U w x∧ R_ w i=soil s (F w) i x:= (decide_a ..).resolve_left (ne_of_lt ((cost_c D w i).trans_lt (by unfold Guard.crown; linarith)))
lemma field (w:A)(i x:Xκ)(p:U w x): R_ w i ≤ soil s (F w) i x:= rim_a x i p
abbrev press(s:ℕ):ℝ:=8*(2*(Halo:ℝ)+4)/s
variable (p:0<s)(t:SmallN s n)
include p t
lemma era (w:A)(x y:Site n)(h:separation x y≤1):|R_ w x-R_ w y|≤press s:=by
 have he(x y)(h:separation x y ≤1): R_ w x-R_ w y ≤press s:= by
    obtain ⟨i,v,hv⟩:=win_c D w y; rw [hv]; exact (sub_le_sub_right (field D w x i v) _).trans ((le_abs_self _).trans (tune x y i _ ((D w).1 _ v).1 h p t))
 rw [abs_le]; exact ⟨by linarith only [he y x (separation_comm .. ▸ h)],he x y h⟩
omit p t
lemma seat (w:A)(i:Xκ):∃ x, π↑ w i x=alpha z:=by obtain ⟨x,h,e⟩:=win_c D w i; exact ⟨x, by unfold valueU; rw [if_pos h, e]; simp only [add_sub_cancel_left,max_eq_right (tiny z).1.le]⟩
omit D
lemma cash (w:A)(i x:Xκ): 0≤π↑ w i x ∧ π↑ w i x ≤ alpha z:=by unfold valueU; split; rename_i p; exact ⟨le_max_left ..,max_le (tiny z).1.le (by linarith only [rim_a (F:=F) (s:=s) x i p])⟩; exact ⟨le_rfl,(tiny z).1.le⟩
def supporters (U:Field n A Prop)(F:Field n A ℝ)(s z:ℕ)(w:A)(i:Site n): Finset (Site n):= univ.filter fun j=> 0< valueU s U F z w i j
lemma starP{w:A}(i x :Xκ):x∈supporters U F s z w i↔π↑ w i x ≠0:=by rw [supporters,mem_filter]; simp only [mem_univ,true_and,ne_eq]; exact lt_iff_le_and_ne.trans (by simp only [(cash w i x).1,true_and,eq_comm]) -- type
lemma fans (w:A)(i x:Xκ): x∈supporters U F s z w i ↔ U w x ∧ soil s (F w) i x < R_ w i+alpha z:=by
 unfold supporters valueU; by_cases t:U w x <;> simp [t]
include p t D
lemma level (w:A)(i j x:Xκ)(h:separation i j≤1): |π↑ w i x-π↑ w j x|≤ 2*press s:=by
 unfold valueU; by_cases u:U w x; swap; · rw [if_neg u,if_neg u, sub_self,abs_zero]; unfold press; positivity
 rw [if_pos u,if_pos u]; have g:= era D p t w i j h; have hh:|soil s (F w) i x-soil s (F w) j x| ≤ press s:= tune i j x (F w) ((D w).1 _ u).1 h p t; rw [abs_le] at g hh ⊢; grind [le_max_left,le_max_right] -- maybe grind sees max_real
lemma bonds(w:A)(i j x:Xκ)(u: separation i j ≤ 1)(z':ℕ)(v:2*press s<alpha z')(h:x∈supporters U F s z' w j): U w x ∧ soil s (F w) i x <R_ w i+2*alpha z' :=by
 obtain ⟨y,t'⟩:= fans ..|>.1 h; have t0:= era D p t w i j u; have t1:|soil s (F w) i x-soil s (F w) j x| ≤press s:= tune i j x (F w) ((D w).1 _ y).1 u p t; refine ⟨y,?_⟩; rw [abs_le] at t0 t1; linarith
omit t
lemma stick (w:A)(i x:Xκ)(t':U w x)(t:soil s (F w) i x <R_ w i+ 2*alpha z) :separation i x≤ Halo*s∧soil s (F w) i x=sizeD s x i +F w x:=by
 have he:soil s (F w) i x<Guard.crown:= by unfold Guard.crown; linarith only [t,cost_c D w i,(tiny z).2]
 refine ⟨(separation_comm ..).trans_le (grow x i p ((D w).1 _ t').1 he),min_eq_left ((min_lt_iff.mp (show min _ _ <_ from he)).resolve_right (lt_irrefl _)).le⟩
lemma never (w:A)(i x:Xκ)(v:Halo*s< separation i x): π↑ w i x=0:=by
 by_contra t; obtain ⟨u,h⟩:= (fans w i x).1 ((starP i x).2 t); exact not_le.mpr v (stick D p w i x u (z:=z) (by linarith only [h,(tiny z).1])).1 -- tune method
end Pie
end YM.CF.BProof.Mesh.Nerve
