import YM.CF.BProof.Nerve.Pay
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
open Guard Policy
variable {U : Field n A Prop}{g:Field n A (Fin z)}{F:Field n A ℝ}
local notation "Xκ"=>Site n
local notation "Y_"=> supporters U F s z
local notation "π↑"=>valueU s U F z
local notation "γ"=>alpha z
local notation "Sm"=> Halo*s
local notation "R_"=> rim s U F
variable (D:Birthday s U F)(D':Lustre U F s z)(p:0 < s)(t:SmallN s n)(v':2*press s<alpha z)
include D p
lemma search(i:Xκ)(w:A) : ∃ x∈region n i (Halo*s),U w x∧soil s (F w) i x=R_ w i :=by
 obtain ⟨x,v,e⟩:=win_c D w i; exact ⟨x,(reg_in ..).2 ((stick D p w i x v (z:=1) (by rw [← e]; linarith only [(tiny 1).1])).1),v,e.symm⟩
lemma rim_cost : Uses (Joint U F) (rim s U F) (Halo*s) :=by
 intro x u v h; have t(u v)(h:Matches (region n x (Halo*s)) (Joint U F u) (Joint U F v)): R_ u x ≤ R_ v x:=by
    obtain ⟨i,p,g,q⟩:= search D p x v; obtain ⟨v1,v2⟩:= (Prod.mk.inj (show (U u i,F u i)=(U v i,F v i) from h p)); rw [←q]; unfold soil; rw [←v2]; exact field D _ _ _ (v1.symm ▸ g) -- tune
 exact le_antisymm (t u v h) (t v u h.rot)
lemma ray : Uses (Joint U F) (valueU s U F z) (Halo*s):=by
 intro x u v h; have he:=rim_cost D p x u v h; funext i; by_cases t:i∈region n x (Halo*s); · unfold valueU soil; rw [he,show U u i=U v i from congrArg Prod.fst (h t),show F u i=F v i from congrArg Prod.snd (h t)]
 rw [not_congr (reg_in ..)] at t; rw [never D p _ _ _ (lt_of_not_ge t),never D p _ _ _ (lt_of_not_ge t)]
lemma used : Uses (Joint U F) (cent s z U F) (Halo*s):=by intro x u v h; funext i; have ht:=ray D p x u v h (z:=z); unfold cent warm; rw [ht]
include t
lemma seen(r:Signed)(x:Site n)(E:Perm A)(p':Transforms (facet r x) (Joint U F) E)(u:A)(y i): π↑ (E u) y i=π↑ u (facet r x y) (facet r x i):=by
 let Q:=facet r x; have he(i):U (E u) i=U u (Q i):=congrArg Prod.fst (p' u i); have ht(i)(h:U (E u) i)(a):soil s (F (E u)) a i=soil s (F u) (Q a) (Q i):= cap_rot t p r x _ _ ((D _).1 i h).1 (show F u (Q i)= _ from (congrArg Prod.snd (p' u i)).symm)
 have hq:R_ (E u) y=R_ u (Q y):=by obtain ⟨v,g,p⟩:= win_c D (E u) y; obtain ⟨w,f,l⟩:=win_c D u (Q y); obtain ⟨w,rfl⟩:=Q.surjective w; apply le_antisymm; rw [l,← ht w (he w|>.symm ▸ f) y]; exact field D _ _ _ ((he w).symm ▸ f); rw [p,ht v g]; exact field D _ _ _ (he v ▸ g)
 change _=π↑ u (Q y) (Q i); unfold valueU; by_cases f:U (E u) i; · rw [if_pos f,if_pos (he i ▸ f),hq,ht i f]
 rw [if_neg f,←he,if_neg f]
lemma cent_ride(r:Signed)(x:Site n)(E:Perm A)(p':Transforms (facet r x) (Joint U F) E)(u:A)(y i): cent s z U F (E u) y i=cent s z U F u (facet r x y) (facet r x i):=by
 unfold cent warm; simp_rw [seen D p t r x E p' u,Equiv.sum_comp]
include D'
def badge(z:ℕ)(s:ℕ):=2* press s<alpha z
-- sizelim.NP.Real no eval palette!
omit D p t D'
lemma birthday(s n:ℕ):True:=trivial -- remove
open Filter
lemma tinyD (z:ℕ) (r:ℝ)(v:0< r):∀ᶠ s:ℕ in Filter.atTop, 0<s∧2*press s<alpha z ∧ rate s z< r:=by
 have he:Filter.Tendsto press Filter.atTop (nhds 0):= tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop -- memory
 have ht: Filter.Tendsto (fun s=> rate s z) Filter.atTop (nhds 0):=by simpa only [rate,mul_zero,zero_div] using ((he.const_mul 20).div_const (alpha z))
 filter_upwards [eventually_gt_atTop 0,ht.eventually_lt_const v,he.eventually_lt_const (show 0<alpha z/2 from half_pos (tiny z).1)] with s u F h; exact ⟨u,by linarith only [h],F⟩
-- fix Tendsto
end Pie
end YM.CF.BProof.Mesh.Nerve
