import YM.CF.BProof.Nerve.Lever
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
namespace Guard
-- clamped value & Lips before cap.
abbrev Head := 4*(Bary:ℝ)^2+1
abbrev crown:ℝ:= Head+3
lemma hill : crown ≤ (Halo:ℝ)^2 :=by norm_num [crown,Head,Halo,Bary]
def alpha (z:ℕ) := slip z z/100
lemma tiny(z:ℕ): 0 < alpha z∧ alpha z ≤1:=by
 have h:= slip_pos z z; have hx: cap z z ≤1:= cap_le z z; have hp: (1:ℝ)≤ shelf z:=by exact_mod_cast (show 1≤ shelf z from fund_pos _)
 unfold cap at hx; unfold alpha; exact ⟨by positivity,by nlinarith⟩
def soil(s:ℕ)(ω: Site n→ℝ)(i x:Site n):= min (sizeD s x i+ω x) crown -- x center
local notation "K°"=>Halo*s
lemma grow(x i:Site n){w:Site n→ℝ}(h:0 < s)(p:0 ≤ w x)(t:soil s w i x<crown):separation x i≤ Halo*s:= rank_soon h (by unfold soil at t; have he:= (min_lt_iff.mp t).resolve_right (lt_irrefl _); linarith only [he,p,hill])
lemma roof(i x:Site n)(ω:Site n→ℝ): soil s ω i x ≤ crown:= min_le_right ..
lemma twin (x:Site n)(y z:Site n)(p:separation y z ≤1)(q: separation x z ≤ Halo*s)(t:SmallN s n)(v:0 < s) : |sizeD s x y-sizeD s x z| ≤ 8*(2*(Halo:ℝ)+4)/s:=by
 let A(i:Axis):ℝ:= lift (x-z) i; let Y(i:Axis):ℝ:= lift (z-y) i; let c:= 2*((2*(Halo:ℝ)+4))/(s:ℝ)
 have hK: (Halo:ℕ)≤ King:=by unfold King; omega
 have he(i): |A i|≤Halo*s:= (incrementX ..).trans (by exact_mod_cast q) -- expected real elaboration? coerces product, may parse Lean to Int.
 have hx(i):|Y i|≤1 :=(incrementX ..).trans (by have ht: pdist (z-y) ≤ 1:=(separation_comm z y).trans_le p; exact_mod_cast ht)
 have hz(i: Axis): (lift (x-y) i :ℝ)= A i + Y i:=by rw [rel_sum x z y (Nat.mul_le_mul_right s hK|>.trans' q) (by rw [separation_comm]; change separation y z ≤ ((4*(4*(1152+1)+1)):ℕ)*s; omega) t]; exact Int.cast_add ..
 unfold sizeD; rw [← sum_sub_distrib]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>c) (fun i _=>?_)).trans_eq (by rw [sum_const,card_univ,show Fintype.card Axis=4 from rfl,nsmul_eq_mul]; unfold c; push_cast; ring))
 change |(lift (x-y) i :ℝ)^2/_ - A i^2/_|≤_; have hp:1 ≤ (s:ℝ):= by exact_mod_cast (show 1 ≤ s from v)
 rw [hz i,← sub_div,abs_div,abs_of_nonneg (show 0≤ (s:ℝ)^2 by positivity)]; unfold c; rw [div_le_div_iff₀ (by positivity : 0<(s:ℝ)^2) (by positivity : (0:ℝ)<s)]
 have ht:|(A i+Y i)^2-A i^2| ≤ 2*((2*(Halo:ℝ)+4))*(s:ℝ):=by
    rw [show _^2-_=(2*A i+Y i)*Y i by ring,abs_mul]; refine (mul_le_of_le_one_right (by positivity) (hx i)).trans ((abs_add_le ..).trans ?_); rw [abs_mul]; -- tune
    apply (add_le_add (mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)) (hx i)).trans; norm_num [Halo,Bary]; push_cast; nlinarith
 exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans_eq (by ring)
lemma tune (i j x:Site n)(w: Site n→ℝ)(p:0≤ w x)(q: separation i j ≤ 1)(h:0<s)(t:SmallN s n): |soil s w i x-soil s w j x| ≤ 8*(2*(Halo:ℝ)+4)/s:=by
 let A(k):=soil s w k x; have he(i j)(u:separation i j≤1): A i-A j≤ 8*(2*(Halo:ℝ)+4)/s:=by
    by_cases v:A j=crown; · rw [v]; exact sub_nonpos.mpr (roof i x w)|>.trans (by positivity)
    have hg:= lt_of_le_of_ne (roof j x w) v; have hp:A j=sizeD s x j+w x:=by unfold soil at hg; rw [min_lt_iff] at hg; exact min_eq_left ((hg.resolve_right (lt_irrefl _)).le) -- needs unfold
    refine le_trans (b:=sizeD s x i-sizeD s x j) ?_ ((le_abs_self _).trans (twin x i j u (grow _ _ h p hg) t h)); rw [hp]; have hh:A i ≤ sizeD s x i+w x:=min_le_left ..
    linarith
 rw [abs_le]; exact ⟨by linarith only [he j i (separation_comm .. ▸ q)],he i j q⟩
lemma cap_rot(h:SmallN s n)(p:0 < s)(r:Signed)(x i y:Site n){ω ω':Site n→ℝ}(v:0≤ω y)(u:ω' (facet r x y)=ω y):soil s ω i y=soil s ω' (facet r x i) (facet r x y):=by
 have he:= facet_keeps r x y i; by_cases q:separation y i ≤ Halo*s
 · unfold soil; rw [reor (p:=q.trans (by unfold King; nlinarith)) (t:=h),u]
 let Q:=facet r x; have ho:soil s ω i y=crown:= le_antisymm (roof ..) (le_of_not_gt (fun t=> q (grow _ _ p v t))); rw [ho]; exact Eq.symm (le_antisymm (roof ..) (le_of_not_gt fun t=> q (he ▸ grow _ _ p (u.symm ▸ v :0 ≤ ω' (Q y)) t)))
end Guard
end YM.CF.BProof.Mesh.Nerve
