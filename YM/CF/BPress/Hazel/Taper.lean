import YM.CF.BPress.Hazel.Stitch
import YM.CF.BPress.Hazel.MarkDown
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch Clipγ Letter
variable {X:Bands s B}(W:Rental)(R:Hangar s)
def Xactual (S:Seal (SiteX X R))(J:Letter X)(K:Tiling s)(U:Micro s):= tree K univ (safe X R W S) U J.G
-- eq:B-tactual. constant path branch to patch preserved X with taper=0. (all inputs). note DP≥ DT^N for licensing.
def Kactual (S:Seal (SiteX X R))(A:Letter X)(K:Tiling s)(U:Micro s)(v:ℝ): Paint s:= fun x=> if blink X W R S x=0 then fullM (Xactual W R S A K U x).val else A.H W (blink X W R S x*v) x

variable {W R}{A:Letter X}{S:Seal (SiteX X R)}{U: Micro s}{K:Tiling s}{g h l c m:ℝ}
structure Stopped (A:Letter X) (K:Tiling s)(p:Grip X W R S A U g h c) (εX εH:ℝ):Prop where
 key: K.r=1
 old : g≤ soil K.b
 hull : (cloakT K+1)*8 ≤ W.T.val
 tone : Speed B W g h c
 finalX : inheritance K.b≤ εX
 finalKe : κ_tri * inheritance K.b ≤ εH
 finalK : h+priceTone * (chk W.T*3) ≤ εH
 ring : Rings U univ (climate K.b)
variable {p:Grip X W R S A U g h c}(t:Stopped A K p l m) {x:Site s} -- z type garbage
include t
namespace Stopped
lemma safeU : Grains (safe X R W S) U A.G (H W A) (soil K.b) h:= ⟨fun i v=> ((p.exterior t.tone).grow i v).trans t.old, (p.exterior t.tone).timing⟩ -- underline
lemma healthX (i:Link s): urgent U i (Xactual W R S A K U) ≤ inheritance K.b:= tree_urgent t.key U _ (subset_univ _) t.ring (t.safeU).grow _ _ (subset_univ _)
-- simp with tActual branch at zero taper needs agreement beyond bound
lemma activeIn(f: blink X W R S x ≠ 0): halo (cloakT K+1) {x} ⊆ safe X R W S:=by
 intro i u; apply mem_compl.mpr; intro wt; apply f; obtain ⟨z,v,h⟩:=halo_spec.mp u; rw [mem_singleton.mp v] at h; exact tTurnZero (halo_spec.mpr ⟨i,wt,(separation_comm ..).le.trans h⟩) t.hull
lemma Xsharp(x:Site s) (q:halo (cloakT K) {x} ⊆ safe X R W S): Xactual W R S A K U x= A.G x:= tree_eq t.key _ _ (subset_univ _) t.ring t.safeU.grow x q
lemma lands (v:ℝ)(x:Site s)(q: halo (cloakT K) {x} ⊆ safe X R W S): Kactual W R S A K U v x=A.H W (blink X W R S x*v) x:= by
 unfold Kactual; split; next h=> rw [h,zero_mul,H_seed W A p.tint p.power.summer,Xsharp t x q]
                                                                                                                                                                            -- tune
                                                                                                                                                                            --
                                                                                                                                                                            --
 next h=>rfl
lemma groomed(h:x∉halo W.T.val (Danger X R W S)): Xactual W R S A K U x=A.G x ∧ ∀ v,Kactual W R S A K U v x=A.H W v x:=by
 have he:blink X W R S x=1:=tAlive h; have ht:halo (cloakT K) {x}⊆ safe X R W S:=(Corona.halo_mono (Nat.le_succ _) le_rfl).trans (t.activeIn (he.trans_ne one_ne_zero)); exact ⟨t.Xsharp x ht,fun v=> by rw [t.lands v x ht,he,one_mul]⟩
lemma K_seed (x:Site s): Kactual W R S A K U 0 x= fullM (Xactual W R S A K U x).val:=by
 unfold Kactual; split; rfl; next h=> rw [mul_zero,H_seed W A p.tint p.power.summer,t.Xsharp x ((Corona.halo_mono (Nat.le_succ _) le_rfl).trans (t.activeIn h))]
lemma Kplan (x:ℝ):MatPlan (Kactual W R S A K U x):=by intro i; unfold Kactual; split; exact Spin.Sym.full _ (vote_unit _); exact Hplan W A p.tint _ _ -- tune
lemma Ksmooth (x:Site s): ContDiff ℝ ∞ (fun v=>Kactual W R S A K U v x):=by unfold Kactual; split; exact contDiff_const; exact (Hsmooth W A p.tint x).comp (by fun_prop)

-- parameter products.
omit t in
lemma prod_active(w:u ∈ Meadow.active)(e:v ∈Hotel): u*v∈Meadow.active:=by
 obtain ⟨p,q⟩:=w; obtain ⟨x,y⟩:=e; -- absurd binders tune
 exact ⟨by nlinarith, by nlinarith⟩
lemma rate (x:Site s): LipschitzOnWith priceTone (fun v=> Kactual W R S A K U v x) Meadow.active:= by
 unfold Kactual; split; refine (LipschitzOnWith.of_dist_le_mul (fun x u y v=> by simp)); -- tune method
 let a:= blink X W R S x; have he:= Hazel.between X W R S x; change a∈ Hotel at he; let g(v):= a*v; refine ((H_pace W A p.tint x).comp (LipschitzOnWith.of_dist_le_mul (K:=1) (f:=g) (fun i u j t=>?_)) ?_).weaken (mul_one ..).le; -- composition defeq
 · rw [Real.dist_eq,Real.dist_eq,show g i-g j=a*(i-j) from (mul_sub ..|>.symm),abs_mul, abs_of_nonneg he.1]; exact mul_le_mul_of_nonneg_right (by simpa using he.2) (abs_nonneg _)
 intro i u; unfold g; rw [mul_comm]; exact prod_active u he

private lemma activated (i:Link s)(h: blink X W R S i.1 ≠ 0 ∨ blink X W R S (endAt i) ≠ 0): let T (x:Site s):= halo (cloakT K) {x}; T i.1⊆ safe X R W S ∧ T (endAt i) ⊆ safe X R W S:=by
 intro C; let k:=cloakT K; let P:=safe X R W S; have he(x y) (u:blink X W R S x≠0) (v:separation x y≤1) : halo k {y}⊆P:=by
    intro i h; obtain ⟨a,h,p⟩:=halo_spec.mp h; rw [mem_singleton.mp h] at p; apply t.activeIn u; exact halo_spec.mpr ⟨x,mem_singleton_self _,(separation_triangle _ y _).trans ((Nat.add_le_add v p).trans_eq (Nat.add_comm ..))⟩
 rcases h with h|h; exact ⟨he _ _ h (by simp),he _ _ h (Lat.oneTouch ..)⟩; exact ⟨he _ _ h ((separation_comm ..).le.trans (Lat.oneTouch ..)), he _ _ h (by simp)⟩
lemma Kmark (i:Link s)(v:ℝ) (hv:v∈ Meadow.active): fare U (Kactual W R S A K U v) i ≤ m:=by
 by_cases l:blink X W R S i.1 ≠0 ∨ blink X W R S (endAt i) ≠0; swap
 · unfold fare Kactual; rw [if_pos (not_not.mp (not_or.mp l).1),if_pos (not_not.mp (not_or.mp l).2)]; exact (fee_base.choose_spec _ U (Xactual W R S A K U) i).trans ((mul_le_mul_of_nonneg_left (healthX t i) κ_tri.property).trans t.finalKe) -- tune let
 obtain ⟨r₁,r₂⟩:= activated t i l; let a:=blink X W R S; let xA:=i.1; let yA:=endAt i; let v₁:= a xA*v; let v₂:=a yA*v; have ht:∀ x,a x*v∈Meadow.active:= fun x=>mul_comm (a x) v|>.symm ▸ prod_active hv (Hazel.between X W R S x); have hV:dist v₁ v₂ ≤ chk W.T*3:=by rw [Real.dist_eq,show v₁-v₂=(a xA-a yA)*v from (sub_mul ..|>.symm), abs_mul]; apply mul_le_mul (t_rate X R W S i) _ (abs_nonneg _) (by unfold chk; positivity); obtain ⟨l,h⟩:= hv; rw [abs_le]; constructor <;> linarith
 unfold fare; rw [t.lands _ _ r₁,t.lands _ _ r₂]; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (swivelC (U i) (A.H W v₁ yA)) _); apply t.finalK.trans'; apply add_le_add; · exact t.safeU.timing v₁ (ht xA) _ ((inside_iff ..).mpr ⟨r₁ (halo_subset _ _ (mem_singleton_self _)), r₂ (halo_subset _ _ (mem_singleton_self _))⟩)
 rw [Paint.iso,←dist_eq_norm]; exact le_trans ((A.H_pace W p.tint yA).dist_le_mul v₁ (ht xA) v₂ (ht yA)) (mul_le_mul_of_nonneg_left hV priceTone.property) -- tune norm

lemma on_torus : Grains (univ) U (Xactual W R S A K U) (Kactual W R S A K U) l m:= ⟨fun i _=>(t.healthX _).trans t.finalX,fun i v k h=> t.Kmark _ _ v⟩
end Stopped
end YM.CF.BPress.Hazel
