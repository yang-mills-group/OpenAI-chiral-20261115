import YM.CF.BProof.Nerve.Free
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
-- Needs local decision only. `jump` chooses weight to charge each Test row at its
-- leader at dawn. Nearby lines within color separation.H orientation charges invariant.
variable (U : Field n A Prop) (g:Field n A (Fin z))
variable (s:ℕ)
private abbrev blank(a:ℕ)(u:0<a) : Fin a:=⟨0,u⟩
def select(p:Fin (shelf z)→ Prop):Fin (shelf z):=if h:∃ i,p i then Classical.choose h else blank _ (fund_pos _)
abbrev due(z s u:ℕ)(X:Quint n)(f:Site n→ℝ)(i: Site n)(k:Fin (shelf z)):Prop:= slip z u/3 ≤ |Drift s X (update f i (jot z u k))|
def bump(X:Field n A ℝ)(w:A)(i:Site n)(u:ℕ):= jot z u (select (fun k:Fin (shelf z)=>∀ V∈ Lines (crowd U w) s i,due z s u V (X w) i k))
def jut(u:ℕ)(X:Field n A ℝ)(w:A)(i:Site n):= if (g w i).val = u then bump (z:=z) U s X w i u else X w i -- only g not U.Test only when active leader.s use
abbrev stageD(j:ℕ): Field n A ℝ:= Policy.stage 0 (jut U g s) j
local notation "jθ"=> jot
local notation "xν"=>Site n
variable {U g s}{w:A}{x: Site n}
lemma choice (t:Policy.Busy.goodHue U g (King*s))(j:ℕ)(X:Field n A ℝ)(v:ℝ)(x:Site n)(zv: A):
 ∀ V∈Lines (crowd U zv) s x, slip z j/3 ≤|Drift s V (update (X zv) x (bump (z:=z) U s X zv x j))|:=by
 let P(V:Quint n)(i:Fin (shelf z)):=due z s j V (X zv) x i; let S:=Lines (crowd U zv) s x; let Z:=select (fun i=>∀ V∈ S,P V i)
 suffices ∃ i,∀ V∈ S,P V i by intro V k; dsimp [bump,Guard.select]; rw [dif_pos this]; exact Classical.choose_spec this V k -- thunk
 let R(V):= (univ:Finset (Fin (shelf z))).filter fun i=>¬P V i; have hp(V)(h:V∈ S): (R V).card ≤ 1:=by
    obtain ⟨H,e⟩:= enters ..|>.1 h; apply Finset.card_le_one.mpr; intro i u k t; let Y(j'):=(update (X zv) x (jθ z j j')); have l(i)(p:i∈ R V):|Drift s V (Y i)|<slip z j/3:=lt_of_not_ge (mem_filter.mp p).2
    by_contra hg; have ht: |Drift s V (Y i)-Drift s V (Y k)| ≤ |Drift s V (Y i)| + |Drift s V (Y k)|:=abs_sub ..; have h1:=l _ u; have h2:=l _ t; have hf:Drift s V (Y i)-Drift s V (Y k)= wind V (lead V)*(jθ z j i-jθ z j k):=by
       have he:V (lead V)=x:=e; rw [tribute (i:=lead V) H.spread]; unfold Y; simp [he]; intro q w; unfold Y; have hx:V q≠ x:=fun v=> w (H.spread (v.trans he.symm)); rw [update_of_ne hx,update_of_ne hx]
    rw [hf,abs_mul,lead_p,one_mul] at ht; linarith only [ht,h1,h2,jumps z j i k hg,(slip_pos z j)]
 let d:= S.biUnion R; have he: d.card < shelf z:=(card_biUnion_le.trans (sum_le_sum hp)).trans_lt (by rw [sum_const,smul_eq_mul,mul_one]; exact Nat.lt_succ_of_le (counted t zv x)) -- tune methods
 obtain ⟨q,u,v⟩:=Finset.exists_mem_notMem_of_card_lt_card (he.trans_eq (by simp) : d.card<(univ:Finset (Fin (shelf z))).card)
 exact ⟨q,fun V p=> by_contra fun k=> v (mem_biUnion.mpr ⟨V,p,mem_filter.mpr ⟨mem_univ _,k⟩⟩)⟩
lemma persists{X:Quint n}(h:Test (crowd U w) s X)(j:ℕ)(H:(g w (target X)).val=j)(t:Policy.Busy.goodHue U g (King*s)): slip z j/3 ≤ |Drift s X (stageD U g s (j+1) w)| :=by
 let P:= stageD U g s j; let y:=target X; have he:= choice (s:=s) t j P 0 y w X ((enters ..).2 ⟨h,rfl⟩); refine he.trans_eq ?_; apply congrArg abs; unfold Drift Mode; apply sum_congr rfl; intro i p
 suffices py:update (P w) y (bump (z:=z) U s P w y j) (X i)= stageD U g s (j+1) w (X i) by rw [py]; -- tune
 by_cases q:X i=y; · rw [q,update_self,stageD,Policy.stage,jut,if_pos H]
 rw [update_of_ne q,stageD,Policy.stage,jut,if_neg]
 exact fun v=> t w _ _ ((Sleet.crowd_in ..).1 (h.crew i)) ((Sleet.crowd_in ..).1 (h.crew _)) q (cost0 h ..) (Fin.ext (v.trans H.symm))
local notation "Fβ"=>stageD U g s
lemma afterD (u:ℕ) {w:A} (x:Site n){s p:ℕ}(v:u < p) (g:Field n A (Fin z))(H:(g w x).val=u)(Z:p≤z): stageD U g s p w x=stageD U g s (u+1) w x :=by
 induction p,v using Nat.le_induction with | base=> rfl| succ k hx ih=> rw [stageD,Policy.stage,jut,H,if_neg (by omega)]; exact ih (by omega)
lemma beforeD (u k:ℕ)(v:u≤ k)(x:Site n)(w:A)(h:(g w x).val=k) : Fβ u w x=0:=by induction u with|zero=>rfl|succ n ih=> rw [stageD,Policy.stage,jut,h,if_neg (by omega)]; exact ih (by omega)
lemma valid (x:Site n)(zv:A): 0≤ Fβ z zv x ∧ Fβ z zv x≤ cap z ((g zv x).val):=by
 let t:=(g zv x).val; rw [afterD t (x) (g zv x).isLt g rfl (le_refl _)]; unfold stageD; rw [Policy.stage,jut,if_pos (show _=t from rfl)]; exact table z t _
theorem bright(X:Quint n)(u:Test (crowd U w) s X)(t:Policy.Busy.goodHue U g (King*s)): slip z z/6 ≤|Drift s X (Fβ z w)|:=by
 let h(q):=Drift s X (Fβ q w); let P(i:Fin 6):=(g w (X i)).val; let i:=P (lead X); have hh:= persists u i rfl t; change slip z i/3 ≤ |h (i+1)| at hh; have h1(z'):|wind X z'|≤1:=(permit X).2.2.1 z'; have ht(p:Fin 6): |Fβ (i+1) w (X p)-Fβ z w (X p)| ≤ cap z (i+1):=by
    by_cases u:P p ≤ i
    · rw [afterD (p:=z) (P p) (X p) (g w (X p)).isLt g rfl le_rfl, afterD (P p) (X p) (by omega) g rfl (show i+1≤z from (g w _).isLt)]; rw [sub_self,abs_zero]; exact mul_nonneg (by positivity) (slip_pos _ _).le
    let u':= valid (U:=U) (s:=s) (g:=g) (X p) w; rw [beforeD _ (P p) (by omega) _ _ rfl, zero_sub,abs_neg,abs_of_nonneg u'.1]; exact u'.2.trans (mul_le_mul_of_nonneg_left (Guard.reverse z (show i+1≤ P p by omega)) (by positivity))
 let q:=cap z (i+1); have hp: |h (i+1)- h z| ≤ 6*q:=by
    unfold h Drift Mode; rw [←sum_sub_distrib]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>q) (fun i' v=>?_)).trans_eq ?_)
    · rw [←mul_sub,add_sub_add_left_eq_sub,abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (h1 _)).trans (ht _)
    simp
 change _ ≤ |h z|; linarith only [Guard.reverse z ((g w _).isLt.le : i≤z),hp,(after z i : 6*q ≤ _),hh,(abs_sub_abs_le_abs_sub (h (i+1)) (h z) : _)] -- tune
end Guard
end YM.CF.BProof.Mesh.Nerve
