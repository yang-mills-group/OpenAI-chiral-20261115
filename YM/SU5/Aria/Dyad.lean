import YM.SU5.Aria.Gale
/-! # Dyadic distributions with support gates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria
open Set Function Filter Metric
open Germ
open scoped Topology InnerProductSpace
inductive Mist (α:Type*) where
| point(x:α)
| midP (D E: Mist α)
variable {α β γ E F:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup F][NormedSpace ℂ F]
namespace Mist
def mean (D:Mist α)(f:α→E):E:=match D with
 | point x=>f x
 | midP A B=> (1/2:ℂ) • (A.mean f+B.mean f)
def holds (D:Mist α)(p:α→Prop):Prop:=match D with
 | point x=>p x
 | midP A B=> A.holds p ∧ B.holds p
def reaches (D:Mist α)(x:α):Prop:=match D with
 | point y=>x=y
 | midP A B=> A.reaches x ∨ B.reaches x
def via (D:Mist α)(f:α→Mist β):Mist β:=match D with
 | point x=> f x
 | midP A B=> midP (A.via f) (B.via f)
abbrev onFn (D:Mist α)(f:α→β):Mist β := D.via (point ∘ f)
variable (D: Mist α) (f:α→E)
lemma hold_via (s:α→Mist β)(p:β→Prop):(D.via s).holds p ↔ D.holds (fun i=>(s i).holds p):=by induction D with
 | point a => exact Iff.rfl
 | midP a b i j => simp only [holds,via,i,j]
lemma reaches_via (s:α→Mist β)(x:β):(D.via s).reaches x ↔ ∃ a,D.reaches a ∧ (s a).reaches x:=by induction D with
 | point a => simp [reaches,via]
 | midP a b i j => simp [reaches,via,i,j,or_and_right,exists_or] -- tune
lemma holds_at {p:α→Prop} : D.holds p ↔ ∀ a,D.reaches a →p a:=by induction D with
 | point a => simp [reaches,holds]
 | midP a b i j=> simp only [holds,reaches,i,j]; grind
lemma solves (p:α→Prop)(t:∀ i,p i):D.holds p:= (D.holds_at).2 fun i _=>t i
lemma promotes{p q:α→Prop}(t:∀ i,p i→q i)(h:D.holds p):D.holds q:= D.holds_at.mpr fun a k=>t _ (D.holds_at.mp h a k)
lemma cradles{p q:α→Prop}(h:D.holds p)(t:D.holds q): D.holds (fun i=>p i∧q i):= D.holds_at.mpr fun i v=> ⟨D.holds_at.mp h i v,D.holds_at.mp t i v⟩
lemma someReach : ∃ a,D.reaches a:=by induction D with
 | point i=> exact ⟨i,rfl⟩
 | midP A B i j=> obtain ⟨a,i⟩:=i; exact ⟨a,Or.inl i⟩
lemma hasReach [DecidableEq α] : {x|D.reaches x}.Finite:=by induction D with
 | point x => simp only [reaches]; exact finite_singleton _
 | midP A B i j=> exact i.union j
lemma mean_via (s:α→Mist β)(g:β→E) : (D.via s).mean g=D.mean (fun a=> (s a).mean g):=by induction D with
 | point a => rfl
 | midP a b i j=>simp [via,mean,i,j]
lemma mean_onFn (s:α→β)(g:β→E): (D.onFn s).mean g=D.mean (g ∘ s):= D.mean_via _ g
lemma mean_const (x:E): D.mean (fun _=>x)=x:=by induction D with
 | point i=>rfl
 | midP A B i j=> simp only [mean,i,j,smul_add,←add_smul]; norm_num
lemma mean_linear (L:E→ₗ[ℂ] F): D.mean (L ∘ f)=L (D.mean f):=by induction D with
 | point a=> rfl
 | midP A B i j=> simp only [mean,i,j,map_smul,map_add]
lemma mean_linear' (L:E→L[ℂ] F): D.mean (fun i=>L (f i))=L (D.mean f):= D.mean_linear f L.toLinearMap
lemma mean_plus (g:α→E): D.mean (f+g)=D.mean f + D.mean g:=by induction D with
 | point a=> rfl
 | midP A B i j=> simp only [mean,i,j,smul_add]; abel
lemma mean_smul (c:ℂ): D.mean (c • f)=c • D.mean f:=by induction D with
 | point a=> exact Pi.smul_apply c f a
 | midP A B i j=> rw [mean,i,j,mean,←smul_add,smul_comm]
lemma mean_sub (g:α→E): D.mean (f-g)=D.mean f-D.mean g:=by induction D with
 | point a=> rfl
 | midP A B i j=> simp only [mean,i,j,smul_add,smul_sub]; abel
lemma mean_congr {g:α→E} (p:D.holds fun a=> f a=g a): D.mean f=D.mean g:=by induction D with
 | point i=>exact p
 | midP A B i j=>rw [mean,mean,i p.1,j p.2]
lemma mean_budget (C:ℝ)(p:D.holds fun a=>‖f a‖≤C): ‖D.mean f‖≤C:=by induction D with
 | point a => exact p
 | midP A B i j=> rw [mean,norm_smul]; norm_num; linarith [norm_add_le (A.mean f) (B.mean f),i p.1,j p.2]
lemma mean_budget_dist (g:α→E)(C:ℝ)(p:D.holds fun i=>dist (f i) (g i) ≤ C): dist (D.mean f) (D.mean g) ≤ C:=by rw [dist_eq_norm,←mean_sub]; simp_rw [dist_eq_norm] at p; exact D.mean_budget (f-g) C p
lemma ceiling (x:E)(C:ℝ)(p:D.holds fun i=> dist (f i) x ≤ C): dist (D.mean f) x ≤ C:=
 (D.mean_const x) ▸ (show dist (D.mean f) (D.mean fun _=>x) ≤ _ from D.mean_budget_dist f _ C p)
lemma mean_comm (s:Mist β)(f:α→β→E): D.mean (fun i=>s.mean (f i))= s.mean (fun b=>D.mean fun i=>f i b):=by
 induction D with
 | point i=> rfl
 | midP A B i j=>
   rw [mean,i,j, show (fun b:β=>(midP A B).mean (fun i=>f i b))= (1/2:ℂ) • ((fun b=> A.mean fun i=>f i b)+(fun b=>B.mean fun i=>f i b)) from rfl,s.mean_smul,s.mean_plus]
end Mist
end YM.CF.Buffered.Afterglow.Tower.Aria
