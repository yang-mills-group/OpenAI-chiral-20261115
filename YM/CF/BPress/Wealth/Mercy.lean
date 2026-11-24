import YM.CF.BPress.Wealth.Canon
import YM.CF.BPress.SheetSum
/-! Core fields defined from gap draws and flags. Reader equality exact on all core zones from columns and sampler noise (even invalid parameters), with canon option keys. Severe indicator actual relative to A via same sky. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure
open scoped Topology BigOperators Classical Matrix
variable {s:Side} {b:BandWidth}(X : Bands s b) (p:X.Index)
open SU
-- implies if any reading of a canon key (evaluated under fallback if beyond all collars) then its actual orientation. Pay chart bound etc per source of keys.
lemma key_orient {t:Per s}{z:FlatLink s}{a:X.Air}(h:keyV X t z= some a): a.2.2=z.2:=by unfold keyV at h; cases i:slot X t with| none=>simp [i] at h| some i=> rw [i] at h; simp only [Option.bind_some] at h; split at h; exact congrArg (fun i:X.Air=>i.2.2) ((Option.some.inj h).symm); contradiction -- tune
lemma represents {j:Link s}{a:X.Air}(h:edgeKey X j=some a)(y:ℝ): background y j=magnetH y a.2.2:=by
 rcases link_cases j with ⟨v,w⟩|w; rw [w,EdgeKey_H] at h; rw [w,key_orient X h]; simp [fl,background,magnetH,backgroundDir]; rw [w,EdgeKey_V] at h; contradiction
lemma normal_background (t: Per s)(x: Tri s)(y:ℝ): background y (vl t x)=1:= background_normal ..
lemma horizontal_background (t: Per s)(x: FlatLink s)(y:ℝ) : background y (fl t x)=magnetH y x.2:= congrFun (horiz_background (t:=t) y) x

/-- field reconstruction on near-collar/gap information. apply group multiplication by noise for ALL pay keys, including copy collars where key is a face link at a different time. Warning: only valid as a reader at `halo cloak` of gaps. -/
def angleBeg (y:ℝ)(w : Bills X E) (e:Link s) := (edgeKey X e).elim (background y e) w
def anglePaid (y:ℝ)(w:Bills X E)(U:Micro s) (e:Link s):= angleBeg X y w e * (if e∈X.coins then U e else 1)
structure Mission (y:ℝ)(K:Bills X E)(V U:Micro s):Prop where
 mission (i:X.Index): Lattice.Agrees (halo (cloak b) (X.gap i)) U (anglePaid X y K V)
 lens : ∀ i:X.Air, U (X.skylink i)=K i
 park : ∀ i∈ X.poles,U i=1

namespace Mission
variable {K : Bills X E} {y:ℝ}{V U:Micro s}{X}
lemma narrates (h: Mission X y K V U)(p:X.Index)(j:Link s)(v:j∈inside (halo (cloak b) (X.gap p))): U j=anglePaid X y K V j:= h.mission p j ((inside_iff ..).mp v).1 ((inside_iff ..).mp v).2
end Mission
-- Severe definition even when use angle v tests. chart need witness on all soft, use Atlas.toChart.
variable (κ:ℝ)(y:ℝ)
def severe (v:Bills X E)(o:X.Hcols) := ∃ a:Bands.Body (B:=b), κ * temp y < chord (v (o,a)) (magnetH y a.2) -- b' rename

def chosen (w:Bills X E) : Finset X.Hcols:= univ.filter (severe X κ y w)
def soft (K:Bills X E) (W: Sheet.Atlas) : Bills X group.Color:= fun i=> W.logV ((magnetH y i.2.2)⁻¹ * K i)
def low (S:Finset X.Hcols){D : Type*}[Zero D](v:X.Air→ D): X.Air→D:= fun i=> if i.1∈ S then 0 else v i
def softAl (K:Bills X E)(W:Sheet.Atlas): Bills X group.Color:= low X (chosen X κ y K) (soft X y K W)
variable {X}
lemma marksev (x:Bills X E)(j): j∈ chosen X κ y x ↔ severe X κ y x j:= by simp [chosen]
lemma choose_meas (X:Bands s b) (j) : MeasurableSet {v:X.Air→ E | j∈chosen X κ y v}:=by simp_rw [marksev,severe, Set.setOf_exists]; exact MeasurableSet.iUnion fun i=> measurableSet_lt measurable_const ((chord.cont (G:=group)).measurable.comp (f:=fun v:X.Air→ E=> (v (j,i),magnetH y i.2)) ((measurable_pi_apply (j,i)).prodMk measurable_const)) -- tune stuck
lemma ream (K:Bills X E)(i:X.Air)(p:i.1∉ chosen X κ y K): chord (K i) (magnetH y i.2.2) ≤ κ*temp y:= le_of_not_gt fun e=> p (marksev ..|>.mpr ⟨i.2,e⟩)
lemma alpha_price (u v : E): group.chord (u⁻¹*v)= chord v u:=by rw [←chord.one,←chord.left v u u⁻¹,inv_mul_cancel]
lemma unsevere (W:Sheet.Atlas)(p:κ * temp y < W.δ) (K : Bills X E){i:X.Air}(q:i.1∉chosen X κ y K) :
 K i=magnetH y i.2.2 * group.lieExp (softAl X κ y K W i) ∧ ‖softAl X κ y K W i‖ ≤ W.C* (κ * temp y):=by
 let t :=magnetH y i.2.2; have h: group.chord (t⁻¹*K i) ≤ _ := (alpha_price ..).le.trans (ream κ y K i q) -- tune
 unfold softAl soft low; simp only [if_neg q]; rw [chord.Chart.logV,if_pos (h.trans_lt p)]; refine ⟨?_, (W.snap_bound _ (h.trans p.le)).trans (mul_le_mul_of_nonneg_left h W.span.le)⟩; rw [W.read _ (h.trans p.le),mul_inv_cancel_left]
lemma soft_bounds (W:Sheet.Atlas)(t:κ*temp y< W.δ) (v:0≤κ*temp y)(K:Bills X E) (i:X.Air): ‖softAl X κ y K W i‖ ≤ W.C*(κ*temp y):=by by_cases h:i.1∈ chosen X κ y K; rw [softAl,low,if_pos h,norm_zero]; exact mul_nonneg W.span.le v; exact (unsevere κ y W t K h).2
lemma raw_le {R:ℝ} (p:0≤R)(W:Bills X group.Color) (k:∀ i, ‖W i‖ ≤ R) (e:Link s): ‖canon X W e‖≤ R:=by change ‖(edgeKey X e).elim 0 W‖≤ _; cases h:edgeKey X e with|none=> simpa using p| some i=>exact k _
-- `ε` same at all nodes even though frame costs in background are weaker
-- need noise actual support and χ closed tolerances, not just weight-nonzero (can treat null excluded). no soft across poles tested here beyond `Mission`.
def ToneNoise (U: Micro s):=∀ i:Link s, group.chord (U i) ≤ xi y
variable {K:Bills X E}{U V:Micro s}
lemma costBeg (h:Mission X y K V U)(v:ToneNoise y V){p:X.Index} {j:Link s}(w:j∈ inside (halo (cloak b) (X.gap p))) : chord (U j) (angleBeg X y K j)≤ xi y:=by
 rw [h.narrates p j w, anglePaid]; split; next t=> nth_rw 2 [←mul_one (angleBeg X y K j)]; rw [chord.left,chord.one]; exact v j
 next t=> rw [mul_one,chord.refl]; exact (group.chord_nonneg _).trans (v j)
def actuated (A:Directions group s) (i:Link s) : E:= background y i* group.lieExp (A i)
lemma use_core {t:ℝ}(p:κ*temp y < t)(W:Sheet.Atlas)(w:t=W.δ)(g:Mission X y K V U)(x: ToneNoise y V)(i:Link s) (h:∀ a,edgeKey X i=some a→ a.1∉ chosen X κ y K){q:X.Index}(e:i∈inside (halo (cloak b) (X.gap q))): chord (U i) (actuated y (canon X (softAl X κ y K W)) i) ≤ xi y:=by
 apply le_trans _ (costBeg y g x e); unfold actuated; change chord _ (_*group.lieExp (raw _ _ _))≤_; unfold raw angleBeg; cases v:edgeKey X i with| none=>simp| some a=> rw [represents X v y]; simp only [Option.elim_some]; rw [show K a= _ from (unsevere κ y W (w ▸ p) K (h a v)).1] -- tune
lemma near_back (w:0 ≤ κ*temp y)(g:Mission X y K V U)(x:ToneNoise y V)(j:Link s) (h:∀ a,edgeKey X j=some a→ a.1∉ chosen X κ y K){q:X.Index}(e:j∈inside (halo (cloak b) (X.gap q))): chord (U j) (background y j) ≤ xi y + κ*temp y:=by
 apply le_trans (chord.triangle (U j) (angleBeg X y K j) _); apply add_le_add (costBeg y g x e); unfold angleBeg; cases v:edgeKey X j with| none=> simpa using w| some a=>rw [represents X v y]; exact ream κ y K a (h a v) -- tune
end YM.CF.BPress.Wealth
