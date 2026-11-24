import YM.SU5.FiniteGaugeData.Poin.Grane
/-! # MULTIVIEW tilt estimates to generate separated Eu readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set Mink Mink.General Mink.Lorentz Real Flute MeasureTheory OS OS.Semigroup
open scoped Topology BigOperators NNReal
local notation "a"=>timeAxis
variable {H:Hilbert}{n:ℕ}{ι:Type}(T:Canopy H ι)(S:OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ x:E4,M S x Ω.val=Ω.val)
variable (s:SO)(x:Points n)
namespace Canopy
open scoped Classical
variable (w:Fin n→ T.Chip)(L:List (Fin n))
local notation "M"=> meanE S Ω.val
abbrev Pear(n:ℕ):= List (Fin n)
abbrev Sr := meanE S Ω.val (T.senses w) (T.credit w) x L
-- every separately billable.NN t.St(L) estimate. LARGE continuum need if before/after rotations.
structure Tile :Prop where
 turn(n:ℕ)(T0:SO)(x:Points n)(w:Fin n→ T.Chip)(L L':Pear n)
     (_: L.Perm (Each n))(_:L'.Perm (Each n))(_: ProofOrder x timeAxis L)(_:ProofOrder (turnO T0.val x) timeAxis L'):
     T.Sr S Ω x w L=T.Sr S Ω (turnO T0.val x) (T.stampE T0 w) L'
variable (V:T.Tile S Ω)
include V
lemma tilt_good : T.Warrant S Ω:=⟨fun n w v=>⟨fun x h t=> V.turn n v x w _ _ (.refl _) (.refl _) (orderX x h) (orderX _ t)⟩⟩
omit V
abbrev Prices (s:SO)(L:Pear n):Prop:= L.Perm (Each n)∧ ProofOrder (turnO s.val x) timeAxis L
local notation "Vt"=> stampE T
@[simp] lemma Em (s u:SO): Vt s (Vt u w)= Vt (s*u) w:=by funext i; unfold stampE; rw [Emult]
@[simp] lemma Et : Vt 1 w=w:=by funext i; exact Eini ..
include V
abbrev fareZ := T.Sr S Ω (turnO s.val x) (stampE T s w) L
lemma paintInto (p:Prices x s L)(T₁:SO)(q:Pear n)(z:Prices x T₁ q): fareZ T S Ω s x w L=fareZ T S Ω T₁ x w q:=by
 let g:=T₁*s⁻¹; let y:= turnO s.val x; have hG:g*s=T₁:=by unfold g; group
 have he: turnO g.val y= turnO T₁.val x:=by unfold y; rw [Lynx,hG]
 have h:ProofOrder (turnO g.val y) timeAxis q:= he ▸ z.2; refine ( V.turn n g y (Vt s w) L q p.1 z.1 p.2 h ).trans ?_; rw [he,Em,hG]
omit V
def ornate (s:Points n) (w:Fin n→ T.Chip):ℂ:= if h:s∈conf n then let v:= CountOra s h; fareZ T S Ω v.choose s w v.choose_spec.choose else 0
include V
local notation "K"=> T.ornate S Ω
lemma shines (p:x∈conf n) (e: Prices x s L): ornate T S Ω x w=fareZ T S Ω s x w L:=by
 unfold ornate; rw [dif_pos p]; exact paintInto T S Ω _ x w _ V (CountOra x p).choose_spec.choose_spec _ L e
lemma sing (e:L.Perm (Each n))(h:ProofOrder x a L): K x w= Sr T S Ω x w L:=by
 rw [shines T S Ω 1 x w L V (order_in x timeAxis L e h) (show Prices x 1 L from ⟨e,h⟩),fareZ,Et]; rfl
lemma openly(p:x∈conf n): ContinuousAt (fun x=> T.ornate S Ω x w) x:=by
 obtain ⟨y,L,t,v⟩:=CountOra x p; let U(x:Points n):=fareZ T S Ω y x w L; have hu:ContinuousAt U x:= (grounded S Ω.val _ _ _ _ v).comp (stale y).continuousAt -- cont proof
 apply hu.congr; filter_upwards [(conf_open _).mem_nhds p,((stale ..).continuousAt (x:=x)).eventually ((PEye a L).mem_nhds v)] with x h k; exact (shines T S Ω y x w L V h ⟨t,k⟩).symm
lemma fluent (p:x∈conf n): ornate T S Ω x w = ornate T S Ω (turnO s.val x) (T.stampE s w):=by
 obtain ⟨y,L,t,v⟩:= CountOra (turnO s.val x) (warm_π x s p); rw [Lynx] at v; rw [shines T S Ω (y*s) x w L V p ⟨t,v⟩, shines T S Ω y _ _ L V (warm_π x s p) (show Prices _ _ _ from ⟨t,by rwa [Lynx]⟩)]; unfold fareZ; rw [Lynx,Em]
include hΩ
lemma bliss(p:x∈conf n)(u:E4): ornate T S Ω x w= ornate T S Ω (moving u x) w:=by
 obtain ⟨z,F,g,h⟩:=CountOra x p; have he: turnO z.val (moving u x)=moving (walk z.val u) (turnO z.val x):= PiLp.ext fun i=> map_add ..; have hv:moving u x∈conf n:= fun i j v=> p (add_right_cancel (show x i+u=x j+u from v)); rw [shines T S Ω z x w F V p ⟨g,h⟩, shines T S Ω z (moving u x) w F V hv ?_]; unfold fareZ Sr; rw [he,dragons S Ω.val hΩ _ _ _ _ _ h]; exact ⟨g,he ▸ ((convOrder _ _ _).mpr h)⟩
#print axioms tilt_good
#print axioms bliss
#print axioms shines
-- even reindexing.
omit V hΩ
abbrev regP (e:Equiv.Perm (Fin n))(x:Points n):= points fun i=>x (e i)
lemma faz(e:Equiv.Perm (Fin n)): Sr T S Ω x w (L.map e) = Sr T S Ω (regP e x) (w ∘ e) L:= by
 refine congrArg (fun o:H.Op=>inner ℂ Ω.val (o Ω.val)) (Eq.trans (Film_map ..) rfl)
lemma fate (e: Equiv.Perm (Fin n)): ProofOrder x a (L.map e) ↔ ProofOrder (regP e x) a L:= List.pairwise_map
variable (e:Equiv.Perm (Fin n)) (b:Axis)
include V
lemma uniformizes (p:x∈conf n) : ornate T S Ω x w=ornate T S Ω (regP e x) (w ∘ e):=by
 let y:= regP e x; let F:=w ∘ e
 have hh: y∈conf n:= p.comp e.injective
 obtain ⟨z,L,v,h⟩:=CountOra y hh
 have he:turnO z.val y=regP e (turnO z.val x):=rfl; have Hx:Prices x z (L.map e):= ⟨(v.map e).trans (Equiv.Perm.map_finRange_perm _), (fate _ _ e).2 (he ▸ h)⟩; exact (shines T S Ω z x w (L.map e) V p Hx).trans ((faz T S Ω _ _ L e).trans (shines T S Ω z y F L V hh ⟨v,h⟩).symm)
#print axioms uniformizes
-- still real plate recovery in any paying chronology without a-coplanar overlap.
variable {Hv:Hilbert} (Y:OS.Semigroup Hv b)(Ow:Hv) (Φ:T.Chip→Hv.Op)
local notation "Xb" X:max=>meanE Y Ow (Φ ∘ w) (T.credit w) X L
variable (q: ∀ x:Points n, ∀ F:List (Fin n), F.Perm (Each n)→ ProofOrder x timeAxis F → ProofOrder x b L→ T.Sr S Ω x w F=meanE Y Ow (Φ ∘ w) (T.credit w) x L)
private abbrev Qx (t:ℝ) := x + t • points (fun i:Fin n=> (i.val:ℝ) • basis timeAxis)
omit V in
lemma march : ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),∃ L:List (Fin n), L.Perm (Each n)∧ ProofOrder (Qx x t) a L:=by
 refine Eventually.mono (p:=fun t:ℝ=> Injective (clockV a (Qx x t))) ?_ (fun y z=>?_); swap; · exact SortApp _ z
 apply Eventually.mono (p:=fun t:ℝ=> ∀ i j: Fin n,i≠j→ (Qx x t) i a≠ (Qx x t) j a) ?_ (fun i p x y h=> by_contra fun u=>p x y u h)
 refine eventually_all.mpr (fun i=> eventually_all.mpr (fun j=>?_)); by_cases h: i=j; · exact Eventually.of_forall (fun _ p=> False.elim (p h))
 by_cases k: x i a = x j a; · filter_upwards [self_mem_nhdsWithin] with t p _ w; have hp:t≠0:=(Set.mem_Ioi.mp p).ne'; simp [Qx,k,hp] at w; exact h (Fin.ext w)
 have he(i:Fin n): Continuous (fun t:ℝ=>(Qx x t) i a):= by unfold Qx; fun_prop
 refine Eventually.mono (p:=fun t=> (Qx x t) i a≠ (Qx x t) j a) (f:=𝓝[>] 0) (nhdsWithin_le_nhds ( (isOpen_ne_fun (he i) (he j)).mem_nhds (?_))) (fun t p _=>p); simp [Qx,k]
include q
lemma soliloque (p:L.Perm (Each n))(H':ProofOrder x b L): ornate T S Ω x w= meanE Y Ow (Φ ∘ w) (T.credit w) x L:= by
 have ht:=order_in x b L p H'; have hw : Tendsto (Qx x) (𝓝[>] 0) (𝓝 x):= ((show Continuous (Qx x) from continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 x (by simp [Qx])).mono_left nhdsWithin_le_nhds
 apply tendsto_nhds_unique_of_eventuallyEq ((openly T S Ω x w V ht).tendsto.comp hw) ((grounded Y Ow x _ _ L H').tendsto.comp hw)
 filter_upwards [march x,hw.eventually ((PEye b L).mem_nhds H')] with t ⟨s,z,v⟩ r; exact (T.sing S Ω _ w s V z v).trans (q _ s z v r)
#print axioms soliloque
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
