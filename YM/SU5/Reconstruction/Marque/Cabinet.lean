import YM.SU5.Reconstruction.Marque.Hall
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric Bornology BridgeClub Picket Anvil ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical Pointwise
variable {H:Hilbert} {S : OS.Semigroup H clock} (G: Gallery H S)
local notation "U"=> Picket.trans S
local notation "τ"=> parcelUp S
local notation "C"=> G.footprint
local notation "K"=> G.hue
local notation "M"=> G.lobby
variable (Ω:H)(j:Axis) (p:j≠clock)
local notation "W"=> Wedge clock j
local notation "D"=> stroll clock j p
variable (X:Chair G.lobby Ω j)
local notation "Z"=> X.boost
-- vac-only obligations
namespace Gallery
noncomputable def sprites (d:ℝ)(V:Set E4):Set H.Op:={x|∃ (i:G.Row)(y:E4)(A:H.Op), y∈ V∧ A∈ K i∧ C i ⊆ ball 0 d ∧ x= τ y A}
structure Fragment : Prop where
  stamp (e d:ℝ)(p:0<e)(t:0<d)(i:G.Row)(A:H.Op)(g:A∈K i): VacDues (G.sprites d (thickening e (C i))) Ω (A Ω)
structure Tilts (s:ℝ) : Prop where
  cap (e:ℝ)(p0:0<e):∃ d>0,∀ (i:G.Row)(A:H.Op),A∈K i→ C i⊆ball 0 d→ VacDues (G.tiles (ball 0 e)) Ω ((Z s) (A Ω))
-- seats already know motion at proper wedges/clock
structure Authenticates : Prop where
  normbase (x:E4): mover S x Ω = Ω
  vac (t:ℝ): Z t Ω=Ω
  motion (t:ℝ)(x:E4):Across (Z t) (U x) (U (D t x)) -- CONT normalization exact
  wrought (t:ℝ)(s:E4):Promotes (Z t) (M (strace s W)) (M (strace (D t s) W))
variable {G Ω j}
variable {A B:H.Op} {p} {X}
variable (b: Authenticates G Ω j p X)
include b
-- cost away at any placement.single-vac distinction
lemma separable (q:E4)(u:A∈ M (strace q W))(v:B∈M (strace q W))(h:A Ω=B Ω): A=B:= by
 let T:=τ (-q)
 have I(f:H.Op)(h:f∈ M (strace q W)) : T f∈ M W:= by
    have hv:=G.traceAppointment (strace q W) (-q) f h _ (mover_parcel S (-q) f); simpa only [strace_add, neg_add_cancel,strace_zero] using hv
 have e:(T A-T B:H.Op) Ω=0:= by
    rw [sub_apply]; apply sub_eq_zero.mpr; unfold T; nth_rw 1 2 [← b.normbase (-q)]; -- replaces all? use exact
    rw [mover_parcel,mover_parcel,h]
 have he:= sub_eq_zero.mp (X.crew.cheap (sub_mem (I A u) (I B v)) e)
 exact (Across.inv (mover_parcel S (-q) _)).unique ((by
    change Across _ (T A) B; rw[he]; exact (mover_parcel S (-q) B).inv)) -- tune he subst
omit b
lemma sprite_star (d:ℝ)(Y:Set E4)(A:H.Op)(p:A∈ G.sprites d Y): star A∈ G.sprites d Y:=by
 obtain ⟨t,v,A,k,y,b,rfl⟩:=p; exact ⟨t,v,star A,k,G.shades _ _ y,b,parcel_star ..⟩
lemma base {i:G.Row} (p:A∈ K i) : A∈ M (C i):= by simpa using G.typeA p 0
include b
variable (p' : Fragment G Ω)
include p' in
lemma payFragment (e d:ℝ)(s:0<e)(t:0<d)(i:G.Row)(z:A∈ K i): A∈ Auditorium (G.sprites d (thickening e (C i))):= by
 let V:= thickening (d+e) (C i); let F:=G.sprites d (thickening e (C i))
 have hv:F⊆ (M V:Set H.Op):=by
    rintro _ ⟨j,y,A,k,h,z,rfl⟩; exact G.mono ((Set.image_mono z).trans (withTrace (C i) y k)) (G.typeA h y)
 obtain ⟨q,h⟩:= enter clock j p (G.close_footprint i |>.isBounded.thickening (δ:=d+e)) -- tune
 replace h : V⊆ strace q W:=h; have hy:(G.sprites d (thickening e (C i))) ⊆ (M (strace q W):Set H.Op):=hv.trans (G.mono h)
 obtain ⟨x,u,v,k⟩:=settled (Y:=Auditorium F) (p'.stamp e d s t i A z) (fun _ u=> audition F u) hy
 rw [← separable b q v (G.mono ((self_subset_thickening (by positivity) (C i)).trans h) (base z)) k]; exact u
lemma purchase {s:ℝ}(g:Tilts G Ω j X s)(e:ℝ)(he:0<e):∃ d>0,∀ (i:G.Row)(A:H.Op),A∈K i → C i⊆ ball 0 d → Fleet.Form (X.convex s) A∈ M (ball 0 e):= by
 obtain ⟨d,v,z⟩:= g.cap e he; use d,v; intro i A h k
 let T:=D s; let R:= T.symm '' closedBall 0 e; let V:= closedBall (0:E4) d∪ R
 obtain ⟨q,hq⟩:=enter clock j p (V:=V) (((isCompact_closedBall ..).union ((isCompact_closedBall ..).image T.symm.continuous)).isBounded)
 have x: A∈ M (strace q W):= G.mono (k.trans (ball_subset_closedBall.trans (subset_union_left.trans hq))) (base h)
 let B:= Fleet.Form (X.convex s) A; have hx:=Fleet.arr (X.convex s) A; have hp:B∈ M (strace (D s q) W):= b.wrought s q A x _ hx
 have hv: G.tiles (ball 0 e) ⊆ (M (strace (D s q) W):Set H.Op):= by
    have h0:ball (0:E4) e ⊆ strace (T q) W:= by
       unfold T; rw [← passAll clock j p s V q]; intro x h; exact ⟨T.symm x,hq (Or.inr (show T.symm x∈R from ⟨x,ball_subset_closedBall h,rfl⟩)), T.apply_symm_apply _⟩
    exact fun y w=> G.mono h0 (audition _ w)
 obtain ⟨y,v',k',t⟩:=settled (z i A h k) (Y:=M (ball 0 e)) (fun y h=> audition _ h) hv
 have hb: y Ω=B Ω:= by rw [t,← hx, b.vac] -- tuning
 change B∈_; rw [← separable b (T q) k' hp hb]; exact v'
end Gallery
end YM.Marque.Flow
