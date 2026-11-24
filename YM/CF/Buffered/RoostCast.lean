import YM.CF.Buffered.Facades
/-! # Support of water cells/Cue, Pair and target tiles at micro period -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {m p v w l B n:Side}

namespace Planck
variable (G:Planck n l p)(r:Rail (Uniform p))
lemma zone_add (x y:Cover) : G.zone r (x+y)=G.zone r x+wrap n y:=by unfold zone; rw [← add_assoc,map_add]
lemma back_inner {t :Rail (Uniform p)}(x:Post l)(y:Roost l ∅)(p:∀ i,0<x.val i)(eq:G.zone r x.val= G.zone t y.val): r=t:=by
 have he : G.slots (r,x)= G.slots (Roost.slide t y):= eq.trans (G.zone_slide t y).symm
 have he':= G.slots.injective he
 have hx:x=y.wallet:= congrArg Prod.snd he'; have hy:r=t+corner (Uniform _) y.plusWall:=congrArg Prod.fst he'; rw [show y.plusWall=∅ from ?_,corner_empty,add_zero] at hy; · exact hy
 refine eq_empty_iff_forall_notMem.mpr fun i w=> ?_; specialize p i; rw [hx,show y.wallet.val i=0 from if_pos (mem_filter.mp w).2] at p; omega

lemma tag_edge {x y:Roost l ∅}{i:Axis}(w:l.val+1<n.val)(e:G.zone r x.val+step i= G.zone r y.val) : ∃ z:Roost l {i}, z.val=x.val:=by
 have he := congr_fun e i
 rw [Pi.add_apply,step_apply,if_pos rfl, zone_one,zone_one,Int.cast_add,Int.cast_add,add_assoc] at he
 have hp:(x.val i:Per n)+1=(y.val i:Per n):=add_left_cancel he
 have hu:x.val i+1=y.val i:= spill_same (n:=n) _ _ (by have u:=x.nonneg i; omega) (y.nonneg i) (by have u:=x.maxval i; omega) (by have u:=y.maxval i; omega) (by simpa using hp)
 refine ⟨⟨x.val,fun j=> ⟨x.nonneg j, ?_⟩⟩,rfl⟩; unfold topwall; split
 next h=> replace h:= mem_singleton.mp h; subst j; have w₁:= y.maxval i; omega
 exact x.maxval j
end Planck
namespace Ordered
variable (K:Ordered m v p) (r:Rail (Uniform p))
abbrev Tor (w:Side) := Roost w ∅
lemma odd_open (x: Tor (GridN v))(i:Axis)(h: OddAxis m (K.pebbles.zone r x.val i)) : 1≤ x.val i ∧ x.val i< (GridN v).val:=by
 change (assembly (More m)).residue _ _=1 at h
 have he:(assembly (More m)).residue (K.pebbles.zone r x.val) i=1:=h -- defeq projection
 rw [Planck.zone, Ratio.residue_wrap, wrap_here] at he; rw [show (K.pebbles.sail r+x.val) i=(GridN v).val*(r i).val+x.val i from rfl] at he
 change (((GridN v).val*(↑(r i).val:ℤ)+x.val i:ℤ):ZMod 2)=1 at he
 have ht : (GridN v).val=(More v).val*2:=rfl
 have hv:= x.nonneg i; have hu:= x.maxval i; have hz: (↑(GridN v).val:ZMod 2)=0:=by rw [ht]; push_cast; rw [show (2:ZMod 2)=0 by decide,mul_zero]
 simp only [Int.cast_add,Int.cast_mul, Int.cast_natCast] at he; rw [hz, zero_mul,zero_add] at he
 by_contra! hy; by_cases p:x.val i=0; · simp [p] at he
 rw [show x.val i=(GridN v).val by omega, Int.cast_natCast,hz] at he; exact zero_ne_one he
lemma in_room (j :Tor (GridN v)) (x:Site (Domain m B))(p:x∈room m B (K.pebbles.zone r j.val)): ∃ y:Tor (Domain v B), (K.sugar B).zone r y.val=x :=by
 let a:= K.pebbles.zone r j.val; let z:= lift (x-address m B a); refine ⟨⟨B.val • j.val+z,fun i=>?_⟩, ?_⟩
 · have he:= (room_mem ..).mp p i; change roomX m B (a i) (x i) at he; rw [roomX, ←(show address m B a i=high m B (a i) from high_here ..)] at he
   change (z i).natAbs ≤ _ at he; have ht:=j.nonneg i; have hy:= j.maxval i; have hp:0<B.val:=B.property
   unfold broadface at he; rw [Pi.add_apply, Pi.smul_apply,nsmul_eq_mul, topwall,if_neg (notMem_empty _),gauge_vs, Nat.cast_mul] -- tune alters More
   split at he
   next h=> obtain ⟨t₁,t₂⟩:= K.odd_open r j i h; have hz: -(B.val:ℤ)≤ z i:=by omega
            have hy:z i ≤ B.val:=by omega
            constructor <;> nlinarith
   have hh:z i=0:=by omega
   rw [hh]; constructor <;> nlinarith
 change (K.sugar _).zone _ _=_; rw [Planck.zone_add, ← placeAddress (K:=K), show wrap (Domain m B) z=x-address m B a from wrap_lift .., add_sub_cancel] -- tune
lemma in_bay (j :Tor (GridN v))(x:Index m)(p:x∈faces m (K.pebbles.zone r j.val)): ∃ y: Tor (GridN v), K.pebbles.zone r y.val=x:=by
 let a:= K.pebbles.zone r j.val; let z:= lift (x-a); refine ⟨⟨j.val+z,fun i=> ?_⟩, ?_⟩
 · have he := ((mem_filter.mp p).2 i); have hx:= j.nonneg i; have h':=j.maxval i
   change _ ∨ (_∧OddAxis m (a i)∧_) at he; rw [topwall,if_neg (notMem_empty _),Pi.add_apply]; rcases he with v|⟨_,g,k⟩
   · rw [show z i=0 from ?_]; exact ⟨by omega, by omega⟩; change ZMod.valMinAbs (x i-a i)=_; simp only [show x i=a i from v,sub_self,ZMod.valMinAbs_zero]
   · rw [d_sym] at k; change (z i).natAbs ≤ 1 at k; have h':=K.odd_open r j i g; omega
 change K.pebbles.zone r _=_; rw [Planck.zone_add, show wrap (GridN m) z=x-a from wrap_lift .., add_sub_cancel] -- tune
lemma meet {x y:Pack m B}(h: reel r (K.fromCube x)=reel r (K.fromCube y)) (i:Tor (GridN v)) :
 Agrees (room m B (K.pebbles.zone r i.val)) x.1 y.1 ∧ Phase.Sample.AgreeF (faces m (K.pebbles.zone r i.val)) x.2 y.2:= by
 constructor
 · rintro ⟨u,a⟩ ht₁ ht₂; obtain ⟨l,f⟩:=K.in_room r i u ht₁; obtain ⟨w,g⟩:= K.in_room r i (u+step a) ht₂
   have hp:(Domain v B).val+1<(Domain m B).val:=by rw [(K.sugar B).ratio]; have hv:= enough v B; have h: 0<B.val:= B.property; have he:2≤(Uniform _ 0).val:= landing_ge K.onGrid 0; change 2≤ p.val at he; nlinarith -- tune
   obtain ⟨z,he⟩ := (K.sugar B).tag_edge r hp (show (K.sugar B).zone r l.val+step a=(K.sugar B).zone r w.val by rw [f,g])
   rw [←f,←he,←Ordered.butter (K:=K), h, butter]
 · intro j p; obtain ⟨x,f⟩:= in_bay K r i j p; rw [←f, ← cand (K:=K), h, cand]
lemma same_water (i:Tor (GridN v)){x y:Pack m B}(p: reel r (K.fromCube x)=reel r (K.fromCube y)) : water m B x.1 (K.pebbles.zone r i.val) x.2=water m B y.1 (K.pebbles.zone r i.val) y.2 := water_limit _ _ _ x.2 y.2 (K.meet r p i).2 (K.meet r p i).1

def canvas (K:Ordered m v p)(r:Rail (Uniform p))(v: Post (CSide v B))(x:Pack m B):= grain m B x.1 (slot m x.2) (stick 0) ((K.spirit B).zone r v.val)
def upstairs (v:Side)(B:Side)(x:Post (CSide v B)):Post (Domain v B):=⟨(2:ℕ) • x.val+1,fun i=>by
 have he:=x.nonneg i; have ht:= x.below i (mem_univ _); simp only [Pi.add_apply,Pi.smul_apply,natM, Pi.one_apply,wall_mem i (mem_univ _),Nat.cast_mul]; rw [two_smul]; omega⟩
lemma up_strict (i: Post (CSide v B)) (j:Axis) : 0 < (upstairs v B i).val j:=by unfold upstairs; simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply]; have ht:= i.nonneg j; rw [two_smul]; omega
lemma up_sends (i: Post (CSide v B)) : node ((K.spirit B).zone r i.val)=(K.sugar B).zone r (upstairs v B i).val:= K.placeNode B r i.val -- tune K order
lemma full (i: Post (CSide v B)) : ∃ j:Tor (GridN v), node ((K.spirit B).zone r i.val) ∈ room m B (K.pebbles.zone r j.val):= by
 obtain ⟨v',g,_⟩:= full_r m B (node ((K.spirit B).zone r i.val)); obtain ⟨⟨t,a⟩,eq⟩:= K.pebbles.slots.surjective v'; change K.pebbles.zone t a.val = v' at eq; subst v'; rw [up_sends (K:=K)] at g
 obtain ⟨b,e⟩:= K.in_room t (ofpost ∅ a) _ g; obtain rfl:= (K.sugar B).back_inner r _ b (up_strict i) e.symm; rw [up_sends (K:=K)]; exact ⟨ofpost ∅ a,g⟩
lemma canvas_eq (i:Post (CSide v B))(x y:Pack m B)(p: reel r (K.fromCube x)=reel r (K.fromCube y)): K.canvas r i x=K.canvas r i y:= by
 obtain ⟨j,t⟩:= K.full r i; apply paint_local _ t _ (K.meet r p j).1; intro b u; exact (K.meet r p j).2 _ (mem_filter.mpr ⟨mem_univ _,room_active t u⟩)
lemma up_turn (i: Post (CSide v B))(T: Finset Axis): flipC (Domain v B) T (upstairs v B i).val=(upstairs v B (shades T i)).val:=by
 funext j; rw [flip_iff]; unfold upstairs; simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply]; split
 next h=> rw [shades_eq _ h,wall_mem j (mem_univ _),natM]; simp only [two_smul]; omega
 next h=> rw [shades_other _ h]
lemma color_turned (t:Rail (Uniform p))(T:Finset Axis)(i: Post (CSide v B))(x:Pack m B): canvas K r i (onPack B (K.ferry r t T) x)= canvas K t (shades T i) x:=by
 change paintV m B (through B _ x.1) ((K.ferry r t T).riseF (slot m x.2)) _ _= _; rw [fees_eq]; unfold canvas grain; dsimp only [comp_apply]; rw [up_sends (K:=K),up_sends (K:=K),ferry_read (K:=K),up_turn]
end Ordered
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ordered.canvas_eq
