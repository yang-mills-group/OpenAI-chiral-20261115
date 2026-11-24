import YM.CF.Vp929.Law.Border
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset
open scoped Classical
namespace Wall
variable (L : Set ℤ) {x y z t:Wall}

structure Split(x y:Wall):Prop where
 on:x ≤ y
 big:y.win → x.win
 low:x.a∈ L
 high:x.b∈ L
 apart (a:ℤ)(v:a∈L): a ≤ x.a ∨ x.b ≤ a
lemma generate (v:y.a ∈ L)(p:y.b∈L)(h:t.Tiny)(q:t≤y)(w:y.win→ t.win):∃ x:Wall, Split L x y ∧ t ≤ x:=by
 by_cases g:y.win; swap; · refine ⟨y,⟨le_rfl,id,v,p,fun i _=>?_⟩,q⟩; unfold Wall.win at g; omega
 let d := (w g); change y.a < y.b at g; have he:t.b=t.a+1:=by change t.a<t.b at d; unfold Tiny at h; omega
 let F:= (Finset.Icc y.a t.a).filter (· ∈ L); let G:= (Finset.Icc t.b y.b).filter (·∈L)
 have hF:y.a∈ F:= Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,(full q).1⟩,v⟩; have hG:y.b∈ G:= Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(full q).2,le_rfl⟩,p⟩
 let a:=F.max' ⟨_,hF⟩; let b:=G.min' ⟨_,hG⟩; obtain ⟨f0,f⟩:= Finset.mem_filter.mp (show a∈F from max'_mem ..); obtain ⟨g0,g⟩:= mem_filter.mp (show b∈G from min'_mem ..); rw [Finset.mem_Icc] at f0 g0; let ht:a < b:=by omega
 refine ⟨⟨a,b,ht.le⟩,⟨⟨f0.1,g0.2⟩,fun _=>ht,f,g,?_⟩,⟨f0.2,g0.1⟩⟩
 intro i v; change i ≤ a ∨ b ≤ i; by_contra! H
 by_cases k : i ≤ t.a
 · exact H.1.not_ge (Finset.le_max' F _ (mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_trans f0.1 H.1.le,k⟩,v⟩))
 exact H.2.not_ge (Finset.min'_le G _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,le_trans H.2.le g0.2⟩,v⟩))
variable {L}
lemma Split.slice (s:Split L x y)(v:z ≤ t)(e:t.a∈ L)(h:t.b∈ L)(w:z.cabin x) : x ≤ t:=by
 by_cases g:x.win; swap; · exact (stay g w.1) ▸ v
 obtain ⟨h0,h1⟩:=full v; obtain ⟨t0,t1⟩:=w.2 g; obtain l:=s.apart _ e; obtain r:=s.apart _ h; change x.a < x.b at g; exact ⟨by omega,by omega⟩
lemma Split.selfUnique (e:Split L x y)(s:Split L t y)(p:z ≤ t)(v:z.cabin x) : x=t:=by
 have h:= e.slice p s.low s.high v
 by_cases g:y.win; swap; · rw [stay g e.on, stay g s.on]
 have t':= e.big g; exact le_antisymm h (s.slice v.1 e.low e.high (by
    have he:=full h; refine ⟨p,fun w=>?_⟩; have h:= v.2 t'; omega))
end Wall
namespace Rooms
variable {L : Set Rooms} {r:Rooms→ℕ} {x y z w t:Rooms}{a:ℤ}
def Cuts (L:Set Rooms)(x:Rooms)(i:Axis) : Set ℤ:= {t | ∃ y∈L, y.meets x ∧ (y i).tips t}
lemma cutters {i}: x∈L→(x i).tips a→a∈Cuts L x i:= fun p t=>⟨x,p,touch (le_refl x) (le_refl x),t⟩
def diced(L:Set Rooms)(x y:Rooms):Prop:= ∀ i,Wall.Split (Cuts L y i) (x i) (y i)
def keeps(r:Rooms→ℕ)(L:Set Rooms)(x y:Rooms):Prop:= ∀ z∈L,inside x z→Plane y z→ r y ≤ r z

def Spread (r:Rooms→ℕ)(L:Set Rooms): Set Rooms:= {x|∃ y∈L, diced L x y∧ keeps r L x y}
lemma diced_le (sx:diced L x y): x ≤ y:= fun i=>(sx i).on
lemma diced_plane (sx:diced L x y) : x.Plane y := plane_of_doors (diced_le sx) (Finset.Subset.antisymm (dim_le (diced_le sx)) (fun i p=> intro_door.2 ((sx _).big (intro_door.1 p))))
lemma dice_own (sx:diced L x y)(v:z≤t)(e:t∈L)(hx:z.inside x): x ≤ t:=by
 let h:= touch v ((place hx).trans (diced_le sx)); intro i; exact Wall.Split.slice (sx i) (v i) ⟨t,e,h,Or.inl rfl⟩ ⟨t,e,h,Or.inr rfl⟩ (hx i)
lemma coverage (r:Rooms→ℕ)(s:t.Tiny)(p:t ≤ x)(v:x∈L):∃ y∈ Spread r L,t ≤ y∧ y ≤ x:=by
 classical
 obtain ⟨z,w,f,F,g⟩:=pad x s p
 have h:∃ i:ℕ,∃ y∈L,z ≤ y ∧ z.Plane y ∧ r y=i:=⟨_,x,v,F,g,rfl⟩
 obtain ⟨y,e,e0,qY,rY⟩:= Nat.find_spec h
 choose A H HG using fun i:Axis=> Wall.generate (L:=Cuts L y i) (cutters e (Or.inl rfl)) (cutters e (Or.inr rfl)) (w i) (e0 i) ((qY.win i).mpr); let k:Rooms:=A; have hx:diced L k y:= H; have hk:=diced_plane hx; have ht:z.Plane k:=qY.trans hk.symm; have hz:z ≤ k:= HG
 have he:= inside_of_plane hz ht
 refine ⟨k, ⟨y,e,hx,?_⟩,f.trans hz, dice_own hx F v he⟩; intro w e v p; rw [rY]; exact Nat.find_min' h ⟨w,e,hz.trans (place v),qY.trans p,rfl⟩
variable (hFeet:∀ x ∈ L,∀ y∈L,y.meets x→ r y=r x→ y=x) {N:ℕ} (h:∀ z∈L,dim z=N)
include hFeet h
lemma separate (p:x∈ Spread r L)(v:y∈Spread r L)(k:z.inside x)(d:z≤y) : x=y:=by
 obtain ⟨a,b,u,k0⟩:=p; obtain ⟨A,e',W,hW⟩:=v; have hc:x≤A:=dice_own u (d.trans (diced_le W)) e' k
 have ha:=diced_plane u; have hz:=diced_plane W
 have hd:x.Plane A:=plane_of_dim hc (ha.dim.trans ((h _ b).trans (h _ e').symm)); have hY:x.Plane y:= hd.trans hz.symm

 have ov(i):∃ γ:Wall,γ ≤ x i ∧ γ ≤ y i ∧ γ.cabin (y i):=by
    let p:= k i; let q:= d i; have he:= Wall.full q; have h:=Wall.full p.1
    by_cases f:(y i).win; swap; · exact ⟨z i,p.1,q,⟨q,fun v=>(f v).elim⟩⟩
    have hf:= p.2 ((hY.win i).2 f); let r:= max (x i).a (y i).a; let s:=min (x i).b (y i).b; have v:r<s:=by change (y i).a < (y i).b at f; unfold r s; have hh:=(hY.win i).2 f; change _ < _ at hh; omega
    exact ⟨⟨r,s,v.le⟩,⟨le_max_left .., min_le_left ..⟩,⟨le_max_right ..,min_le_right ..⟩,Wall.cabin_win ⟨le_max_right ..,min_le_right ..⟩ v⟩
 choose g Q S H using ov; let t:Rooms:=g; let q:y ≤ a:= dice_own W ((show t ≤ x from Q).trans (diced_le u)) b H
 have hg:A=a:= hFeet _ b _ e' (touch hc (diced_le u)) (le_antisymm (hW a b (inside_of_plane q (hY.symm.trans ha)) (hd.symm.trans ha)) (k0 A e' (inside_of_plane hc hd) (ha.symm.trans hd))); subst A
 exact funext fun i=> Wall.Split.selfUnique (u i) (W i) (d i) (k i)
omit hFeet
lemma rank (p:x∈ Spread r L) : dim x=N:=by obtain ⟨y,p,e,v⟩:=p; exact (diced_plane e).dim.trans (h y p)
end Rooms
end YM.CF.VolumeCape
