import YM.CF.BPress.Locale.Cubus
/-! Deep components budget per B-map. Work for every arc, but only request N interpolation when used. Width r where r ≤ (w=⌊D_P/16⌋)-1. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s :Side}{b:BandWidth}(X:Bands s b)
def umbra (b:BandWidth):= b.marked.val /16
def Deep (i:X.Index)(u:ℕ)(x:Site s):= ∃ k:ℕ, u≤k ∧ k+u ≤ b.marked.val ∧ x 0=(X.mark i).rise k
lemma surface (i:X.Index)(x:Site s) (p:x∈X.band i): Deep X i 0 x:= by obtain ⟨k,v,h⟩:=(X.mark i).internal x|>.mp p; exact ⟨k,Nat.zero_le _,v,h⟩
variable {X}
lemma deep_m {u t:ℕ}{i:X.Index}{x:Site s}(p:Deep X i u x)(h:t≤u): Deep X i t x:=by obtain ⟨k,v,p,x⟩:=p; exact ⟨k,h.trans v,(Nat.add_le_add_left h k).trans p,x⟩
lemma own_band {i:X.Index}{u:ℕ}{x:Site s}(p:Deep X i u x):x ∈ X.band i:=by obtain ⟨k,v,q,h⟩:=p; exact (X.mark i).internal x |>.mpr ⟨k,(Nat.le_add_right ..|>.trans q),h⟩
lemma near_in {i:X.Index}{u t:ℕ}{x y:Site s}(p:Deep X i u x)(f:delta1 s (x 0) (y 0)≤ t)(v:t≤u): Deep X i (u-t) y:=by
 obtain ⟨n,hn,f⟩:= step_exists (y 0) (x 0) _ ((d_sym ..).le.trans f); obtain ⟨k,h,l,g⟩:=p; let a:ℤ:=k+n; have hp:0≤a:=by unfold a; omega
 refine ⟨a.toNat,by omega,by omega,?_⟩; rw [f,g]; unfold Tunnel.rise; rw [← Int.cast_natCast (R:=Per s) a.toNat,Int.toNat_of_nonneg hp]; unfold a; push_cast; abel
lemma off_gap {i:X.Index}{x:Site s}{u:ℕ}(p:0<u)(v:Deep X i u x) (j:X.Index): x∉ X.gap j:=by
 intro t; have ht:= (X.at_overlap t).mp (own_band v); obtain ⟨k,a,q,g⟩:=v; rcases ht with ⟨hh,g'⟩|⟨hh,g'⟩; · have e:x 0= (X.mark i).rise b.marked.val:=g'.trans (hh ▸ ((X.mark_last i).symm)); have he:= (X.mark i).rise_inj (by change k ≤ b.marked.val+1; omega) (Nat.le_succ b.marked.val) (g.symm.trans e); omega
 have e:x 0= (X.mark i).rise 0:=g'.trans (hh.symm ▸ ((X.mark i).rise_zero).symm); have he:= (X.mark i).rise_inj (by change k ≤ b.marked.val+1; omega) (Nat.zero_le _) (g.symm.trans e); omega
lemma off_far {i:X.Index}{u r:ℕ}{x:Site s}(p:r<u)(h:Deep X i u x): ¬ NearBlock X r x:=by
 rintro ⟨j,t,ht,v⟩; let y:= event t (Fin.tail x); exact off_gap (Nat.sub_pos_of_lt p) (near_in (y:=y) h v p.le) j ((time_Zone X j y).1 ht)

variable (X)
local notation "Ψ" => Grid.field 4 s
variable (S:Support s)
def dark (i:X.Index) := S.filter (Deep X i (umbra b))
def family (i:X.Index)(x:Site s) := (dark X S i).filter (Origin (Grid.field 4 s) (dark X S i) x)
def peek := (Deep X · (2*umbra b) ·)
def richT (i:X.Index) := S.filter (peek X i)
def gaze : Finset (X.Index × Support s):= univ.biUnion fun i=>(richT X S i).image fun x=>(i,family X S i x)
variable {X S} {i : X.Index} {x y: Site s}
lemma family_dark : family X S i x⊆ dark X S i:=filter_subset ..
lemma family_ne (h:x∈dark X S i): x∈family X S i x:= mem_filter.mpr ⟨h,.refl⟩
lemma family_base (h:x∈dark X S i)(v:y∈family X S i x): family X S i x=family X S i y:=by
 have hx:= (mem_filter.mp v).2; ext1 j; simp only [family,mem_filter]; exact and_congr_right fun u=> ⟨fun g=> (orig_flip hx).trans g,fun t=> hx.trans t⟩
lemma family_g (h:x∈dark X S i): Grove Ψ (family X S i x):=by
 let A:= family X S i x; let V:= dark X S i; let F:= Grid.field 4 s; have he (y:Site s) (p:Origin F V x y): Origin F A x y:= by
   induction p with| refl=>exact .refl| @tail z y p e ih=>exact .tail ih ⟨mem_filter.mpr ⟨e.1,p⟩,mem_filter.mpr ⟨e.2.1,p.tail e⟩,e.2.2⟩
 exact trunk (B:=F) (family_ne h) (fun i t=> he i ((mem_filter.mp t).2)) -- tune
-- exit lower. include even if jut every component. use induction path WHEN from qualifying vertex and length payment via diameter contradict first exit.
lemma stem_dep {r:ℕ}(p:Grove Ψ S)(u:r<umbra b)(x':meets X r S)(q:x∈richT X S i): umbra b ≤ (family X S i x).card:=by
 let F:= Grid.field 4 s; let U:= dark X S i; let V:= family X S i x; obtain ⟨h,s'⟩:=mem_filter.mp q; have hz:x∈dark X S i:= mem_filter.mpr ⟨h,deep_m s' (Nat.le_mul_of_pos_left (umbra b) (by norm_num))⟩; let f:=family_g hz; obtain ⟨w,v,h'⟩:=x'; by_contra! e; have he(y:Site s)(t: Origin F S x y): y∈V:=by
    induction t with
    | refl=> exact family_ne hz
    | @tail a y t e' ih=>
     have hV:(F.span x y)≤umbra b:= (F.tri x a y).trans (le_trans (add_le_add (f.lim x (family_ne hz) a ih |>.le) e'.2.2) (by omega)) -- tune no +? need e restrictive
     have Hy: Deep X i (umbra b) y:= deep_m (near_in (x:=x) (y:=y) s' ((Grid.delta_at x y 0).trans hV) (show umbra b≤2*umbra b by omega)) (by omega) -- tune
     have hm:y∈U:=mem_filter.mpr ⟨e'.2.1,Hy⟩; exact mem_filter.mpr ⟨hm, (mem_filter.mp ih|>.2).tail ⟨(mem_filter.mp ih).1,hm,e'.2.2⟩⟩
 exact off_far u ((mem_filter.mp (family_dark (he w (rooted p x h w v)))).2) h'
-- purchase lower all peek in union
variable (X S)
@[simp] lemma gaze_mem (i:X.Index)(v:Support s): (i,v)∈ gaze X S ↔ ∃ x∈richT X S i,family X S i x=v:=by unfold gaze; simp [and_left_comm]
def quayDeep (p:X.Index × Support s): Prop:= p∈gaze X S
lemma gaze_cover (u:X.Index × Support s)(h:u∈gaze X S): u.2⊆ S∧ Grove Ψ u.2 ∧ ∀ i∈u.2, Deep X u.1 (umbra b) i:=by
 rcases u with ⟨i,v⟩; obtain ⟨x,vx,rfl⟩:= (gaze_mem ..).mp h; exact ⟨family_dark.trans (filter_subset ..), family_g (mem_filter.mpr ⟨(mem_filter.mp vx).1,deep_m ((mem_filter.mp vx).2) (by omega)⟩),fun _ h=>(mem_filter.mp (family_dark h)).2⟩ -- tune dotted p
lemma gaze_disjoint : ((gaze X S:Set (X.Index × Support s))).PairwiseDisjoint Prod.snd:=by
 rintro ⟨i,v⟩ hi ⟨j,w⟩ hj p; obtain ⟨x,vx,rfl⟩:= (gaze_mem ..).mp hi; obtain ⟨y,vy,rfl⟩:=(gaze_mem ..).mp hj; apply disjoint_left.mpr; intro a s t; by_cases q:i=j
 · subst j; apply p; apply congrArg (fun v=> (i,v)); change a∈ family X S i x at s; change a∈ family X S i y at t; exact (family_base (mem_filter.mpr ⟨ (mem_filter.mp vx).1, deep_m ((mem_filter.mp vx).2) (by omega)⟩) s).trans ((family_base (mem_filter.mpr ⟨(mem_filter.mp vy).1,deep_m ((mem_filter.mp vy).2) (by omega)⟩) t).symm)
 exact disjoint_left.mp (X.band_disjoint q) (own_band (gaze_cover X S _ hi|>.2.2 a s)) (own_band (gaze_cover X S _ hj|>.2.2 a t)) -- tune mem_coe
end YM.CF.BPress.Locale
