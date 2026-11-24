import YM.CF.BPress.Wealth.Core
/-!
Canonical perturbation for W variables. Copy collars in eventual geometric region. Defined on all sites, even those not paying heavy charges or in gap; uses n.round to nearest face in collar, value zero elsewhere. Ignores D-face fluctuations. Is linear on formal variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel
open scoped Topology BigOperators Classical Matrix
variable {s:Side} {b:BandWidth}(X : Bands s b)
open SU
-- use fixed radius of copy = Bpress lips (marked/4), large enough for all heavy. not same as ω0 collar.
def cloak (b:BandWidth):=b.marked.val/4
lemma cloak_lt (b : BandWidth): 2*cloak b<b.marked.val:=by have h:0<b.marked.val:=b.marked.property; unfold cloak; omega
lemma lips_c (i:X.Index): (X.mark i).lips=cloak b:=rfl
abbrev feast (i:X.Index):= Fest X i (cloak b) (cloak_lt b)
def pin (i:X.Index)(t:Per s) : ℕ:= (t-(feast X i).o).val
def station (t:Per s)(p:X.Index) := ZoneNear X p (cloak b) t
def slot (t:Per s) : Option X.Index:= if h:∃ p, station X t p then some h.choose else none
def tempo (p:X.Index)(t:Per s):= min ((pin X p t)-cloak b) b.D -- depth in positive orientation if D->N
def magtime (p:X.Index)(t:Per s):= if p∈X.dc then tempo X p t else b.D - tempo X p t
lemma magtime_le (p:X.Index)(t:Per s): magtime X p t ≤ b.D:=by unfold magtime; split; exact min_le_right ..; exact Nat.sub_le ..
lemma station_g (t:Per s)(p:X.Index): station X t p ↔ ∃ k≤ hall (b:=b) (cloak b),t=(feast X p).rise k:=by
 let x:=event t (0:Tri s); exact ((zone_of_halo X p (cloak b) x).symm.trans (z_iff X p (cloak_lt _) x)).trans ((feast X p).internal x)
lemma station_pin (t:Per s)(p:X.Index)(w:station X t p): pin X p t ≤ (feast X p).n.val ∧ t=(feast X p).rise (pin X p t):=by obtain ⟨k,h,e⟩:=station_g X t p|>.1 w; rw [pin,e,(feast X p).rise_val (Nat.le_succ_of_le (show k≤ (feast X p).n.val from h))]; exact ⟨h,rfl⟩
lemma station_one {t:Per s}{i j:X.Index}(p: station X t i)(q: station X t j): i=j:=by
 let x:=event t (0:Tri s); apply Classical.byContradiction; intro v; exact disjoint_left.mp (pill X (cloak_lt b) v) ((zone_of_halo X i _ x).2 p) ((zone_of_halo X j _ x).2 q)
lemma slot_eq {p:X.Index}{t:Per s}(v: station X t p): slot X t=some p:=by unfold slot; rw [dif_pos ⟨p,v⟩]; exact congrArg _ (station_one X (Exists.choose_spec (show ∃ k, station X t k from ⟨p,v⟩)) v)

lemma feeD (i:X.Index){k:ℕ}(v:k≤b.D): tempo X i ((X.ditch i).rise k)=k:=by
 let M:= cloak b; let W:= feast X i; have ht:M≤ W.n.val+1:= by change M ≤ b.D+2*M+1; omega
 have he:W.rise (M+k)=(X.ditch i).rise k:= Eq.trans (case_ditch X i (cloak_lt b) (k:=M+k) (show M≤ M+k by omega)) (by change (X.ditch i).rise (M+k-M)=_; rw [Nat.add_sub_cancel_left]); unfold tempo pin; rw [←he,W.rise_val (by change M+k≤ b.D+2*M+1; omega)]; change min (M+k-M) b.D=k; omega -- tune shadow
lemma magGap (i:X.Index){k:ℕ}(v:k≤b.D): magtime X i (X.depth i k)=k:= by by_cases t:i∈X.dc; rw [depth,if_pos (X.dc_index ..|>.mp t),magtime,if_pos t,feeD X i v]; rw [depth,if_neg (fun p=> t ((X.dc_index ..).mpr p)),magtime,if_neg t,Tunnel.fall,X.ditch_n,feeD X i (Nat.sub_le ..),Nat.sub_sub_self v]
lemma preClock (i:X.Index){k:ℕ}(v:k ≤ cloak b) : let t:=(X.mark i).fall k; station X t i ∧ tempo X i t=0:=by
 intro t; let M:=cloak b; have e:(feast X i).rise (M-k)=(X.mark i).fall k:= Eq.trans (case_left X i (cloak_lt b) (Nat.sub_le M k)) (by rw [show cloak b-(M-k)=k from Nat.sub_sub_self v])
 unfold t; rw [←e]; have hu:M-k≤hall (b:=b) M:= by unfold hall; omega
 refine ⟨station_g ..|>.mpr ⟨M-k,hu,rfl⟩,?_⟩; unfold tempo pin; rw [(feast X i).rise_val (show M-k≤ (feast X i).n.val+1 from Nat.le_succ_of_le hu),Nat.sub_eq_zero_of_le (show M-k ≤ M from Nat.sub_le ..),Nat.zero_min]
lemma postClock (i:X.Index){k:ℕ}(v:k ≤ cloak b) : let t:=(X.mark (i+1)).rise k; station X t i ∧ tempo X i t=b.D:=by
 intro t; let M:=cloak b; have e:(feast X i).rise (M+b.D+k)=t:= Eq.trans (case_right X i (cloak_lt b) (Nat.le_add_right _ k)) (by rw [show _ - (cloak b+b.D)=k from Nat.add_sub_cancel_left ..]); -- tune
 rw [←e]; have hu : M+b.D+k≤ hall (b:=b) M:= by change k≤ M at v; unfold hall; omega
 refine ⟨station_g ..|>.mpr ⟨ M+b.D+k,hu,rfl⟩,?_⟩; unfold tempo pin; rw [(feast X i).rise_val (show M+b.D+k≤ (feast X i).n.val+1 from Nat.le_succ_of_le hu)]; change min (_ - M) _=_; omega
lemma magfront (i:X.Index){k:ℕ}(v:k ≤ cloak b): magtime X i ((X.mark i).fall k)= if i∈ X.dc then 0 else b.D:=by unfold magtime; rw [(preClock X i v).2,Nat.sub_zero]
lemma maglast (i:X.Index){k:ℕ}(v:k ≤ cloak b): magtime X i ((X.mark (i+1)).rise k)= if i∈ X.dc then b.D else 0:=by unfold magtime; rw [(postClock X i v).2,Nat.sub_self]

-- `pin` uses Option X ordinal (unique in Zones, even if r region price sometimes <). choose equivalent finite code by min.
def keyV (t:Per s)(j:FlatLink s) : Option X.Air:= (slot X t).bind fun p=> let k:= magtime X p t; if h: 0<k then some ((p,j.1),⟨k-1,(show k-1<b.D from (by have he : k≤ b.D:= magtime_le X p t; omega))⟩,j.2) else none
def edgeKey (j:Link s): Option X.Air:= Fin.cases none (fun i=> keyV X (j.1 0) (Fin.tail j.1,i)) j.2
lemma EdgeKey_H (t:Per s)(i:FlatLink s): edgeKey X (fl t i)=keyV X t i:=by simp [edgeKey,fl,event]
lemma EdgeKey_V (t:Per s)(i:Tri s): edgeKey X (vl t i)=none:=by simp [edgeKey,vl,event]
lemma key_spec (t:Per s)(i:FlatLink s)(p:X.Index)(b: station X t p) :
    (keyV X t i).isSome ↔ magtime X p t ≠0 := by
 rw [keyV,slot_eq X b]; dsimp; split; next h=> simp; omega
 next h=> simp; omega
lemma key_frame (t:Per s)(i:FlatLink s)(p:X.Index){k:Fin b.D} (g:station X t p)(v:k.val+1=magtime X p t) : keyV X t i=some ((p,i.1),k,i.2):=by
 rw [keyV,slot_eq X g]; dsimp; split; next h=> congr; omega
 next h=>omega
lemma key_depth (i:X.Air): edgeKey X (X.skylink i)=some i:=by rcases i with ⟨⟨p,x⟩,k,i⟩; rw [skylink,EdgeKey_H]; exact key_frame X _ _ _ (time_zero X p _ (depth_time X p k.isLt) (cloak b)) ((magGap X p k.isLt).symm)
lemma key_o (i:X.Index)(x:FlatLink s): edgeKey X (fl (X.depth i 0) x)=none:=by rw [EdgeKey_H,←Option.not_isSome_iff_eq_none,key_spec X _ x i (time_zero X i _ (depth_time X i (Nat.zero_le b.D)) (cloak b)),magGap X i (Nat.zero_le b.D)]; simp
lemma key_reads {t:Per s}{i:FlatLink s}{k:X.Air}{p:X.Index}(v:station X t p)(h:keyV X t i=some k): k.1=(p,i.1):=by
 rw [keyV,slot_eq X v] at h; dsimp at h; split at h; next p=> exact congrArg Prod.fst (Option.some.inj h|>.symm)
 next=>contradiction
lemma key_housed {p:X.Index} {i:Link s} (v:station X (i.1 0) p) {k:X.Air}(t:edgeKey X i=some k): k.1=(p,Fin.tail i.1):=by
 rcases link_cases i with ⟨j,u⟩|u; rw [u,EdgeKey_H] at t; rw [u]; simpa only [fl,event, Fin.tail_cons] using key_reads X v t; rw [u,EdgeKey_V] at t; contradiction

abbrev Bills (J:Type*) := X.Air → J
section
variable {J:Type*} [Zero J]
def raw (v:Bills X J) (i : Link s) := (edgeKey X i).elim 0 v
lemma pay_key (v:Bills X J){i:Link s}{k : X.Air}(h:edgeKey X i=some k): raw X v i=v k:=by simp [raw,h]
lemma none_key (v:Bills X J){i:Link s}(h:edgeKey X i=none): raw X v i=0:=by simp [raw,h]
lemma roll_gap (v:Bills X J)(i:X.Index)(k:ℕ)(q:k≤ b.D)(x:FlatLink s) : raw X v (fl (X.depth i k) x)=(if p: 0<k then v ((i,x.1), ⟨k-1,(by omega)⟩,x.2) else 0):=by
 split; next p=> refine pay_key X v ?_; rw [EdgeKey_H]; apply key_frame X _ _ _ (time_zero X i _ (depth_time X i q) _); rw [magGap X i q]; change k-1+1=k; omega
 next p=> rw [show k=0 by omega]; apply none_key X v (key_o ..)
end
variable {G : Gauge}
def canon : Bills X G.Color →ₗ[ℝ] Directions G s where
 toFun := raw X
 map_add' u v:=by funext i; dsimp; unfold raw; cases h:edgeKey X i<;> simp
 map_smul' c u:=by funext i; dsimp; unfold raw; cases h:edgeKey X i <;> simp
end YM.CF.BPress.Wealth
