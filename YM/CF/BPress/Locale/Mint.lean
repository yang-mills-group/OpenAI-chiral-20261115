import YM.CF.BPress.Locale.Atlas
/-! Connecting and pushing supports at PL radius. `lem:B-mapcard` base layer. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s : Side}{b:BandWidth}(X:Bands s b) (R:Hangar s)
lemma internal_halfway {d r t:ℕ}{x y:Space d s} (h:delta x y≤r+t) : ∃ z, delta x z≤r∧ delta z y≤t :=by
 induction t generalizing y with
 | zero=> rw [add_zero] at h; exact ⟨y,h,by simp⟩
 | succ k ih=>
   obtain ⟨z,t,v⟩:=decrease_bay x y h; obtain ⟨w,g,p⟩:=ih t; exact ⟨w,g,(delta_triangle w z y).trans (add_le_add p v)⟩
lemma two_sector {x y : Site s}(u:R.L.val ≤ b.full.val)(p:Grid.delta x y ≤ 2*R.L.val) : (shape X R).span (plan X R x) (plan X R y)≤2:=by
 rw [two_mul] at p; obtain ⟨z,v,t⟩:= internal_halfway p; exact ((shape X R).tri _ (plan X R z) _).trans (add_le_add (dispatch X R u v) (dispatch X R u t))
lemma two_sectorC {x y:X.Hcols}(p:(grass X).span x y≤ 2*R.L.val)(t:x.1=y.1) : (shape X R).span (own X R x) (own X R y)≤2:=by
 rw [two_mul] at p; obtain ⟨z,v,h⟩:= internal_halfway (x:=x.2) (y:=y.2) p; let i:X.Hcols:=(x.1,z); exact ((shape X R).tri _ (own X R i) _).trans (add_le_add (radial_foot X R x i v rfl) (radial_foot X R i y h t))
abbrev estate (r:ℕ):= (4*r+1)^4
section packing
variable {Y :Type}[Fintype Y][DecidableEq Y]
lemma fitG {S:Finset Y}(A:Branch.Field Y)(h:Grove A S)(f : Y→SiteX X R)(r:ℕ)
  (v:∀ i∈ S,∀ j∈ S,A.span i j≤2*R.L.val→ (shape X R).span (f i) (f j) ≤ r) : R.L.val* (S.image f).card ≤ estate r*(S.card+R.L.val):=by
 obtain ⟨T,p,w,l⟩:= cover_g A S h R.L.val; let Q:= shape X R; let U:=T.biUnion fun i=> bay Q (f i) r; have hS : S.image f ⊆ U:= by intro i k; obtain ⟨x,f',rfl⟩:= mem_image.mp k; obtain ⟨j,v',g⟩:= (broad_mem ..).mp (w f'); exact mem_biUnion.mpr ⟨j,v',(bay_mem _).mpr (v j (p v') x f' g)⟩
 have he:U.card≤ T.card*estate r:= card_biUnion_le.trans ((sum_le_sum (fun i (_:i∈T)=>capacity X R (f i) r)).trans_eq (by simp [estate])); refine le_trans (Nat.mul_le_mul_left _ ((card_le_card hS).trans he)) ?_; rw [←mul_assoc,mul_comm _ (estate r)]; exact Nat.mul_le_mul_left _ l
end packing
lemma shape_print (u:R.L.val ≤ b.full.val)(S:Seal (Site s))(h:Grove (Grid.field 4 s) S): Grove (shape X R) (S.image (plan X R))∧ R.L.val*(S.image (plan X R)).card≤ estate 2*(S.card+R.L.val):=⟨morph _ _ h _ _ (fun i _ j _ p=>dispatch X R u (p.trans R.L.property)), fitG X R _ h _ 2 (fun _ _ _ _ p=> two_sector X R u p)⟩
lemma turf_print (S:Seal X.Hcols)(h:Turf X S): Grove (shape X R) (S.image (own X R)) ∧ R.L.val*(S.image (own X R)).card ≤ estate 2*(S.card+R.L.val):= ⟨crowd X R S h,fitG X R _ h.1 _ 2 (fun i p j q v=> two_sectorC X R v (h.2 i p j q))⟩
lemma b_blank {T:Type}[Fintype T][DecidableEq T](F:Branch.Field T)(S: Finset T)(r:ℕ) : S⊆ broad F S r :=fun x p=> (broad_mem ..).mpr ⟨x,p, by rw [F.reflex]; omega⟩
lemma b_up {T:Type}[Fintype T][DecidableEq T]{A B:Finset T}(F:Branch.Field T)(p:A⊆B){r t:ℕ}(v:r≤t): broad F A r⊆broad F B t:=by intro i h; obtain ⟨x,g,j⟩:= (broad_mem ..).mp h; exact (broad_mem ..).mpr ⟨x,p g,j.trans v⟩
lemma b_print (S:Seal (SiteX X R))(h:Grove (shape X R) S)(r:ℕ): Grove (shape X R) (broad (shape X R) S r) ∧ (broad (shape X R) S r).card ≤ estate r * S.card:=by
 let A:=shape X R; refine ⟨ (show S∪broad A S r=broad A S r from union_eq_right.mpr (b_blank ..)) ▸ (show Grove A (S∪broad A S r) from ?_), card_biUnion_le.trans ((sum_le_sum (fun i (_:i∈S)=> capacity X R i r)).trans_eq (by simp [estate,mul_comm]))⟩; exact (many A _ h S _ (fun i _=>body_bay ..) (fun i p=>⟨i,p,(bay_mem _).mpr (show A.span i i≤r from (A.reflex i|>.trans_le (Nat.zero_le _)))⟩)).1
lemma frame_bridge (T:Seal (Site s))(U:Tri s)(i:X.Index){u:Per s}{k:ℕ}(g:k≤(X.mark i).n.val)(e:u=(X.mark i).rise k)(h:event u U∈T) : own X R (i-1,U) ∈ broad (shape X R) (T.image (plan X R)) 1 ∧ own X R (i,U)∈ broad (shape X R) (T.image (plan X R)) 1:=by
 let F:=shape X R; let Q:= T.image (plan X R); have hi:plan X R (event u U) ∈ Q:= mem_image_of_mem _ h; unfold plan at hi; rw [am_event,e,band_time X i g] at hi; have hq:(shape X R).span (i-1,tang R U) (i,tang R U) ≤1:=by have he:= adjacent X R (i-1) (tang R U); rwa [sub_add_cancel] at he; -- tune
 split at hi; exact ⟨b_blank F Q 1 hi,(broad_mem ..).mpr ⟨_,hi,hq⟩⟩; exact ⟨(broad_mem ..).mpr ⟨_,hi,(F.sym _ _).le.trans hq⟩, b_blank F Q 1 hi⟩
end YM.CF.BPress.Locale
