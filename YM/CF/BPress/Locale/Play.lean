import YM.CF.BPress.Locale.Cape
/-! Actual reading on Λ. Continuation through V-space at O(1) more halo, stated pre-hset too. Labels currently Slates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}(X:Bands s b)(R:Hangar s){T:Sheet.Atlas}{Lf C C' y:ℝ}{a:ℕ}
open Net SU Port
-- maybe scope workaround: holds W space. raw/ticket assumption & permit rearrangements later
abbrev Ward (Q:Seal (SiteX X R))(K K':X.Sky) := ∀ i:X.Air, own X R i.1 ∈ Q → K i=K' i
structure Track (Q:Seal (SiteX X R))(w w':X.Slates):Prop where
 early (i:X.Index)(x:Tri s) : i∈X.nc → own X R (i-1,x)∈Q→ (w i).1 x=(w' i).1 x
 late(i:X.Index)(x:Tri s) : i∈X.nc → own X R (i,x)∈Q→(w i).2 x=(w' i).2 x
abbrev Ear (Q:Seal (SiteX X R))(U V:Micro s):= ∀ i:Link s, plan X R i.1∈Q → U i=V i

variable {X R}{Q W: Seal (SiteX X R)}{U V:Micro s}{K K':X.Sky}{w w':X.Slates}
lemma Track.drop (A:Track X R Q w w')(v:W⊆Q): Track X R W w w':= ⟨fun i x k h=> A.early i x k (v h),fun i x k h=> A.late i x k (v h)⟩
lemma Ward.drop (A:Ward X R Q K K')(v:W⊆Q): Ward X R W K K':=fun i p=>A _ (v p)
lemma Ear.drop (A:Ear X R Q U V)(v:W⊆Q): Ear X R W U V:=fun i p=>A _ (v p)
-- Summary from `urchin` read on crown. owners sky all N faces.
lemma horizonDepth (i:X.Index)(x:FlatLink s)(u: X.Sky): horizontal (X.depth i b.D) (X.atmospheric u) x=u ((i,x.1),(⟨b.D-1,Nat.sub_one_lt b.D_pos.ne'⟩,x.2)):=by
 let k:Fin b.D:=⟨b.D-1,Nat.sub_one_lt b.D_pos.ne'⟩; have ht:k.val+1=b.D:= Nat.sub_add_cancel b.D_pos; let e:X.Air:= ((i,x.1),k,x.2); unfold horizontal; rw [show fl (X.depth i b.D) x=X.skylink e from ?_]; exact X.mat_atm u e; change _=fl (X.depth i (k.val+1)) (x.1,x.2); rw [ht]
lemma right_shadow {i:X.Index}(p:i∈ X.nc): X.depth i b.D=(X.mark i).last:=by rw [X.depth_D, if_neg (X.nc_index ..|>.mp p)]; rfl
lemma left_shadow {i:X.Index}(p:i∈ X.nc): X.depth (i-1) b.D=(X.mark i).o:=by rw [X.depth_D, if_pos (X.next_prev i|>.mpr ((X.nc_index ..).mp p)), sub_add_cancel]; rfl
lemma poleLeft (i:X.Index)(p:i∈ X.nc)(u:Ward X R Q K K') (x:FlatLink s) (e:own X R (i-1,x.1)∈ Q) : ((X.mark i).reads (X.atmospheric K)).1 x=((X.mark i).reads (X.atmospheric K')).1 x:=by change horizontal (X.mark i).o (X.atmospheric K) x=horizontal (X.mark i).o (X.atmospheric K') x; rw [←left_shadow p,horizonDepth,horizonDepth]; exact u _ e
lemma poleRight (i:X.Index)(p:i∈X.nc)(u:Ward X R Q K K') (x:FlatLink s)(e:own X R (i,x.1)∈Q): ((X.mark i).reads (X.atmospheric K)).2 x=((X.mark i).reads (X.atmospheric K')).2 x:=by change horizontal (X.mark i).last (X.atmospheric K) x=horizontal (X.mark i).last (X.atmospheric K') x; rw [←right_shadow p,horizonDepth,horizonDepth]; exact u _ e
-- read both coordinates of frame.Flow (even if not allowed). need costs for plaq to compute h labels. halo+1
lemma horizonT {i:X.Index}{x:Tri s}(p:own X R (i,x)∈ Q)(k:SpatialDir): own X R (i,hop x k 1)∈broad (shape X R) Q 1:=by refine (broad_mem ..).mpr ⟨_,p,?_ ⟩; exact radial_foot X R _ _ ((delta_hop ..).trans R.L.property) rfl
lemma hue_screen (T:Sheet.Atlas)(y:ℝ)(f g:Horiz s)(i:Tri s)(h:∀ k:SpatialDir, f (i,k)=g (i,k))(t:∀ k j:SpatialDir,f (hop i k 1,j)=g (hop i k 1,j)): T.hue y f i=T.hue y g i:=by ext x; unfold Sheet.Atlas.hue; simp only [WithLp.ofLp_toLp]; rw [plaq,h,h,t,t]; rfl -- tune
variable {S:Support s}{F:Net s T Lf y C C' a}
-- Bundle F comp reads at EACH used coalesced site. Peek.
abbrev summit (X:Bands s b)(T:Sheet.Atlas)(y:ℝ)(w:X.Slates) (K:X.Sky)(i:X.Index) := see (T:=T) (y:=y) X w (X.atmospheric K) i
def starry (F:Net s T Lf y C C' a)(i:X.Index)(w:X.Slates)(K:X.Sky): Duo s:= F.fill ((X.mark i).reads (X.atmospheric K)) (summit X T y w K i)
lemma see_pair (v:Floor X R F S Q) {i:X.Index}(p:i ∈ X.nc){x:Site s}(e:x∈richT X S i) (g:Ward X R (broad (shape X R) Q 1) K K')(h:Track X R Q w w') :
 (starry F i w K).1 (Fin.tail x)= (starry F i w' K').1 (Fin.tail x) ∧ (starry F i w K).2 (Fin.tail x)= (starry F i w' K').2 (Fin.tail x) := by
 let T':=family X S i x; let G:=shape X R; have he : Fin.tail x ∈ firm T':= mem_image.mpr ⟨x,family_ne (mem_filter.mpr ⟨(mem_filter.mp e).1,deep_m ((mem_filter.mp e).2) (by omega)⟩),rfl⟩; obtain ⟨B,f,j⟩:= v.knows (i,T') ((gaze_mem ..).mpr ⟨x,e,rfl⟩); let z(S:X.Sky):=(X.mark i).reads (X.atmospheric S); have hn:i∉X.dc:= (mem_sdiff.mp p).2; unfold starry fill summit see putF; simp only [if_neg hn]; constructor
 · have hk(a:Tri s)(p:a∈B): own X R (i-1,a)∈Q:= j (mem_union_left _ (membership p)); let t(a:FlatLink s)(e:a.1∈ B): (z K).1 a=(z K').1 a:= poleLeft i p (g.drop (b_blank ..)) a (hk a.1 e); -- tune
   apply f.read (z K).1 (z K').1 _ _ (fun a e _=>t a e) _ he; intro a v; unfold Sheet.Atlas.frame Sheet.Atlas.give; rw [h.early i a p (hk a v)]; change _ * T.sect (T.hue y (z K).1 a)= _ * T.sect (T.hue y (z K').1 a); rw [hue_screen T y _ _ a (fun i=> t (a,i) v) (fun k l=>poleLeft i p g _ (horizonT (hk a v) k))]
 have hk(a:Tri s)(p:a∈B): own X R (i,a)∈Q:= j (mem_union_right _ (membership p)); let t(a:FlatLink s)(e:a.1∈ B) : (z K).2 a=(z K').2 a:= poleRight i p (g.drop (b_blank ..)) a (hk a.1 e); apply f.read (z K).2 (z K').2 _ _ (fun a e _=> t a e) _ he; intro a v; unfold Sheet.Atlas.frame Sheet.Atlas.give; rw [h.late i a p (hk a v)]; change _ * T.sect (T.hue y (z K).2 a)= _ * T.sect (T.hue y (z K').2 a); rw [hue_screen T y _ _ a (fun i=> t (a,i) v) (fun k l=>poleRight i p g _ (horizonT (hk a v) k))]
end YM.CF.BPress.Locale
