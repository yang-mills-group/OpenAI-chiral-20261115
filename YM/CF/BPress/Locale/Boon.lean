import YM.CF.BPress.Locale.Play
/-! Ride covers incur exactly the charge for actual frame lookups. No nonzero condition on fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}{X:Bands s b} {R: Hangar s}{T:Sheet.Atlas}{C C' Lf y:ℝ}{m :ℕ}{F:Net s T Lf y C C' m}{r:ℕ}
variable {S:Support s}{Q:Seal (SiteX X R)}
open Net SU Port
variable {K K':X.Sky}{w w':X.Slates}{U V: Micro s}
namespace Floor
variable (f:Floor X R F S Q)
include f in
lemma shape_at (p:Site s)(h:p∈ S) : plan X R p∈Q:=f.yard (b_blank _ _ _ (mem_image_of_mem _ h))
variable (u:Rights R b Lf y r)(g:Ward X R (broad (shape X R) Q 1) K K')(e:Track X R Q w w') (h:Ear X R Q U V)
include f u g e h
-- near reuse Mission closeness (exact). lemma horizontal station
lemma bridge_w {j:X.Index}{t:Per s}(x:FlatLink s)(p: station X t j)(v: (fl t x).1∈ S): F.roll X w K U (fl t x)= F.roll X w' K' V (fl t x):=by
 rw [fact_H X F w K U _ _ _ p,fact_H X F w' K' V _ _ _ p]; let W:= fl t x; have hp:=f.shape_at _ v; have ht:U W= V W:=h _ hp; unfold anglePaid angleBeg; rw [show U (fl t x)= _ from ht,EdgeKey_H]; cases l:keyV X t x with
 |none=>rfl
 |some i=>
     have hx:=key_reads X p l; have hg: plan X R (fl t x).1=own X R i.1:= by rw [hx]; unfold plan fl; simp only [am_event, collar_ride X p le_rfl]; -- tune
     simp only [Option.elim_some]; rw [g i (b_blank _ Q 1 (hg ▸ hp))]
-- deep and memory assumptions. branch m mark
variable {i : X.Index}
omit u
lemma coup (p:i∈X.nc){x:Per s}{t:Tri s}(l:event x t∈richT X S i)(k:ℕ) : F.deck (X.mark i) ((X.mark i).reads (X.atmospheric K)) (summit X T y w K i) k t=F.deck (X.mark i) ((X.mark i).reads (X.atmospheric K')) (summit X T y w' K' i) k t:=by
 have he : Fin.tail (event x t)=t:=Fin.tail_cons ..; obtain ⟨a,b⟩:= see_pair f p l g e; rw [he] at a b; unfold deck access; split; exact a; exact b
lemma consort (p:i∈X.nc) (k:ℕ)(t:FlatLink s)(W:Link s)(u:W=fl ((X.mark i).rise k) t)(a:2*umbra b ≤ k)(b':k+2*umbra b≤ b.marked.val) (l:W∈inside S) :
 F.avgN X (X.atmospheric K) i (summit X T y w K i) W= F.avgN X (X.atmospheric K') i (summit X T y w' K' i) W:=by
 let M:= X.mark i; let d:=M.rise k; have hx:k ≤ b.marked.val:=by omega
 rw [u] at l ⊢; obtain ⟨h1,h2⟩:=inside_iff ..|>.mp l
 let x':=hop t.1 t.2 1; have hk(m:Tri s): peek X i (event d m):=⟨k,a,b',rfl⟩; have t':event d x' ∈ S:=by unfold x'; rw [hop_glide]; unfold d M; unfold fl at h2; simpa only [event_across] using h2
 have Hp:event d t.1∈richT X S i:= mem_filter.mpr ⟨h1,hk t.1⟩ -- tune implicit
 obtain ⟨w1,w2⟩:=frame_bridge X R S t.1 i hx rfl h1; let hq:=mem_filter.mpr ⟨t',hk x'⟩; have hD:= f.coup g e h p Hp k; have hT:= f.coup g e h p hq k; unfold avgN; simp_rw [if_neg (mem_sdiff.mp p|>.2)]; change horizontal d (F.template M _ _) t = horizontal d (F.template M _ _) t; rw [F.readH _ _ _ hx,F.readH _ _ _ hx]; unfold tarH; obtain ⟨v1,v2⟩:=see_pair f p Hp g e; obtain ⟨v3,v4⟩:=see_pair f p hq g e; -- tune implicit h order
 dsimp only [event] at v1 v2 v3 v4; unfold starry at v1 v2 v3 v4; rw [Fin.tail_cons] at v1 v2 v3 v4; simp only [adjust,built]; have W:= g.drop (b_blank _ Q 1); unfold x' at v3 v4 hT; unfold M; rw [poleLeft i p W t (f.yard w1),poleRight i p W t (f.yard w2)]; simp only [Pi.inv_apply,hD,hT,v1,v2,v3,v4]; -- tune x' mismatch
end Floor
end YM.CF.BPress.Locale
