import YM.CF.BPress.Locale.Mint
/-! block-price fiber counts. Exact area. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}(X:Bands s b)(R:Hangar s)
abbrev Patio := Fin 3 → Fin R.L.val
def packB (x:Tri s) : Patio R:= fun i=> innerV R.geom 0 (x i)
def porch (u: SiteX X R)(x:Patio R) : X.Hcols:= (u.1,fun i=> Radix.clock s R.L R.period R.geom 0 (u.2 i,x i))
lemma porch_own (u: SiteX X R)(x:Patio R) : own X R (porch X R u x)=u:= Prod.ext rfl (funext fun i=>idx_at ..)
lemma pack_p (u:SiteX X R)(x: Patio R): packB R (porch X R u x).2=x:= funext fun i=> congrArg Prod.snd (Equiv.symm_apply_apply (Radix.clock s R.L R.period R.geom 0) (u.2 i,x i))
def lodge : X.Hcols≃ SiteX X R × Patio R where
 toFun x:=(own X R x,packB R x.2)
 invFun x:=porch X R x.1 x.2
 left_inv x:=Prod.ext rfl (funext fun i=> (Radix.clock s R.L R.period R.geom 0).apply_symm_apply (x.2 i))
 right_inv x:=Prod.ext (porch_own ..) (pack_p ..)
def podium (u:SiteX X R):=univ.filter fun x=> own X R x=u
lemma podium_cost (u:SiteX X R): (podium X R u).card=R.L.val^3:=by
 have hp: podium X R u= univ.image (porch X R u):=by ext x; refine ⟨fun v=>?_,fun v=>?_⟩; refine mem_image.mpr ⟨packB R x.2,mem_univ _,?_⟩; rw [← (mem_filter.mp v).2]; exact (lodge X R).left_inv x; obtain ⟨j,v,rfl⟩:=mem_image.mp v; simp [podium,porch_own]
 rw [hp, card_image_of_injective,card_univ]; · simp [Patio]
 intro i j v; rw [← pack_p X R u i, ←pack_p X R u j,v]
-- each block micro-charged hits ≤near*LC^3*( ...). Need injection using owner & temporal extent near.
def NearBlock (r:ℕ) (x:Site s):Prop:=∃ i:X.Index, ZoneNear X i r (x 0)
def meets (r:ℕ)(S:Support s) := ∃ x∈S, NearBlock X r x
def positions (u:SiteX X R)(r:ℕ):= univ.filter fun x:Site s=> plan X R x=u ∧ NearBlock X r x
lemma pinned_cost (u:SiteX X R){r:ℕ}(v:r ≤ cloak b) : (positions X R u r).card ≤ R.L.val^3 * (b.D+2*r+1):=by
 have hr : 2*r<b.marked.val:= Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ v) (cloak_lt b); let i:=u.1; let M:=Fest X i r hr; let U:=range (b.D+2*r+1); let P:=positions X R u r; let Q:=podium X R u; let f(n:X.Hcols×ℕ):= event (M.rise n.2) n.1.2
 have he:P ⊆ (Q×ˢ U).image f:=by
   intro x k; obtain ⟨a,j,c⟩:= (mem_filter.mp k).2; have h: j=i:= (collar_ride X c v).symm.trans (congrArg Prod.fst a); rw [h] at c; obtain ⟨t,d,H⟩:= M.internal x|>.mp ((z_iff X i hr x).mp ((zone_of_halo X i r x).2 c)); refine mem_image.mpr ⟨ (panel X x,t), mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,a⟩, mem_range.mpr (Nat.lt_succ_of_le (show t≤ b.D+2*r from d))⟩,?_⟩; unfold f; rw [←H]; exact event_eta ..
 apply (card_le_card he).trans; apply card_image_le.trans; rw [card_product,podium_cost]; unfold U; rw [card_range]
end YM.CF.BPress.Locale
