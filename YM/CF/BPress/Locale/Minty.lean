import YM.CF.BPress.Locale.Boon
/-! charge eq:B-map; connection tests for arbitrary B-map length. Build fields through aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}{X:Bands s b} {R:Hangar s}{T:Sheet.Atlas}{C C' Lf y:ℝ}{m:ℕ}{F:Net s T Lf y C C' m}{r:ℕ}
variable {S:Support s}{Q:Seal (SiteX X R)}
open Net SU Port
variable {K K':X.Sky}{w w':X.Slates}{U V: Micro s}
namespace Floor
variable (f:Floor X R F S Q)(u:Rights R b Lf y r)(g:Ward X R (broad (shape X R) Q 1) K K')(e:Track X R Q w w')(h:Ear X R Q U V)
include f u g e h
lemma cut_v (z: Link s)(hz:z∈ inside S){i:X.Index}{x:Tri s}(v:z=vl ((X.mark i).rise (X.mark i).cut) x)(j:i∈ X.nc)(t:z∈ X.pay i) : F.roll X w K U z= F.roll X w' K' V z:=by
 let d:=(X.mark i).cut; let q:=(X.mark i).rise d; have hx:U z=V z:= h z (f.shape_at _ ((inside_iff ..).mp hz).1); have hv:event q x∈richT X S i:=mem_filter.mpr ⟨ (inside_iff ..|>.mp (v ▸ hz)).1,d,(show 2*umbra b ≤ d from (by unfold d umbra; unfold cut; change 2*(_ / _) ≤ b.marked.val/2; omega)),(by change b.marked.val/2 + _ ≤ b.marked.val; unfold umbra; omega),rfl⟩
 rw [rep_pay X F w K U i z t,rep_pay X F w' K' V i z t,hx]; apply congrArg (· * V _); unfold avgN; simp_rw [if_neg (mem_sdiff.mp j|>.2)]; rw [v]; change normal q (F.template (X.mark i) _ (summit X T y w K i)) x=normal q (F.template (X.mark i) _ (summit X T y w' K' i)) x; unfold q; rw [F.readV _ _ _ (X.mark i).cut_lt,F.readV _ _ _ (X.mark i).cut_lt]; unfold tarV; simp only [Pi.inv_apply, Pi.mul_apply]; rw [f.coup g e h j hv d,f.coup g e h j hv (d+1)]
lemma light_all (z:Link s)(v:z∈ inside S) : F.roll X w K U z= F.roll X w' K' V z:=by
 have hp:= f.shape_at _ ((inside_iff ..).mp v).1; rcases X.kind z with p|p|p
 · obtain ⟨j,_,k⟩:= mem_image.mp p; let a:=X.skylink j; have h': own X R j.1∈ Q:=by apply (show plan X R a.1=own X R j.1 from ?_) ▸ (show plan X R a.1∈Q from (show plan X R (X.skylink j).1∈Q from k.symm ▸ hp)); simp only [plan,a,skylink,fl,am_event,ditch_ride X j.1.1 _ (depth_time X j.1.1 (k:=j.2.1.val+1) j.2.1.isLt)]; -- tune proof
   rw [←k,actor,actor]; exact g j (b_blank _ Q 1 h')
 · obtain ⟨i,_,p⟩:=mem_biUnion.mp p; have hU:= h z hp; by_cases q:i∈X.dc; · rw [rep_pay X F w K U i z p, rep_pay X F w' K' V i z p,hU]; simp only [avgN,q, ↓reduceIte]
   have hb:=p; unfold Bands.pay at hb; rw [if_neg q] at hb; have hm:i∈X.nc:= mem_sdiff.mpr ⟨mem_univ _,q⟩; rcases (X.mark i).banks_tem _|>.mp hb with ⟨x,k⟩| ⟨k,z',p',x,k'⟩; · exact f.cut_v u g e h z v k hm p
   change k<b.marked.val at z'; by_cases a:(2*umbra b≤ k∧ k+2*umbra b≤ b.marked.val)
   · rw [rep_pay X F w K U i z p,rep_pay X F w' K' V i z p,hU]; exact congrArg (·*V z) (f.consort g e h hm k x z k' a.1 a.2 v)
   rw [k'] at v ⊢; by_cases w0:k< 2*umbra b
   · refine f.bridge_w u g e h (j:=i-1) x ?_ ((inside_iff ..).mp v).1; have ht:= (postClock X (i-1) (k:=k) (by unfold umbra at w0; unfold cloak; omega)).1; rwa [sub_add_cancel] at ht
   have hg:k+2*umbra b > b.marked.val:= by omega
   refine f.bridge_w u g e h (j:=i) x ?_ ((inside_iff ..).mp v).1; apply (show station X ((X.mark i).rise k) i from ?_); rw [show (X.mark i).rise k=(X.mark i).fall (b.marked.val-k) from ?_]; exact (preClock X i (k:=b.marked.val-k) (by unfold umbra at hg; unfold cloak; omega)).1; unfold Tunnel.fall; rw [X.mark_n,Nat.sub_sub_self z'.le] -- tune mark_n type
 exact (F.roll_hold X w K U _ p).trans (F.roll_hold X w' K' V _ p).symm
-- across block-transform one halo pay. state projection on Fills. Kernel T only gauge; other links e.g. pulsespinise
omit g
lemma lightV (A:Fare X){r':ℕ}(q:r'≤R.L.val)(c:Connect X A r')(S' V':Seal X.Hcols)(x y':Quarters X)
 (p:let M:=fun i=> own X R i∈ broad (shape X R) Q 2; ∀ i, M i → (i∈ S' ↔ i∈V') ∧ x.1 i=y'.1 i ∧ x.2 i=y'.2 i):
 let K:= Aback X (bodyBase X y A S' x); let K':=Aback X (bodyBase X y A V' y');
 Lattice.Agrees S (F.roll X w K U) (F.roll X w' K' V) ∧ Ward X R (broad (shape X R) Q 1) K K':=by
 intro K K'; suffices ht:Ward X R (broad (shape X R) Q 1) K K' from ⟨fun i v w=> f.light_all u ht e h i (inside_iff ..|>.mpr ⟨v,w⟩),ht⟩
 intro i v; let a:= i.1; let U:=broad (shape X R) Q 2; have he(j)(h:j∈columnBall X i.1 r') : own X R j∈ U:=by
   obtain ⟨k,f,g⟩:= (broad_mem ..).mp v; refine (broad_mem ..).mpr ⟨k,f,?_⟩; exact ((shape X R).tri _ (own X R a) _).trans (add_le_add g (radial_foot X R i.1 j ((column_eq.mp h).2.trans q) (column_eq.mp h).1.symm)) -- tune h shadow
 exact congrFun (body_reads c S' V' x y' i.1 (fun j u=>(p j (he j u)).1) (fun j u=>(p j (he j u)).2.1) (p _ (he _ (column_self ..))).2.2 (y:=y)) i.2
end Floor
end YM.CF.BPress.Locale
