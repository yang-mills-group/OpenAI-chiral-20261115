import YM.SU5.Reconstruction.Marque.Precinct
import YM.SU5.Reconstruction.Marque.Seat
/-! Upholster the net from its priced bodies. Bound only is enough to buy stars. -/
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric Real BridgeClub Picket Anvil ContinuousLinearMap CrossedFrame
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical
variable {H:Hilbert}(S:OS.Semigroup H clock)
local notation "V"=> Wander H.space
local notation "Ū"=> trans S
local notation "τ"=> parcelUp S
noncomputable def mover(x:E4):V:=deal (mobile S x)
lemma transport(x:E4): Fleet (mover S x) false:= deal_fleet ..
lemma mover_at (x:E4)(y:H): mover S x y=Ū x y:= deal_at ..
lemma mover_parcel (x:E4)(A:H.Op): Across (mover S x) A (τ x A):= by intro y; rw [mover_at,mover_at]; exact show (parcelUp S x A*Ū x) y = (Ū x*A) y from (by unfold parcelUp; rw[mul_assoc (Ū x*A),mail_inv,mul_one])
-- generic monotone push f∈M => ...
abbrev Promotes (v:V)(M N:Net H):Prop:=∀ x∈ M,∀ y:H.Op, Across v x y→ y∈N
lemma promotes_trans {M N P:Net H}{v w:V}(p:Promotes v M N)(q:Promotes w N P){a:Bool}(f:Fleet v a): Promotes (w*v) M P:= by
 intro x d y e; refine q _ (p x d _ (f.arr x)) y ?_; intro u; obtain ⟨i,rfl⟩:= v.surjective u; rw [f.arr]; exact e i
lemma promotion_includes {M N P:Net H}{v:V}(p:Promotes v M N)(q:N≤P):Promotes v M P:= fun x h y e=>q (p x h _ e)
-- double ring
lemma promotes_bic {M:Net H}{X:Set H.Op}{v:V}{a:Bool}(f:Fleet v a)(e:∀ x∈ X,star x∈X)(h:∀ x∈ X,f.Form x∈ M): Promotes v (Auditorium X) M:= by
 intro x p y t; rw [← M.commutant_commutant]; apply VonNeumannAlgebra.mem_commutant_iff.mpr; intro g q
 let A:= f.inv.Form g; have hv:Across v A g:= by simpa only [inv_inv] using (f.inv.arr g).inv
 have ha: A∈Set.centralizer X:= by
    intro i b; have he:f.Form i * g=g*f.Form i:=VonNeumannAlgebra.mem_commutant_iff.mp q _ (h _ b); have hp:= (f.arr i).multiply hv; have hq:= hv.multiply (f.arr i); rw [he] at hp; exact hp.inv.unique hq.inv
 rw [←SetLike.mem_coe,lobby X e] at p
 exact (hv.multiply t).unique ((p A ha).symm ▸ t.multiply hv)
structure Gallery (H:Hilbert)(S:OS.Semigroup H clock) where
 Row : Type
 hue : Row → Set H.Op
 footprint : Row → Set E4
 close_footprint : ∀ i:Row, IsCompact (footprint i)
 shades : ∀ i x,x∈hue i→ star x∈hue i
variable {S}
namespace Gallery
variable (G:Gallery H S)
local notation "Λ"=> G.footprint
local notation "F"=> G.hue
-- defeq with CP iso
noncomputable def tiles (W:Set E4):Set H.Op:={x| ∃ (i:G.Row)(q:E4)(A:H.Op), A∈F i∧ strace q (Λ i) ⊆ W ∧ x=τ q A }
noncomputable def lobby(W:Set E4): Net H:= Auditorium (G.tiles W)
variable {i:G.Row}
local notation "M"=> G.lobby
lemma tiles_meet (W:Set E4)(x:H.Op)(p:x∈ G.tiles W):star x∈G.tiles W:= by
 obtain ⟨i,d,B,h,t,rfl⟩:=p; exact ⟨i,d,star B, G.shades i B h,t,parcel_star ..⟩
lemma typeA {A:H.Op}(p:A∈ G.hue i)(q:E4) : (τ q A)∈ M (strace q (Λ i)):= audition _ ⟨i,q,A,p,Set.Subset.refl _,rfl⟩
lemma mono {U W:Set E4}(h: U⊆W):M U≤M W:=by apply houseGrow; rintro A ⟨i,q,B,t,v,w⟩; exact ⟨i,q,B,t,v.trans h,w⟩ -- U notation shadows bug
lemma traceAppointment(U:Set E4)(q:E4): Promotes (mover S q) (M U) (M (strace q U)):=by
 refine promotes_bic (transport S q) (G.tiles_meet U) ?_; rintro _ ⟨i,t,B,u,v,rfl⟩; rw [((transport S q).arr _).unique (mover_parcel S q (τ t B))]; apply audition;
 refine ⟨i,q+t,B,u,?_, (parcel_add ..).symm⟩; rw [←strace_add]; exact Set.image_mono v
lemma traceAct (W:Set E4)(q:E4):Conveys (mover S q) (M W) (M (strace q W)):= by
 refine fun x y e=>⟨fun p=>G.traceAppointment W q x p y e, fun p=>?_⟩;
 have hx: mover S (-q) = (mover S q)⁻¹:= inv_eq_of_mul_eq_one_left (b:=mover S q) (a:=mover S (-q)) ?_ |>.symm -- tune
 have he:=G.traceAppointment (strace q W) (-q) y p x (hx.symm ▸ e.inv); simpa only [strace_add,neg_add_cancel,strace_zero] using he
 ext z; rw [wander_mul,mover_at,mover_at]; exact DFunLike.congr_fun (mail_inv S q) z
-- march singular stars & envelope
abbrev bay (X:Set H.Op):= StarAlgebra.adjoin ℂ X
lemma rear {X:Set H.Op}{Y:Net H}(p:X⊆(Y:Set H.Op)) : (bay X:Set H.Op)⊆ (Y:Set H.Op):= show StarAlgebra.adjoin ℂ X ≤ Y.toStarSubalgebra from StarAlgebra.adjoin_le p
-- petition. datum p.App with $Eu pulse$; true purchase
structure VacDues(X:Set H.Op)(Ω:H)(y:H): Prop where
   ask : ∃ (A:ℕ→H.Op)(C:ℝ), 0≤C ∧ (∀ i, A i∈bay X ∧ ‖A i‖≤ C) ∧ ∀ v:H,Tendsto (fun i=> inner ℂ v (A i Ω)) atTop (𝓝 (inner ℂ v y))
-- inside recover enough monitoring
variable {Y X':Net H}{Ω v:H}
lemma settled {X:Set H.Op}(p:VacDues X Ω v) (b:X⊆(Y:Set H.Op))(u:X⊆(X':Set H.Op)): ∃ x∈ Y,x∈ X'∧ x Ω=v:=by
 let L:= Ultrafilter.of (atTop:Filter ℕ); obtain ⟨A,C,h,r,w⟩:=p.ask; obtain ⟨f,h',p'⟩:= Limit_World L h (fun i:ℕ=>(r i).2)
 exact ⟨f,staysClosed p' (fun i=> rear b (r i).1),staysClosed p' (fun i=>rear u (r i).1),ext_inner_left ℂ fun x=> tendsto_nhds_unique (p'.confirms x Ω) ((w x).mono_left (Ultrafilter.of_le ..))⟩
end Gallery
end YM.Marque.Flow
