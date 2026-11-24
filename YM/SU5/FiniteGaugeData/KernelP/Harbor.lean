import YM.SU5.FiniteGaugeData.KernelP.Parliament
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
local notation "N" i:max=> nectar Y h i W' R a
local notation "Ys" k:max=> days Y h k W' R a
local notation "V"=> Playlist.Show.Vect Y h a 0
structure Hostage (X Y:Type)[AddCommMonoid X][Module ℂ X][AddCommMonoid Y][Module ℂ Y] (lens:ℕ→ X→ Y)(panel:ℕ→Y→ₗ[ℂ] X)(R:Y→ℕ→Prop) (F:ℕ→ X→ X→ℂ) where
 space: Hilbert
 value : Y →ₗ[ℂ] space
 leaf (s:ℕ) : X→ₗ[ℂ] space
 measure s x y : inner ℂ (leaf s x) (leaf s y)= F s x y
 fleets (s:ℕ)(x:X): leaf s x=value (lens s x)
 docks (s:ℕ)(w:Y): R w s→ leaf s (panel s w)=value w
 varied : DenseRange value
variable (Φ) in
abbrev Harbor := Hostage (Decko Y h a) (Playlist.Show.Vect Y h a 0) (fun s=> seedling Y h s a) (fun s=> days Y h s W' R a) (fun w s=> Arrive Y h w.val s) (fun s x y=> Φ s (helve Kₜ a x.val y.val))
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)(w v₁:Vect Y h a 0)
include H
lemma PortWhole : (fun s=> H.leaf s (days Y h s W' R a w)) =ᶠ[atTop] fun _=> H.value w:= (arrived Y h w.val).mono fun i p=>H.docks i w p
lemma Harbor.up : H.leaf (s+1) (nectar Y h s W' R a x)= H.leaf s x := by
 let w:=seedling Y h s a x; let t:Arrive Y h w.val s:= pulse_arr Y h s x.val; rw [H.fleets s x]; change _= H.value w; rw [← H.docks (s+1) w (arriving Y h s _ a w t (by omega)), nectar_next Y h s W' R a w t,show (days Y h s W' R a) w=x from fullDay ..]
lemma Harbor.upwards (p:s ≤ i): ∃ y:D,H.leaf i y=H.leaf s x:=by
 induction i,p using Nat.le_induction with
 | base=> exact ⟨x,rfl⟩
 | succ n _ ih=> obtain ⟨t,e⟩:= ih; exact ⟨nectar Y h n W' R a t,(H.up Y h n W' R a t).trans e⟩
lemma leaf_lift (P:Set H.space)(p:IsClosed P)(v:∀ i:ℕ,s ≤ i→∀ y:Decko Y h a,H.leaf i y ∈ P) : ∀ x:H.space,x∈P:= fun x=>H.varied.induction (by
 rintro _ ⟨w,rfl⟩; obtain ⟨i,c,h⟩:= ((PortWhole Y h W' R a H w).and (eventually_ge_atTop s)).exists; dsimp only at c; rw [←c]; exact v i h _) p x
lemma leaf_ext {H': Hilbert}{F G:H.space→L[ℂ]H'}(p:∀ i:ℕ,s ≤ i→∀ y:Decko Y h a,F (H.leaf i y)= G (H.leaf i y)) : F=G:= ContinuousLinearMap.ext fun x=> leaf_lift Y h s W' R a H {x| F x=G x} (isClosed_eq F.continuous G.continuous) p x

include S'
lemma itineraryH : inner ℂ (H.value w) (H.value v₁)= coordinate Y h W' R Φ a 0 w v₁:= by
 obtain ⟨s,u,v⟩:=((arrived Y h w.val).and (arrived Y h v₁.val)).exists; rw [← H.docks s w u,← H.docks s v₁ v,H.measure s, contracts Y h s W' R A S' a w v₁ u v]
omit H
-- construction from Sphere in same data.H first.Connection.Fullness.
section build
private def duet : Den (coordinate Y h W' R Φ a 0):=Classical.choice (throne (coordinate Y h W' R Φ a 0) (coords Y h W' R A S' a 0))
local notation "D'"=>duet Y h W' R A S' a
private abbrev vecto (s:ℕ)(x:Decko Y h a) := (duet Y h W' R A S' a).paid (seedling Y h s a x)
local notation "L"=> vecto Y h W' R A S' a s
private lemma pub : inner ℂ (vecto Y h W' R A S' a s x) (vecto Y h W' R A S' a s y)= Φ s (helve Kₜ a x.val y.val):=by unfold vecto; rw [(D').folding, contracts Y h s W' R A S' a _ _ (pulse_arr Y h s x.val) (pulse_arr Y h s y.val),fullDay,fullDay]
omit S' in
private lemma rotor {H:Hilbert} {x y:H} (h:inner ℂ x x=inner ℂ y x)(p:inner ℂ x y=inner ℂ y y) : x=y:=sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).1 (by rw [inner_sub_right,inner_sub_left,inner_sub_left,h,p,sub_self,sub_self,sub_zero]))
private def pylon : Decko Y h a→ₗ[ℂ] (duet Y h W' R A S' a).space where
 toFun:= vecto Y h W' R A S' a s
 map_add' x y:= by
    have e(z:D): inner ℂ ((L) (x+y)) ((L) z)= inner ℂ ((L) x+ (L) y) ((L) z):=by rw [inner_add_left]; simp_rw [pub,helve]; rw [Subalgebra.coe_add,ice_more, add_mul,map_add]
    apply rotor; exact e _; rw [inner_add_right,inner_add_right,e,e]
 map_smul' c x:= by
    change (L) (c • x)=c • (L) x; have e(z:D):inner ℂ ((L) (c • x)) ((L) z)=inner ℂ (c • (L) x) ((L) z):=by rw [inner_smul_left]; simp_rw [pub,helve]; rw [Subalgebra.coe_smul,ice_paid,Algebra.smul_mul_assoc,map_smul]; rfl
    apply rotor; exact e _; rw [inner_smul_right,inner_smul_right,e]
lemma affairs (p: Arrive Y h w.val s): pylon Y h s W' R A S' a ((Ys s) w)=(D').paid w:= by
 let v:=seedling Y h s a ((Ys s) w); have h':Arrive Y h v.val s:=pulse_arr Y h s (((Ys s) w).val)
 have he (x:V)(t:Arrive Y h x.val s):inner ℂ ((D').paid v) ((D').paid x)=inner ℂ ((D').paid w) ((D').paid x):=by rw [(D').folding,(D').folding, contracts Y h s W' R A S' a v x h' t,contracts Y h s W' R A S' a w x p t,show (Ys s) v=(Ys s) w from fullDay ..]
 exact rotor (he v h') (he w p)
def Port : Harbor Y h W' R Φ a where
 space:= (duet Y h W' R A S' a).space
 value:= (duet Y h W' R A S' a).paid
 leaf s:= pylon Y h s W' R A S' a
 docks s w:= affairs Y h s W' R A S' a w
 measure s x y:= pub Y h s W' R A S' a x y
 fleets s x:=rfl
 varied:= (D').issued
#print axioms Port
end build
-- compare via Harbor presentation using the actual Ω as harbor.Shape.Poles.Delivery
omit S'
def OriginalH : Harbor Y h W' R (actual Y h W') a where
 space:= (A a).space
 value:= (A a).paid
 leaf s:= store Y h s W' R a (A a)
 docks s w:= contains Y h s W' R a (A a) w
 measure s x y:= lawStore Y h s W' R a (A a) x y
 fleets s x:= rfl
 varied := (A a).issued
#print axioms OriginalH
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
