import YM.SU5.FiniteGaugeData.Largo.Azure
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
-- net loans. µ,ξ. own marks bound independently. costs heights.MAX across windows. push all extra durability eventually cut d before r? here for any d. width of P influences via µ.
variable {N X:Side} {M:Tulip.Male}{l l' r u d k n v m w:ℕ} {σ ζ μ K:ℝ}
open Curtain Concert Waltz Manifest
set_option quotPrecheck false
structure Suite (n:ℕ)(X:Side)(M:Tulip.Male)(U Lft Rgt:Finset Cover)(g f ε:ℝ): Prop where
  choice : ∃ S T Z, Concert (Y:=Fin n) X (flatH M X) Lft Rgt S T Z g f ε ∧ cutM (wal X U)* Z=Z
abbrev artE (σ ζ μ K:ℝ)(u d:ℕ):=Real.exp (-σ*d)*ζ*u+2*(Real.exp (-μ*d)*K)*((1+ζ)*u)
lemma artE_mono (Z:0≤ ζ)(k':0≤ K)(h:u≤m): artE σ ζ μ K u d≤ artE σ ζ μ K m d:=by unfold artE; gcongr
local notation "Q"=> platter N k
local notation "Z"=> LodgeP d N.val (r+d)
local notation "SΨ"=> LodgeP 0 N.val (r+d+d)
variable (P: Ream (bar 4 M.val) μ K) (h:0<σ)(z:0<ζ)(v₀:0<μ)(u₀:0≤K)
variable (H:∀ p:Stereo N, p∈ (platter N k)→ Ream (shineF (stairF 4 (badge p) M)) σ ζ)
variable (g:r+d+d+(r+d+d)<N.val)(s:N.val=24*k)(x:N.val≤X.val)
variable (p:l+u≤r)(p':l'+w≤r)
variable (y:boxSeats l u M N false (platter N k) n)(y':boxSeats l' w M N true (platter N k) n)
abbrev Studio (d r N:ℕ):ℕ:= 6*d*N^2*marginA r*4
include H h z g s P v₀ u₀ x
private lemma venueR {l u:ℕ}{b:Bool} (e:l+u ≤ r)(v:boxSeats l u M N b Q n)(O:Ruler (Core Q n) (Fin m))(uO:Oᴴ*O=1) (hZ: cutM (wal N (LodgeP d N.val (r+d))) * (Lyra v r d*O)=Lyra v r d*O) :
    Suite m X M (LodgeP d N.val (r+d)) (Opera l u N.val b) (Opera l u N.val (!b)) u ((1+ζ)*u) (artE σ ζ μ K u d) := by
 let Ψ:= TauP N X (LodgeP 0 N.val (r+d+d)); have hp:SΨ=SΨ:=rfl
 have hl:Waltz N SΨ:= Walsh g le_rfl 0; have hs:Waltz X SΨ:= Walsh (g.trans_le x) x 0; have hu:LodgeP d N.val (r+d)⊆ SΨ:= LodgeP_sub (by omega) (by omega); let h':= ferment (d:=d) h.le z.le H e v (platterA s) (by omega)
 have he : ∀ v:Cover,v∈ LodgeP d N.val (r+d)→∀ i:Cover,i∈ box d→ v-i∈ SΨ:= fun i t=> edgeK i t
 let hq:= (h'.rightM O uO).sailing (Basis:=SΨ) (bar 4 M.val) rfl hl hs (operaE (by omega)) (operaE (by omega)) v₀.le u₀ d _ P _ hZ hu he le_rfl
 exact ⟨_,_,_,hq,hull' hl hs hu hZ⟩ -- tune one ctor flattened? Suite single
include y y' p p'
lemma commissioned (a:m+2*Studio d (r+d) N.val ≤ k^3*n) :
     Suite m X M Z (Opera l u N.val false) (Opera l u N.val true) u ((1+ζ)*u) (artE σ ζ μ K u d) ∧ Suite m X M Z (Opera l' w N.val true) (Opera l' w N.val false) w ((1+ζ)*w) (artE σ ζ μ K w d):= by
 let U:= wal N Z; let S:= wal N (LodgeP 0 N.val (r+d)); have hA:Fintype.card (Core Q n)=k^3*n:=by unfold Core; rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,platterC s]; -- may `simp Q`
 have hx':(S\ U).card ≤ Studio d (r+d) N.val:= portal_loss (by omega) (by omega)
 obtain ⟨T,Z',V,W⟩:= dim_b (Lyra y r d) (Lyra y' r d) (S\ U) m (by omega)
 have he {b:Bool}{t u:ℕ}(p:boxSeats t u M N b Q n)(e: cutM (S\U)*Lyra p r d*T=0) : cutM U*(Lyra p r d*T)=Lyra p r d*T:= cutShrunk U S (Lyra p r d*T) (by rw [←Matrix.mul_assoc, wing]) (by rw [←Matrix.mul_assoc]; exact e)
 -- tune e n shadow
 exact ⟨venueR P h z v₀ u₀ H g s x p y T Z' (he y V),venueR P h z v₀ u₀ H g s x p' y' T Z' (he y' W)⟩
-- capacity fees. choose N=24*k any k large. rank = i⋅k^3 where need >= site period witness. n=2* wanted(i>0); cut pay θ. 
omit P H g h z v₀ u₀ s x y y' p p'
lemma enchant (d r i:ℕ)(t:0< i) : ∃ B:ℕ,∀ k:ℕ, B≤ k → k^3*i+2*Studio d (r+d) (24*k) ≤ k^3*(2*i) := by
 let t':= 6*d*24^2*marginA (r+d)*4
 refine ⟨2*t',fun k h=>?_⟩; unfold Studio; have hx: 2*(6*d*(24*k)^2*marginA (r+d)*4) ≤ k^3:=by
    calc
      _ = (2*t')*k^2:= by unfold t'; ring
      _ ≤ k*k^2:= Nat.mul_le_mul_right _ h
      _ = _ := by ring
 have hs:k^3*1 ≤ k^3*i:= Nat.mul_le_mul_left _ t; nlinarith only [hx,hs]
#print axioms commissioned
#print axioms enchant
end YM.CF.Window.Largo
